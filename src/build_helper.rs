use core::num::NonZeroU32;

use alloc::vec::Vec;

use crate::errors::{DaachorseError, Result};
use crate::utils::FromU32;
use crate::{DEAD_STATE_IDX, ROOT_STATE_IDX};

/// Access counts of automaton states collected by scanning documents.
pub struct Profile {
    pub visits: Vec<usize>,
    pub probes: Vec<usize>,
}

impl Profile {
    pub fn new(len: usize) -> Self {
        Self {
            visits: vec![0; len],
            probes: vec![0; len],
        }
    }
}

/// A group of sibling states sharing a single BASE value.
pub struct SiblingGroup {
    pub parent: u32,
    pub children: Vec<(u32, u32)>,
    pub weight: usize,
}

/// Helper struct in double-array construction to maintain indices of vacant elements and
/// unused BASE values.
///
/// This struct manages array elements in fixed-size blocks and supports extending the array
/// block by block. The helper starts in the exhaustive mode, where the whole array is scanned
/// so that groups are packed at the smallest vacant indices. Once [`Self::enable_window()`] is
/// called, only the vacant indices in the last `num_free_blocks` blocks are scanned; vacant
/// indices dropped from the window are left unused, which slightly increases the memory usage
/// but bounds the construction time.
pub struct BuildHelper {
    items: Vec<ListItem>,
    block_len: u32,
    num_free_blocks: u32,
    num_blocks: u32,
    head_idx: Option<u32>,
    windowed: bool,
    pub idx_map: Vec<u32>,
    pub bases: Vec<Option<NonZeroU32>>,
}

impl BuildHelper {
    /// Creates a helper holding the vacancy information of a double array and places the sibling
    /// groups in the given order, packing each group at the smallest vacant position.
    ///
    /// All edge labels must be smaller than `block_len`, which must be a power of two, so that
    /// all children of a group stay within a single aligned block. When `track_bases` is true,
    /// BASE values are additionally kept unique among groups; the byte-wise version requires
    /// this because its CHECK values are edge labels, whereas the character-wise version stores
    /// parent indices in CHECK and can safely share a BASE value among multiple states.
    ///
    /// # Panics
    ///
    /// Panics if block_len == 0 || num_free_blocks == 0.
    pub fn new(
        groups: &[SiblingGroup],
        num_nfa_states: usize,
        block_len: u32,
        num_free_blocks: u32,
        track_bases: bool,
    ) -> Result<Self> {
        let capacity = block_len.checked_mul(num_free_blocks).ok_or_else(|| {
            DaachorseError::automaton_scale("block_len * num_free_blocks", u32::MAX)
        })?;
        assert_ne!(capacity, 0);

        let mut helper = Self {
            items: Vec::with_capacity(usize::from_u32(capacity)),
            block_len,
            num_free_blocks,
            num_blocks: 0,
            head_idx: None,
            windowed: false,
            idx_map: vec![DEAD_STATE_IDX; num_nfa_states],
            bases: vec![None; num_nfa_states],
        };
        helper.push_block()?;
        helper.use_index(ROOT_STATE_IDX);
        helper.use_index(DEAD_STATE_IDX);
        helper.idx_map[usize::from_u32(ROOT_STATE_IDX)] = ROOT_STATE_IDX;
        helper.idx_map[usize::from_u32(DEAD_STATE_IDX)] = DEAD_STATE_IDX;
        let mut labels = vec![];
        for group in groups {
            if group.weight == 0 && !helper.windowed {
                helper.enable_window();
            }
            labels.clear();
            labels.extend(group.children.iter().map(|&(c, _)| c));
            let base = helper.find_base(&labels)?;
            if track_bases {
                helper.use_base(base);
            }
            for &(c, child_id) in &group.children {
                let child_idx = base.get() ^ c;
                helper.use_index(child_idx);
                helper.idx_map[usize::from_u32(child_id)] = child_idx;
            }
            helper.bases[usize::from_u32(group.parent)] = Some(base);
        }
        Ok(helper)
    }

    /// Gets the number of current double-array elements.
    #[inline(always)]
    pub const fn num_elements(&self) -> u32 {
        self.num_blocks * self.block_len
    }

    /// Creates an iterator to visit vacant indices in the active blocks.
    #[inline(always)]
    pub const fn vacant_iter(&self) -> VacantIter<'_> {
        VacantIter {
            list: self,
            idx: self.head_idx,
        }
    }

    /// Gets an unused BASE value in the block.
    #[inline(always)]
    pub fn unused_base_in_block(&self, block_idx: u32) -> Option<u32> {
        let start = block_idx * self.block_len;
        let end = start + self.block_len;
        (start..end).find(|&base| !self.is_used_base(base))
    }

    /// Checks if the BASE value is used.
    #[inline(always)]
    pub fn is_used_base(&self, base: u32) -> bool {
        self.get_ref(base).is_used_base()
    }

    /// Checks if the index is used.
    #[inline(always)]
    pub fn is_used_index(&self, idx: u32) -> bool {
        self.get_ref(idx).is_used_index()
    }

    /// Uses the BASE value.
    #[inline(always)]
    fn use_base(&mut self, base: NonZeroU32) {
        self.get_mut(base.get()).use_base();
    }

    /// Uses the index.
    #[inline(always)]
    fn use_index(&mut self, idx: u32) {
        debug_assert!(!self.get_ref(idx).is_used_index());
        self.get_mut(idx).use_index();
        self.unlink(idx);
    }

    /// Removes the index from the vacant list without marking it used, so that it is no longer
    /// scanned but is still treated as vacant by `is_used_index()`.
    fn unlink(&mut self, idx: u32) {
        let next = self.get_ref(idx).next();
        let prev = self.get_ref(idx).prev();
        *self.get_mut(prev).next_mut() = next;
        *self.get_mut(next).prev_mut() = prev;
        if self.head_idx.unwrap() == idx {
            self.head_idx = Some(next).filter(|&x| x != idx);
        }
    }

    /// Extends the array by pushing a block back.
    fn push_block(&mut self) -> Result<()> {
        if self.num_elements() > u32::MAX - self.block_len {
            return Err(DaachorseError::automaton_scale("num_elements", u32::MAX));
        }

        let old_len = self.num_elements();
        let new_len = old_len + self.block_len;

        // Update the active index range.
        self.num_blocks += 1;
        self.items
            .resize(usize::from_u32(new_len), ListItem::default());

        for idx in old_len..new_len {
            *self.get_mut(idx).next_mut() = idx + 1;
            *self.get_mut(idx).prev_mut() = idx.wrapping_sub(1);
        }

        if let Some(head_idx) = self.head_idx {
            let tail_idx = self.get_ref(head_idx).prev();
            *self.get_mut(old_len).prev_mut() = tail_idx;
            *self.get_mut(tail_idx).next_mut() = old_len;
            *self.get_mut(new_len - 1).next_mut() = head_idx;
            *self.get_mut(head_idx).prev_mut() = new_len - 1;
        } else {
            *self.get_mut(old_len).prev_mut() = new_len - 1;
            *self.get_mut(new_len - 1).next_mut() = old_len;
            self.head_idx = Some(old_len);
        }

        if self.windowed {
            self.prune();
        }
        Ok(())
    }

    /// Switches to the windowed mode, where only the vacant indices in the last
    /// `num_free_blocks` blocks are scanned.
    fn enable_window(&mut self) {
        self.windowed = true;
        self.prune();
    }

    /// Drops the vacant indices that have fallen out of the window from the list. Since the
    /// list is kept in ascending order of indices, it suffices to unlink from the head.
    fn prune(&mut self) {
        let boundary = self.num_blocks.saturating_sub(self.num_free_blocks) * self.block_len;
        while let Some(head_idx) = self.head_idx {
            if head_idx >= boundary {
                break;
            }
            self.unlink(head_idx);
        }
    }

    /// Finds the smallest vacant placement for the given labels, extending the array if needed.
    ///
    /// The scan visits the vacant indices in ascending order, so the placement is the densest
    /// first-fit over the exhaustive or windowed scan range.
    fn find_base(&mut self, labels: &[u32]) -> Result<NonZeroU32> {
        loop {
            for idx in self.vacant_iter() {
                let base = idx ^ labels[0];
                if base != 0
                    && !self.is_used_base(base)
                    && labels.iter().all(|&c| !self.is_used_index(base ^ c))
                {
                    return Ok(NonZeroU32::new(base).unwrap());
                }
            }
            self.push_block()?;
        }
    }

    #[inline(always)]
    fn get_ref(&self, idx: u32) -> &ListItem {
        &self.items[usize::from_u32(idx)]
    }

    #[inline(always)]
    fn get_mut(&mut self, idx: u32) -> &mut ListItem {
        &mut self.items[usize::from_u32(idx)]
    }
}

pub struct VacantIter<'a> {
    list: &'a BuildHelper,
    idx: Option<u32>,
}

impl Iterator for VacantIter<'_> {
    type Item = u32;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let curr = self.idx?;
        let next = self.list.get_ref(curr).next();
        // self.list.head_idx is always Some because, whenever self.list.head_idx is None,
        // self.idx? of the first line will break this function.
        self.idx = Some(next).filter(|&x| x != self.list.head_idx.unwrap());
        Some(curr)
    }
}

// TODO: Make memory-efficient.
#[derive(Default, Clone)]
pub struct ListItem {
    next: u32,
    prev: u32,
    used_base: bool,
    used_index: bool,
}

impl ListItem {
    #[inline(always)]
    pub const fn next(&self) -> u32 {
        self.next
    }

    #[inline(always)]
    pub const fn prev(&self) -> u32 {
        self.prev
    }

    #[inline(always)]
    pub fn next_mut(&mut self) -> &mut u32 {
        &mut self.next
    }

    #[inline(always)]
    pub fn prev_mut(&mut self) -> &mut u32 {
        &mut self.prev
    }

    #[inline(always)]
    pub const fn is_used_base(&self) -> bool {
        self.used_base
    }

    #[inline(always)]
    pub const fn is_used_index(&self) -> bool {
        self.used_index
    }

    #[inline(always)]
    pub fn use_base(&mut self) {
        self.used_base = true;
    }

    #[inline(always)]
    pub fn use_index(&mut self) {
        self.used_index = true;
    }
}
