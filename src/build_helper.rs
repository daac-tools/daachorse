use core::num::NonZeroU32;
use core::ops::Range;

use alloc::vec::Vec;

use crate::errors::{DaachorseError, Result};
use crate::utils::FromU32;

/// Helper class in double-array construction to maintain indices of vacant elements and
/// unused BASE values.
///
/// This class manages array elements in fixed-size blocks and supports to extend the array
/// block by block. Given a constant parameter N, this class maintains information for only
/// the last N blocks and drops the others according to array extension. Such last blocks are
/// called *active blocks*.
pub struct BuildHelper {
    items: Vec<ListItem>,
    block_len: u32,
    num_free_blocks: u32,
    num_blocks: u32,
    head_idx: Option<u32>,
}

impl BuildHelper {
    /// Creates a helper class that handles the last `block_len * num_free_blocks` elements.
    ///
    /// # Panics
    ///
    /// Panics will arise if block_len == 0 || num_free_blocks == 0.
    pub fn new(block_len: u32, num_free_blocks: u32) -> Result<Self> {
        let capacity = block_len.checked_mul(num_free_blocks).ok_or_else(|| {
            DaachorseError::automaton_scale("block_len * num_free_blocks", u32::MAX)
        })?;
        let capacity = usize::from_u32(capacity);
        assert_ne!(capacity, 0);

        Ok(Self {
            items: vec![ListItem::default(); capacity],
            block_len,
            num_free_blocks,
            num_blocks: 0,
            head_idx: None,
        })
    }

    /// Gets the number of current double-array elements.
    #[inline(always)]
    pub const fn num_elements(&self) -> u32 {
        self.num_blocks * self.block_len
    }

    /// Gets the index range of elements in the active blocks.
    #[inline(always)]
    pub const fn active_index_range(&self) -> Range<u32> {
        let r = self.active_block_range();
        r.start * self.block_len..r.end * self.block_len
    }

    /// Gets the block index range in the active blocks.
    #[inline(always)]
    pub const fn active_block_range(&self) -> Range<u32> {
        self.num_blocks.saturating_sub(self.num_free_blocks)..self.num_blocks
    }

    /// Creates an iterator to visit vacant indices in the active blocks.
    #[inline(always)]
    pub const fn vacant_iter(&self) -> VacantIter {
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
    ///
    /// # Panic
    ///
    /// Panic will arise if active_index_range().contains(&base) == false.
    #[inline(always)]
    pub fn is_used_base(&self, base: u32) -> bool {
        self.get_ref(base).is_used_base()
    }

    /// Checks if the index is used.
    ///
    /// # Panic
    ///
    /// Panic will arise if active_index_range().contains(&idx) == false.
    #[inline(always)]
    pub fn is_used_index(&self, idx: u32) -> bool {
        self.get_ref(idx).is_used_index()
    }

    /// Uses the BASE value.
    ///
    /// # Panic
    ///
    /// Panic will arise if active_index_range().contains(&base) == false.
    #[inline(always)]
    pub fn use_base(&mut self, base: NonZeroU32) {
        self.get_mut(base.get()).use_base();
    }

    /// Uses the index.
    ///
    /// # Panic
    ///
    /// Panic will arise if active_index_range().contains(&idx) == false.
    #[inline(always)]
    pub fn use_index(&mut self, idx: u32) {
        debug_assert!(!self.get_ref(idx).is_used_index());
        self.get_mut(idx).use_index();

        let next = self.get_mut(idx).get_next();
        let prev = self.get_mut(idx).get_prev();
        self.get_mut(prev).set_next(next);
        self.get_mut(next).set_prev(prev);

        if self.head_idx.unwrap() == idx {
            self.head_idx = Some(next).filter(|&x| x != idx);
        }
    }

    /// Extends the array by pushing a block back.
    pub fn push_block(&mut self) -> Result<()> {
        if self.num_elements() > u32::MAX - self.block_len {
            return Err(DaachorseError::automaton_scale("num_elements", u32::MAX));
        }

        if let Some(closed_block) = self.dropped_block() {
            let end_idx = (closed_block + 1) * self.block_len;
            while let Some(head_idx) = self.head_idx {
                if end_idx <= head_idx {
                    break;
                }
                self.use_index(head_idx);
            }
        }

        let old_len = self.num_elements();
        let new_len = old_len + self.block_len;

        // Update the active index range.
        self.num_blocks += 1;

        for idx in old_len..new_len {
            self.reset(idx);
            self.get_mut(idx).set_next(idx + 1);
            self.get_mut(idx).set_prev(idx.wrapping_sub(1));
        }

        if let Some(head_idx) = self.head_idx {
            let tail_idx = self.get_ref(head_idx).get_prev();
            self.get_mut(old_len).set_prev(tail_idx);
            self.get_mut(tail_idx).set_next(old_len);
            self.get_mut(new_len - 1).set_next(head_idx);
            self.get_mut(head_idx).set_prev(new_len - 1);
        } else {
            self.get_mut(old_len).set_prev(new_len - 1);
            self.get_mut(new_len - 1).set_next(old_len);
            self.head_idx = Some(old_len);
        }

        Ok(())
    }

    /// Retruns the index of an active block that will be dropped in the next `push_block`.
    #[inline(always)]
    pub fn dropped_block(&self) -> Option<u32> {
        (self.capacity() <= self.num_elements()).then(|| self.active_block_range().start)
    }

    #[inline(always)]
    fn capacity(&self) -> u32 {
        u32::try_from(self.items.len()).unwrap()
    }

    #[inline(always)]
    fn reset(&mut self, idx: u32) {
        let offset = self.offset(idx);
        self.items[offset] = ListItem::default();
    }

    #[inline(always)]
    fn get_ref(&self, idx: u32) -> &ListItem {
        &self.items[self.offset(idx)]
    }

    #[inline(always)]
    fn get_mut(&mut self, idx: u32) -> &mut ListItem {
        let offset = self.offset(idx);
        &mut self.items[offset]
    }

    #[inline(always)]
    fn offset(&self, idx: u32) -> usize {
        assert!(self.active_index_range().contains(&idx));
        usize::from_u32(idx % self.capacity())
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
        let next = self.list.get_ref(curr).get_next();
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
    pub const fn get_next(&self) -> u32 {
        self.next
    }

    #[inline(always)]
    pub const fn get_prev(&self) -> u32 {
        self.prev
    }

    #[inline(always)]
    pub fn set_next(&mut self, x: u32) {
        self.next = x;
    }

    #[inline(always)]
    pub fn set_prev(&mut self, x: u32) {
        self.prev = x;
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
