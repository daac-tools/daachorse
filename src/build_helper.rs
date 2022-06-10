use core::ops::Range;

use alloc::vec::Vec;

const INVALID_IDX: u32 = u32::MAX;

/// Helper class in double-array construction to maintain indices of vacant elements and
/// unused BASE values.
///
/// This class manages array elements in fixed-size blocks and supports to extend the array
/// block by block. Given a constant parameter N, this class maintains information for only
/// the last N blocks and drops the others according to array extension. We call such last
/// blocks *active blocks*.
#[derive(Default)]
pub struct BuildHelper {
    items: Vec<ListItem>,
    block_len: u32,
    num_elements: u32,
    head_idx: u32,
}

impl BuildHelper {
    /// Creates a helper class that handles the last `block_len * num_free_blocks` elements.
    pub fn new(block_len: u32, num_free_blocks: u32) -> Self {
        let capacity = usize::try_from(block_len * num_free_blocks).unwrap();
        assert_ne!(capacity, 0);

        Self {
            items: vec![ListItem::default(); capacity],
            block_len,
            num_elements: 0,
            head_idx: INVALID_IDX,
        }
    }

    /// Gets the number of current double-array elements.
    #[inline(always)]
    pub fn num_elements(&self) -> u32 {
        self.num_elements
    }

    /// Checks if the next `push_block` can drop information of a block.
    #[inline(always)]
    pub fn is_full(&self) -> bool {
        self.capacity() <= self.num_elements()
    }

    /// Gets the element index range in the active blocks.
    #[inline(always)]
    pub fn active_index_range(&self) -> Range<u32> {
        let start = self.capacity().max(self.num_elements()) - self.capacity();
        start..self.num_elements()
    }

    /// Gets the block position range in the active blocks.
    #[inline(always)]
    pub fn active_block_range(&self) -> Range<u32> {
        let r = self.active_index_range();
        r.start / self.block_len..r.end / self.block_len
    }

    /// Creates an iterator to visit vacant indices in the active blocks.
    #[inline(always)]
    pub fn vacant_iter(&self) -> VacantIter {
        let idx = Some(self.head_idx).filter(|&x| x != INVALID_IDX);
        VacantIter { list: self, idx }
    }

    /// Gets an unused BASE value in the block.
    #[inline(always)]
    pub fn unused_base_in_block(&self, block_idx: u32) -> Option<u32> {
        let start = block_idx * self.block_len;
        let end = start + self.block_len;
        for base in start..end {
            if !self.is_used_base(base) {
                return Some(base);
            }
        }
        None
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
    pub fn use_base(&mut self, base: u32) {
        self.get_mut(base).use_base()
    }

    /// Uses the index.
    #[inline(always)]
    pub fn use_index(&mut self, idx: u32) {
        debug_assert!(!self.get_ref(idx).is_used_index());
        self.get_mut(idx).use_index();

        let next = self.get_mut(idx).get_next();
        let prev = self.get_mut(idx).get_prev();
        self.get_mut(prev).set_next(next);
        self.get_mut(next).set_prev(prev);

        if self.head_idx == idx {
            if next == idx {
                self.head_idx = INVALID_IDX;
            } else {
                self.head_idx = next;
            }
        }
    }

    /// Extends the array by pushing a block back.
    pub fn push_block(&mut self) {
        if self.is_full() {
            let closed_block = self.active_block_range().start;
            let end_idx = (closed_block + 1) * self.block_len;
            while self.head_idx < end_idx && self.head_idx != INVALID_IDX {
                self.use_index(self.head_idx);
            }
        }

        let old_len = self.num_elements;
        let new_len = old_len + self.block_len;

        // Update the active index range.
        self.num_elements = new_len;

        for idx in old_len..new_len {
            self.reset(idx);
            self.get_mut(idx).set_next(idx + 1);
            self.get_mut(idx).set_prev(idx.wrapping_sub(1));
        }

        if self.head_idx == INVALID_IDX {
            self.get_mut(old_len).set_prev(new_len - 1);
            self.get_mut(new_len - 1).set_next(old_len);
            self.head_idx = old_len;
        } else {
            let head_idx = self.head_idx;
            let tail_idx = self.get_ref(head_idx).get_prev();
            self.get_mut(old_len).set_prev(tail_idx);
            self.get_mut(tail_idx).set_next(old_len);
            self.get_mut(new_len - 1).set_next(head_idx);
            self.get_mut(head_idx).set_prev(new_len - 1);
        }
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
        debug_assert!(self.active_index_range().contains(&idx));
        usize::try_from(idx % self.capacity()).unwrap()
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
        self.idx = Some(next).filter(|&x| x != self.list.head_idx);
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
