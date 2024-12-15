//! Iterators for [`DoubleArrayAhoCorasick`].

use core::iter::Enumerate;
use core::num::NonZeroU32;

use alloc::vec::Vec;

use crate::bytewise::DoubleArrayAhoCorasick;
use crate::Match;

use crate::bytewise::ROOT_STATE_IDX;
use crate::utils::FromU32;

/// Iterator for some struct that implements [`AsRef<[u8]>`].
#[doc(hidden)]
pub struct U8SliceIterator<P> {
    inner: P,
    pos: usize,
}

impl<P> U8SliceIterator<P>
where
    P: AsRef<[u8]>,
{
    #[allow(clippy::missing_const_for_fn)]
    pub(crate) fn new(inner: P) -> Self {
        Self { inner, pos: 0 }
    }
}

impl<P> Iterator for U8SliceIterator<P>
where
    P: AsRef<[u8]>,
{
    type Item = u8;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let ret = *self.inner.as_ref().get(self.pos)?;
        self.pos += 1;
        Some(ret)
    }
}

/// Iterator created by [`DoubleArrayAhoCorasick::find_iter()`].
pub struct FindIterator<'a, P, V> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
    pub(crate) haystack: Enumerate<P>,
}

impl<P, V> Iterator for FindIterator<'_, P, V>
where
    P: Iterator<Item = u8>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let mut state_id = ROOT_STATE_IDX;
        for (pos, c) in self.haystack.by_ref() {
            // state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            state_id = unsafe { self.pma.next_state_id_unchecked(state_id, c) };
            if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(usize::from_u32(state_id))
                    .output_pos()
            } {
                // output_pos is always smaller than self.pma.outputs.len() because
                // State::output_pos() ensures to return such a value when it is Some.
                let out = unsafe {
                    self.pma
                        .outputs
                        .get_unchecked(usize::from_u32(output_pos.get() - 1))
                };
                return Some(Match {
                    length: usize::from_u32(out.length()),
                    end: pos + 1,
                    value: out.value(),
                });
            }
        }
        None
    }
}

/// Iterator created by [`DoubleArrayAhoCorasick::find_overlapping_iter()`].
pub struct FindOverlappingIterator<'a, P, V> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
    pub(crate) haystack: Enumerate<P>,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
    pub(crate) output_pos: Option<NonZeroU32>,
}

impl<P, V> Iterator for FindOverlappingIterator<'_, P, V>
where
    P: Iterator<Item = u8>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(output_pos) = self.output_pos {
            // output_pos.get() is always smaller than self.pma.outputs.len() because
            // Output::parent() ensures to return such a value when it is Some.
            let out = unsafe {
                self.pma
                    .outputs
                    .get_unchecked(usize::from_u32(output_pos.get() - 1))
            };
            self.output_pos = out.parent();
            return Some(Match {
                length: usize::from_u32(out.length()),
                end: self.pos,
                value: out.value(),
            });
        }
        for (pos, c) in self.haystack.by_ref() {
            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            self.state_id = unsafe { self.pma.next_state_id_unchecked(self.state_id, c) };
            if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(usize::from_u32(self.state_id))
                    .output_pos()
            } {
                self.pos = pos + 1;
                // output_pos.get() is always smaller than self.pma.outputs.len() because
                // State::output_pos() ensures to return such a value when it is Some.
                let out = unsafe {
                    self.pma
                        .outputs
                        .get_unchecked(usize::from_u32(output_pos.get() - 1))
                };
                self.output_pos = out.parent();
                return Some(Match {
                    length: usize::from_u32(out.length()),
                    end: self.pos,
                    value: out.value(),
                });
            }
        }
        None
    }
}

/// Iterator created by [`DoubleArrayAhoCorasick::find_overlapping_no_suffix_iter()`].
pub struct FindOverlappingNoSuffixIterator<'a, P, V> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
    pub(crate) haystack: Enumerate<P>,
    pub(crate) state_id: u32,
}

impl<P, V> Iterator for FindOverlappingNoSuffixIterator<'_, P, V>
where
    P: Iterator<Item = u8>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        for (pos, c) in self.haystack.by_ref() {
            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            self.state_id = unsafe { self.pma.next_state_id_unchecked(self.state_id, c) };
            if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(usize::from_u32(self.state_id))
                    .output_pos()
            } {
                // output_pos is always smaller than self.pma.outputs.len() because
                // State::output_pos() ensures to return such a value when it is Some.
                let out = unsafe {
                    self.pma
                        .outputs
                        .get_unchecked(usize::from_u32(output_pos.get() - 1))
                };
                return Some(Match {
                    length: usize::from_u32(out.length()),
                    end: pos + 1,
                    value: out.value(),
                });
            }
        }
        None
    }
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::leftmost_find_iter()`].
pub struct LeftmostFindIterator<'a, P, V> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
    pub(crate) haystack: Enumerate<P>,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
    pub(crate) matches: Vec<Match<V>>,
    pub(crate) prev_pos_c: Option<(usize, u8)>,
}

impl<'a, P, V> LeftmostFindIterator<'a, P, V>
where
    V: Copy,
{
    #[inline(always)]
    unsafe fn retrieve_matches(&mut self, pos: usize) {
        if let Some(mut output_pos) = self
            .pma
            .states
            .get_unchecked(usize::from_u32(self.state_id))
            .output_pos()
        {
            let state_depth = self
                .pma
                .state_depths
                .get_unchecked(usize::from_u32(self.state_id));
            loop {
                let out = self
                    .pma
                    .outputs
                    .get_unchecked(usize::from_u32(output_pos.get() - 1));
                let output_depth = self
                    .pma
                    .output_depths
                    .get_unchecked(usize::from_u32(output_pos.get() - 1));
                self.matches.push(Match {
                    length: usize::from_u32(out.length()),
                    end: pos + 1 - usize::from_u32(state_depth - output_depth),
                    value: out.value(),
                });
                let Some(parent_pos) = out.parent() else {
                    return;
                };
                output_pos = parent_pos;
            }
        }
    }

    #[inline(always)]
    fn move_and_retrieve_matches(&mut self, c: u8) -> Option<Match<V>> {
        loop {
            let (next_state_id, fail) =
                unsafe { self.pma.next_state_id_leftmost_unchecked(self.state_id, c) };
            if !fail {
                self.state_id = next_state_id;
                return None;
            }
            unsafe { self.retrieve_matches(self.pos) };
            self.state_id = next_state_id;
            if let Some(m) = self.matches.pop() {
                return Some(m);
            }
        }
    }
}

impl<P, V> Iterator for LeftmostFindIterator<'_, P, V>
where
    P: Iterator<Item = u8>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(m) = self.matches.pop() {
            return Some(m);
        }
        if let Some((pos, c)) = self.prev_pos_c {
            if let Some(m) = self.move_and_retrieve_matches(c) {
                return Some(m);
            }
            self.pos = pos;
            self.prev_pos_c = None;
        }
        while let Some((pos, c)) = self.haystack.next() {
            dbg!(c);
            if let Some(m) = self.move_and_retrieve_matches(c) {
                self.prev_pos_c = Some((pos, c));
                return Some(m);
            }
            self.pos = pos;
        }
        while self.state_id != ROOT_STATE_IDX {
            unsafe { self.retrieve_matches(self.pos) };
            self.state_id = unsafe {
                self.pma
                    .states
                    .get_unchecked(usize::from_u32(self.state_id))
                    .fail
            };
            if let Some(m) = self.matches.pop() {
                return Some(m);
            }
        }
        None
    }
}
