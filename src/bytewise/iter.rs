//! Iterators for [`DoubleArrayAhoCorasick`].

use core::iter::Enumerate;
use core::num::NonZeroU32;

use crate::bytewise::DoubleArrayAhoCorasick;
use crate::Match;

use crate::bytewise::ROOT_STATE_IDX;

/// Iterator for some struct that implements [`AsRef<[u8]>`].
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
pub struct FindIterator<'a, P> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick,
    pub(crate) haystack: Enumerate<P>,
}

impl<'a, P> Iterator for FindIterator<'a, P>
where
    P: Iterator<Item = u8>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let mut state_id = ROOT_STATE_IDX;
        for (pos, c) in self.haystack.by_ref() {
            // state_id is always smaller than self.pma.states.len() because
            // self.pma.get_next_state_id_unchecked() ensures to return such a value.
            state_id = unsafe { self.pma.get_next_state_id_unchecked(state_id, c) };
            if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(state_id as usize)
                    .output_pos()
            } {
                // output_pos is always smaller than self.pma.outputs.len() because
                // State::output_pos() ensures to return such a value when it is Some.
                let out = unsafe { self.pma.outputs.get_unchecked(output_pos.get() as usize) };
                return Some(Match {
                    length: out.length() as usize,
                    end: pos + 1,
                    value: out.value() as usize,
                });
            }
        }
        None
    }
}

/// Iterator created by [`DoubleArrayAhoCorasick::find_overlapping_iter()`].
pub struct FindOverlappingIterator<'a, P> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick,
    pub(crate) haystack: Enumerate<P>,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
    pub(crate) output_pos: Option<NonZeroU32>,
}

impl<'a, P> Iterator for FindOverlappingIterator<'a, P>
where
    P: Iterator<Item = u8>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(output_pos) = self.output_pos {
            // output_pos.get() is always smaller than self.pma.outputs.len() because
            // Output::parent() ensures to return such a value when it is Some.
            let out = unsafe { self.pma.outputs.get_unchecked(output_pos.get() as usize) };
            self.output_pos = out.parent();
            return Some(Match {
                length: out.length() as usize,
                end: self.pos,
                value: out.value() as usize,
            });
        }
        for (pos, c) in self.haystack.by_ref() {
            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.get_next_state_id_unchecked() ensures to return such a value.
            self.state_id = unsafe { self.pma.get_next_state_id_unchecked(self.state_id, c) };
            if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(self.state_id as usize)
                    .output_pos()
            } {
                self.pos = pos + 1;
                // output_pos.get() is always smaller than self.pma.outputs.len() because
                // State::output_pos() ensures to return such a value when it is Some.
                let out = unsafe { self.pma.outputs.get_unchecked(output_pos.get() as usize) };
                self.output_pos = out.parent();
                return Some(Match {
                    length: out.length() as usize,
                    end: self.pos,
                    value: out.value() as usize,
                });
            }
        }
        None
    }
}

/// Iterator created by [`DoubleArrayAhoCorasick::find_overlapping_no_suffix_iter()`].
pub struct FindOverlappingNoSuffixIterator<'a, P> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick,
    pub(crate) haystack: Enumerate<P>,
    pub(crate) state_id: u32,
}

impl<'a, P> Iterator for FindOverlappingNoSuffixIterator<'a, P>
where
    P: Iterator<Item = u8>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        for (pos, c) in self.haystack.by_ref() {
            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.get_next_state_id_unchecked() ensures to return such a value.
            self.state_id = unsafe { self.pma.get_next_state_id_unchecked(self.state_id, c) };
            if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(self.state_id as usize)
                    .output_pos()
            } {
                // output_pos is always smaller than self.pma.outputs.len() because
                // State::output_pos() ensures to return such a value when it is Some.
                let out = unsafe { self.pma.outputs.get_unchecked(output_pos.get() as usize) };
                return Some(Match {
                    length: out.length() as usize,
                    end: pos + 1,
                    value: out.value() as usize,
                });
            }
        }
        None
    }
}

/// Iterator created by [`DoubleArrayAhoCorasick::leftmost_find_iter()`].
pub struct LestmostFindIterator<'a, P>
where
    P: AsRef<[u8]>,
{
    pub(crate) pma: &'a DoubleArrayAhoCorasick,
    pub(crate) haystack: P,
    pub(crate) pos: usize,
}

impl<'a, P> Iterator for LestmostFindIterator<'a, P>
where
    P: AsRef<[u8]>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let mut state_id = ROOT_STATE_IDX;
        let mut last_output_pos: Option<NonZeroU32> = None;

        let haystack = self.haystack.as_ref();
        for (pos, &c) in haystack.iter().enumerate().skip(self.pos) {
            // state_id is always smaller than self.pma.states.len() because
            // self.pma.get_next_state_id_leftmost_unchecked() ensures to return such a value.
            state_id = unsafe { self.pma.get_next_state_id_leftmost_unchecked(state_id, c) };
            if state_id == ROOT_STATE_IDX {
                if let Some(output_pos) = last_output_pos {
                    // last_output_pos is always smaller than self.pma.outputs.len() because
                    // State::output_pos() ensures to return such a value when it is Some.
                    let out = unsafe { self.pma.outputs.get_unchecked(output_pos.get() as usize) };
                    return Some(Match {
                        length: out.length() as usize,
                        end: self.pos,
                        value: out.value() as usize,
                    });
                }
            // state_id is always smaller than self.pma.states.len() because
            // self.pma.get_next_state_id_leftmost_unchecked() ensures to return such a value.
            } else if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(state_id as usize)
                    .output_pos()
            } {
                last_output_pos.replace(output_pos);
                self.pos = pos + 1;
            }
        }

        last_output_pos.map(|output_pos| {
            // last_output_pos is always smaller than self.pma.outputs.len() because
            // State::output_pos() ensures to return such a value when it is Some.
            let out = unsafe { self.pma.outputs.get_unchecked(output_pos.get() as usize) };
            Match {
                length: out.length() as usize,
                end: self.pos,
                value: out.value() as usize,
            }
        })
    }
}
