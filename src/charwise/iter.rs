use std::iter::Enumerate;

use crate::charwise::CharwiseDoubleArrayAhoCorasick;
use crate::Match;
use crate::{DEAD_STATE_IDX, OUTPUT_POS_INVALID, ROOT_STATE_IDX};

/// Iterator for some struct that implements [`AsRef<str>`].
pub struct StrIterator<P> {
    inner: P,
    pos: usize,
}

impl<P> StrIterator<P>
where
    P: AsRef<str>,
{
    pub(crate) fn new(inner: P) -> Self {
        Self { inner, pos: 0 }
    }
}

impl<P> Iterator for StrIterator<P>
where
    P: AsRef<str>,
{
    type Item = u8;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let ret = *self.inner.as_ref().as_bytes().get(self.pos)?;
        self.pos += 1;
        Some(ret)
    }
}

pub struct CharWithEndOffsetIterator<I> {
    inner: Enumerate<I>,
}

impl<I> CharWithEndOffsetIterator<I>
where
    I: Iterator<Item = u8>,
{
    /// Creates a new iterator.
    ///
    /// # Safety
    ///
    /// `inner` must represent a correct UTF-8 string.
    pub unsafe fn new(inner: I) -> Self {
        Self {
            inner: inner.enumerate(),
        }
    }
}

impl<I> Iterator for CharWithEndOffsetIterator<I>
where
    I: Iterator<Item = u8>,
{
    type Item = (usize, char);

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let (i, first) = self.inner.next()?;
        let (end_offset, c) = if first < 0x80 {
            // 1 byte
            (i + 1, u32::from(first))
        } else {
            // 2 bytes ~
            let (i, rest) = unsafe { self.inner.next().unwrap_unchecked() };
            let c = u32::from(rest & 0x3f);
            if first < 0xe0 {
                (i + 1, u32::from(first & 0x1f) << 6 | c)
            } else {
                // 3 bytes ~
                let (i, rest) = unsafe { self.inner.next().unwrap_unchecked() };
                let c = c << 6 | u32::from(rest & 0x3f);
                if first < 0xf0 {
                    (i + 1, u32::from(first & 0x0f) << 12 | c)
                } else {
                    // 4 bytes
                    let (i, rest) = unsafe { self.inner.next().unwrap_unchecked() };
                    let c = c << 6 | u32::from(rest & 0x3f);
                    (i + 1, u32::from(first & 0x07) << 18 | c)
                }
            }
        };
        Some((end_offset, unsafe { char::from_u32_unchecked(c) }))
    }
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_iter()`].
pub struct FindOverlappingIterator<'a, P> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick,
    pub(crate) haystack: CharWithEndOffsetIterator<P>,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
    pub(crate) output_pos: usize,
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_overlapping_iter()`].
pub struct FindIterator<'a, P> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick,
    pub(crate) haystack: CharWithEndOffsetIterator<P>,
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_overlapping_no_suffix_iter()`].
pub struct FindOverlappingNoSuffixIterator<'a, P> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick,
    pub(crate) haystack: CharWithEndOffsetIterator<P>,
    pub(crate) state_id: u32,
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::leftmost_find_iter()`].
pub struct LestmostFindIterator<'a, P> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick,
    pub(crate) haystack: P,
    pub(crate) pos: usize,
}

impl<'a, P> Iterator for FindOverlappingIterator<'a, P>
where
    P: Iterator<Item = u8>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        // self.output_pos is always smaller than self.pma.outputs.len() because
        // State::output_pos() ensures to return such a value when it is Some.
        let out = unsafe { self.pma.outputs.get_unchecked(self.output_pos) };
        if !out.is_begin() {
            self.output_pos += 1;
            return Some(Match {
                length: out.length() as usize,
                end: self.pos,
                value: out.value() as usize,
            });
        }

        for (pos, c) in self.haystack.by_ref() {
            self.pos = pos;
            let mapped_c = c as u32;

            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.get_next_state_id_unchecked() ensures to return such a value.
            self.state_id = unsafe {
                self.pma
                    .get_next_state_id_unchecked(self.state_id, mapped_c)
            };
            if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(self.state_id as usize)
                    .output_pos()
            } {
                self.output_pos = output_pos as usize + 1;
                let out = unsafe { self.pma.outputs.get_unchecked(output_pos as usize) };
                return Some(Match {
                    length: out.length() as usize,
                    end: pos,
                    value: out.value() as usize,
                });
            }
        }
        None
    }
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
            let mapped_c = c as u32;

            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.get_next_state_id_unchecked() ensures to return such a value.
            state_id = unsafe { self.pma.get_next_state_id_unchecked(state_id, mapped_c) };
            if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(state_id as usize)
                    .output_pos()
            } {
                // output_pos is always smaller than self.pma.outputs.len() because
                // State::output_pos() ensures to return such a value when it is Some.
                let out = unsafe { self.pma.outputs.get_unchecked(output_pos as usize) };
                return Some(Match {
                    length: out.length() as usize,
                    end: pos,
                    value: out.value() as usize,
                });
            }
        }
        None
    }
}

impl<'a, P> Iterator for FindOverlappingNoSuffixIterator<'a, P>
where
    P: Iterator<Item = u8>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        for (pos, c) in self.haystack.by_ref() {
            let mapped_c = c as u32;

            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.get_next_state_id_unchecked() ensures to return such a value.
            self.state_id = unsafe {
                self.pma
                    .get_next_state_id_unchecked(self.state_id, mapped_c)
            };
            if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(self.state_id as usize)
                    .output_pos()
            } {
                // output_pos is always smaller than self.pma.outputs.len() because
                // State::output_pos() ensures to return such a value when it is Some.
                let out = unsafe { self.pma.outputs.get_unchecked(output_pos as usize) };
                return Some(Match {
                    length: out.length() as usize,
                    end: pos,
                    value: out.value() as usize,
                });
            }
        }
        None
    }
}

impl<'a, P> Iterator for LestmostFindIterator<'a, P>
where
    P: AsRef<str>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let mut state_id = ROOT_STATE_IDX;
        let mut last_output_pos = OUTPUT_POS_INVALID;

        let mut skips = 0;
        for c in unsafe { self.haystack.as_ref().get_unchecked(self.pos..) }.chars() {
            skips += c.len_utf8();
            let mapped_c = c as u32;

            // state_id is always smaller than self.pma.states.len() because
            // self.pma.get_next_state_id_leftmost_unchecked() ensures to return such a value.
            state_id = unsafe {
                self.pma
                    .get_next_state_id_leftmost_unchecked(state_id, mapped_c)
            };
            if state_id == DEAD_STATE_IDX {
                debug_assert_ne!(last_output_pos, OUTPUT_POS_INVALID);
                break;
            }

            // state_id is always smaller than self.pma.states.len() because
            // self.pma.get_next_state_id_leftmost_unchecked() ensures to return such a value.
            if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(state_id as usize)
                    .output_pos()
            } {
                last_output_pos = output_pos;
                self.pos += skips;
                skips = 0;
            }
        }

        if last_output_pos == OUTPUT_POS_INVALID {
            None
        } else {
            // last_output_pos is always smaller than self.pma.outputs.len() because
            // State::output_pos() ensures to return such a value when it is Some.
            let out = unsafe { self.pma.outputs.get_unchecked(last_output_pos as usize) };
            Some(Match {
                length: out.length() as usize,
                end: self.pos,
                value: out.value() as usize,
            })
        }
    }
}
