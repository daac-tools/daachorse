//! Iterators for [`CharwiseDoubleArrayAhoCorasick`].

use core::iter::Enumerate;
use core::num::NonZeroU32;

use alloc::vec::Vec;

use crate::charwise::CharwiseDoubleArrayAhoCorasick;

use crate::charwise::ROOT_STATE_IDX;
use crate::utils::FromU32;
use crate::Match;

/// Iterator for some struct that implements [`AsRef<str>`].
#[doc(hidden)]
pub struct StrIterator<P> {
    inner: P,
    pos: usize,
}

impl<P> StrIterator<P>
where
    P: AsRef<str>,
{
    #[allow(clippy::missing_const_for_fn)]
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

/// Iterator for UTF-8 strings with end positions.
#[doc(hidden)]
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
pub struct FindOverlappingIterator<'a, P, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) haystack: CharWithEndOffsetIterator<P>,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
    pub(crate) output_pos: Option<NonZeroU32>,
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_overlapping_iter()`].
pub struct FindIterator<'a, P, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) haystack: CharWithEndOffsetIterator<P>,
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_overlapping_no_suffix_iter()`].
pub struct FindOverlappingNoSuffixIterator<'a, P, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) haystack: CharWithEndOffsetIterator<P>,
    pub(crate) state_id: u32,
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
            self.pos = pos;

            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            self.state_id = unsafe { self.pma.next_state_id_unchecked(self.state_id, c) };
            if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(usize::from_u32(self.state_id))
                    .output_pos()
            } {
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
                    end: pos,
                    value: out.value(),
                });
            }
        }
        None
    }
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
            // self.state_id is always smaller than self.pma.states.len() because
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
                    end: pos,
                    value: out.value(),
                });
            }
        }
        None
    }
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
                    end: pos,
                    value: out.value(),
                });
            }
        }
        None
    }
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::leftmost_find_iter()`].
pub struct LeftmostFindIterator<'a, P, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) haystack: CharWithEndOffsetIterator<P>,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
    pub(crate) matches: Vec<Match<V>>,
    pub(crate) prev_pos_c: Option<(usize, char)>,
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
                    end: pos - usize::from_u32(state_depth - output_depth),
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
    fn move_and_retrieve_matches(&mut self, c: char) -> Option<Match<V>> {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_char_with_end_offset_iterator() {
        let test_string =
            "\u{0000}\u{0001}\u{0002}\u{0004}\u{0008}\u{0010}\u{001f}\u{0020}\u{0040}\
             \u{007f}\u{0080}\u{0100}\u{01ff}\u{0200}\u{0400}\u{07ff}\u{0800}\u{1000}\
             \u{1fff}\u{2000}\u{4000}\u{8000}\u{ffff}\u{10000}\
             \u{1ffff}\u{20000}\u{40000}\u{80000}\u{100000}\u{10ffff}";
        let mut it =
            unsafe { CharWithEndOffsetIterator::new(test_string.as_bytes().iter().copied()) };

        // 1 byte
        assert_eq!(Some((1, '\u{0000}')), it.next());
        assert_eq!(Some((2, '\u{0001}')), it.next());
        assert_eq!(Some((3, '\u{0002}')), it.next());
        assert_eq!(Some((4, '\u{0004}')), it.next());
        assert_eq!(Some((5, '\u{0008}')), it.next());
        assert_eq!(Some((6, '\u{0010}')), it.next());
        assert_eq!(Some((7, '\u{001f}')), it.next());
        assert_eq!(Some((8, '\u{0020}')), it.next());
        assert_eq!(Some((9, '\u{0040}')), it.next());
        assert_eq!(Some((10, '\u{007f}')), it.next());

        // 2 bytes
        assert_eq!(Some((12, '\u{0080}')), it.next());
        assert_eq!(Some((14, '\u{0100}')), it.next());
        assert_eq!(Some((16, '\u{01ff}')), it.next());
        assert_eq!(Some((18, '\u{0200}')), it.next());
        assert_eq!(Some((20, '\u{0400}')), it.next());
        assert_eq!(Some((22, '\u{07ff}')), it.next());

        // 3 bytes
        assert_eq!(Some((25, '\u{0800}')), it.next());
        assert_eq!(Some((28, '\u{1000}')), it.next());
        assert_eq!(Some((31, '\u{1fff}')), it.next());
        assert_eq!(Some((34, '\u{2000}')), it.next());
        assert_eq!(Some((37, '\u{4000}')), it.next());
        assert_eq!(Some((40, '\u{8000}')), it.next());
        assert_eq!(Some((43, '\u{ffff}')), it.next());

        // 4 bytes
        assert_eq!(Some((47, '\u{10000}')), it.next());
        assert_eq!(Some((51, '\u{1ffff}')), it.next());
        assert_eq!(Some((55, '\u{20000}')), it.next());
        assert_eq!(Some((59, '\u{40000}')), it.next());
        assert_eq!(Some((63, '\u{80000}')), it.next());
        assert_eq!(Some((67, '\u{100000}')), it.next());
        assert_eq!(Some((71, '\u{10ffff}')), it.next());

        // end of iterator
        assert_eq!(None, it.next());
        assert_eq!(None, it.next());
    }
}
