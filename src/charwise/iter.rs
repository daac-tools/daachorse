//! Iterators for [`CharwiseDoubleArrayAhoCorasick`].

use core::borrow::BorrowMut;
use core::iter::Enumerate;
use core::num::NonZeroU32;

use alloc::string::String;
use alloc::vec::Vec;

use crate::charwise::{CharwiseDoubleArrayAhoCorasick, State};
use crate::prefilter::{Prefilter, PrefilterGate};
use crate::utils::FromU32;
use crate::{Match, ROOT_STATE_IDX};

/// Returns the length of the UTF-8 character starting with `b`, or `None` if `b` is an invalid
/// or continuation leading byte.
#[inline(always)]
const fn utf8_char_len_from_first_byte(b: u8) -> Option<usize> {
    match b {
        0x00..=0x7F => Some(1),
        0xC2..=0xDF => Some(2),
        0xE0..=0xEF => Some(3),
        0xF0..=0xF4 => Some(4),
        _ => None,
    }
}

/// Decodes the character starting at byte position `pos`.
///
/// # Safety
///
/// `bytes` must represent a valid UTF-8 string, and `pos` must be a character boundary with
/// `pos < bytes.len()`.
#[inline(always)]
unsafe fn decode_char_unchecked(bytes: &[u8], pos: usize) -> (char, usize) {
    let first = *bytes.get_unchecked(pos);
    let (c, len) = if first < 0x80 {
        // 1 byte
        (u32::from(first), 1)
    } else {
        // 2 bytes ~
        let c = u32::from(*bytes.get_unchecked(pos + 1) & 0x3f);
        if first < 0xe0 {
            ((u32::from(first & 0x1f) << 6) | c, 2)
        } else {
            // 3 bytes ~
            let c = (c << 6) | u32::from(*bytes.get_unchecked(pos + 2) & 0x3f);
            if first < 0xf0 {
                ((u32::from(first & 0x0f) << 12) | c, 3)
            } else {
                // 4 bytes
                let c = (c << 6) | u32::from(*bytes.get_unchecked(pos + 3) & 0x3f);
                ((u32::from(first & 0x07) << 18) | c, 4)
            }
        }
    };
    (char::from_u32_unchecked(c), len)
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
    /// `inner` must represent a valid UTF-8 string.
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
                (i + 1, (u32::from(first & 0x1f) << 6) | c)
            } else {
                // 3 bytes ~
                let (i, rest) = unsafe { self.inner.next().unwrap_unchecked() };
                let c = (c << 6) | u32::from(rest & 0x3f);
                if first < 0xf0 {
                    (i + 1, (u32::from(first & 0x0f) << 12) | c)
                } else {
                    // 4 bytes
                    let (i, rest) = unsafe { self.inner.next().unwrap_unchecked() };
                    let c = (c << 6) | u32::from(rest & 0x3f);
                    (i + 1, (u32::from(first & 0x07) << 18) | c)
                }
            }
        };
        Some((end_offset, unsafe { char::from_u32_unchecked(c) }))
    }
}

/// Runs the automaton over `haystack` and returns the output position of the next match, or
/// `None` when the end of the haystack is reached. While `*prefilter` is `Some`, whenever the
/// automaton is in the root state, scanning skips ahead to the next candidate position: no
/// pattern occurrence starts before it, so the characters in between cannot affect the
/// results. Each skip length is recorded into `gate`; once the gate closes because the skips
/// turned out too short to pay off, `*prefilter` is cleared (disabling it for the callers'
/// later calls as well) and scanning falls through to the plain loop.
#[inline(always)]
fn scan<V>(
    pma: &CharwiseDoubleArrayAhoCorasick<V>,
    prefilter: &mut Option<&Prefilter>,
    gate: &mut PrefilterGate,
    haystack: &str,
    state_id: &mut u32,
    pos: &mut usize,
) -> Option<NonZeroU32> {
    let bytes = haystack.as_bytes();
    if let Some(pf) = *prefilter {
        loop {
            if *state_id == ROOT_STATE_IDX {
                let candidate_pos = pf.next_position_at_char_boundary(haystack, *pos);
                gate.record(candidate_pos - *pos);
                *pos = candidate_pos;
                if !gate.is_enabled() {
                    // The prefilter does not pay off on this haystack; drop it and continue
                    // with the plain loop below.
                    *prefilter = None;
                    break;
                }
            }
            if *pos >= bytes.len() {
                return None;
            }
            // pos is always on a character boundary: it advances by whole characters, and the
            // prefilter only reports positions at character boundaries.
            let (c, char_len) = unsafe { decode_char_unchecked(bytes, *pos) };
            // state_id is always smaller than pma.states.len() because
            // pma.next_state_id_unchecked() ensures to return such a value.
            *state_id = unsafe { pma.next_state_id_unchecked(*state_id, c) };
            *pos += char_len;
            if let Some(output_pos) = unsafe { pma.output_pos_unchecked(*state_id) } {
                return Some(output_pos);
            }
        }
    }
    loop {
        if *pos >= bytes.len() {
            return None;
        }
        // pos is always on a character boundary: it advances by whole characters, and the
        // prefilter only reports positions at character boundaries.
        let (c, char_len) = unsafe { decode_char_unchecked(bytes, *pos) };
        // state_id is always smaller than pma.states.len() because
        // pma.next_state_id_unchecked() ensures to return such a value.
        *state_id = unsafe { pma.next_state_id_unchecked(*state_id, c) };
        *pos += char_len;
        if let Some(output_pos) = unsafe { pma.output_pos_unchecked(*state_id) } {
            return Some(output_pos);
        }
    }
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_iter_from_iter()`].
pub struct FindIterator<'a, P, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) haystack: CharWithEndOffsetIterator<P>,
    pub(crate) first_call: bool,
}

impl<P, V> Iterator for FindIterator<'_, P, V>
where
    P: Iterator<Item = u8>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(value) = self.pma.root_output_value() {
            return if self.first_call {
                self.first_call = false;
                Some(Match {
                    length: 0,
                    end: 0,
                    value,
                })
            } else {
                self.haystack.next().map(|(pos, _)| Match {
                    length: 0,
                    end: pos,
                    value,
                })
            };
        }
        let mut state_id = ROOT_STATE_IDX;
        for (pos, c) in self.haystack.by_ref() {
            // state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            state_id = unsafe { self.pma.next_state_id_unchecked(state_id, c) };
            if let Some(output_pos) = unsafe { self.pma.output_pos_unchecked(state_id) } {
                let out = unsafe { self.pma.output_at(output_pos) };
                return Some(out.to_match(pos));
            }
        }
        None
    }
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_iter()`].
pub struct FindSliceIterator<'a, P, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) haystack: P,
    pub(crate) pos: usize,
    pub(crate) first_call: bool,
    // The prefilter of `pma`, or None after the gate has closed.
    pub(crate) prefilter: Option<&'a Prefilter>,
    pub(crate) gate: PrefilterGate,
}

impl<P, V> Iterator for FindSliceIterator<'_, P, V>
where
    P: AsRef<str>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let haystack = self.haystack.as_ref();
        let bytes = haystack.as_bytes();
        // When the pattern set contains the empty string, it matches at every character
        // boundary and this block handles all calls; the scanning loop below never runs. No
        // prefilter is built for such a pattern set.
        if let Some(value) = self.pma.root_output_value() {
            if self.first_call {
                self.first_call = false;
                return Some(Match {
                    length: 0,
                    end: 0,
                    value,
                });
            }
            if self.pos < bytes.len() {
                let (_, char_len) = unsafe { decode_char_unchecked(bytes, self.pos) };
                self.pos += char_len;
                return Some(Match {
                    length: 0,
                    end: self.pos,
                    value,
                });
            }
            return None;
        }

        let mut state_id = ROOT_STATE_IDX;
        let mut pos = self.pos;
        // A single transition, unrolled ahead of the prefilter dispatch in scan(): pattern
        // sets that match at almost every position return here on most calls, paying no
        // prefilter cost (routing even this single step through scan() measurably slows them
        // down). This is harmless to the prefilter, which can skip ahead only from the root
        // state.
        {
            // No field has changed yet, so nothing needs to be written back on this exit.
            if pos >= bytes.len() {
                return None;
            }
            // pos is always on a character boundary: it advances by whole characters, and the
            // prefilter only reports positions at character boundaries.
            let (c, char_len) = unsafe { decode_char_unchecked(bytes, pos) };
            // state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            state_id = unsafe { self.pma.next_state_id_unchecked(state_id, c) };
            pos += char_len;
            if let Some(output_pos) = unsafe { self.pma.output_pos_unchecked(state_id) } {
                self.pos = pos;
                let out = unsafe { self.pma.output_at(output_pos) };
                return Some(out.to_match(pos));
            }
        }
        let output_pos = scan(
            self.pma,
            &mut self.prefilter,
            &mut self.gate,
            haystack,
            &mut state_id,
            &mut pos,
        );
        self.pos = pos;
        let out = unsafe { self.pma.output_at(output_pos?) };
        Some(out.to_match(pos))
    }
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_overlapping_iter_from_iter()`].
pub struct FindOverlappingIterator<'a, P, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) haystack: CharWithEndOffsetIterator<P>,
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
            let out = unsafe { self.pma.output_at(output_pos) };
            self.output_pos = out.parent();
            return Some(out.to_match(self.pos));
        }

        for (pos, c) in self.haystack.by_ref() {
            self.pos = pos;

            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            self.state_id = unsafe { self.pma.next_state_id_unchecked(self.state_id, c) };
            if let Some(output_pos) = unsafe { self.pma.output_pos_unchecked(self.state_id) } {
                let out = unsafe { self.pma.output_at(output_pos) };
                self.output_pos = out.parent();
                return Some(out.to_match(pos));
            }
        }
        None
    }
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_overlapping_iter()`].
pub struct FindOverlappingSliceIterator<'a, P, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) haystack: P,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
    pub(crate) output_pos: Option<NonZeroU32>,
    // The prefilter of `pma`, or None after the gate has closed.
    pub(crate) prefilter: Option<&'a Prefilter>,
    pub(crate) gate: PrefilterGate,
}

impl<P, V> Iterator for FindOverlappingSliceIterator<'_, P, V>
where
    P: AsRef<str>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        // Report the remaining matches ending at the current position (suffix patterns of the
        // previously reported match) before consuming further input.
        if let Some(output_pos) = self.output_pos {
            let out = unsafe { self.pma.output_at(output_pos) };
            self.output_pos = out.parent();
            return Some(out.to_match(self.pos));
        }
        let haystack = self.haystack.as_ref();
        let bytes = haystack.as_bytes();
        let mut state_id = self.state_id;
        let mut pos = self.pos;
        // A single transition, unrolled ahead of the prefilter dispatch in scan(): pattern
        // sets that match at almost every position return here on most calls, paying no
        // prefilter cost (routing even this single step through scan() measurably slows them
        // down). This is harmless to the prefilter, which can skip ahead only from the root
        // state.
        {
            // No field has changed yet, so nothing needs to be written back on this exit.
            if pos >= bytes.len() {
                return None;
            }
            // pos is always on a character boundary: it advances by whole characters, and the
            // prefilter only reports positions at character boundaries.
            let (c, char_len) = unsafe { decode_char_unchecked(bytes, pos) };
            // state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            state_id = unsafe { self.pma.next_state_id_unchecked(state_id, c) };
            pos += char_len;
            if let Some(output_pos) = unsafe { self.pma.output_pos_unchecked(state_id) } {
                self.state_id = state_id;
                self.pos = pos;
                let out = unsafe { self.pma.output_at(output_pos) };
                self.output_pos = out.parent();
                return Some(out.to_match(pos));
            }
        }
        let output_pos = scan(
            self.pma,
            &mut self.prefilter,
            &mut self.gate,
            haystack,
            &mut state_id,
            &mut pos,
        );
        self.state_id = state_id;
        self.pos = pos;
        let out = unsafe { self.pma.output_at(output_pos?) };
        self.output_pos = out.parent();
        Some(out.to_match(pos))
    }
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_overlapping_no_suffix_iter_from_iter()`].
pub struct FindOverlappingNoSuffixIterator<'a, P, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) haystack: CharWithEndOffsetIterator<P>,
    pub(crate) state_id: u32,
    pub(crate) first_call: bool,
}

impl<P, V> Iterator for FindOverlappingNoSuffixIterator<'_, P, V>
where
    P: Iterator<Item = u8>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.first_call {
            self.first_call = false;
            if let Some(value) = self.pma.root_output_value() {
                return Some(Match {
                    length: 0,
                    end: 0,
                    value,
                });
            }
        }
        for (pos, c) in self.haystack.by_ref() {
            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            self.state_id = unsafe { self.pma.next_state_id_unchecked(self.state_id, c) };
            if let Some(output_pos) = unsafe { self.pma.output_pos_unchecked(self.state_id) } {
                let out = unsafe { self.pma.output_at(output_pos) };
                return Some(out.to_match(pos));
            }
        }
        None
    }
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_overlapping_no_suffix_iter()`].
pub struct FindOverlappingNoSuffixSliceIterator<'a, P, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) haystack: P,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
    pub(crate) first_call: bool,
    // The prefilter of `pma`, or None after the gate has closed.
    pub(crate) prefilter: Option<&'a Prefilter>,
    pub(crate) gate: PrefilterGate,
}

impl<P, V> Iterator for FindOverlappingNoSuffixSliceIterator<'_, P, V>
where
    P: AsRef<str>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.first_call {
            self.first_call = false;
            if let Some(value) = self.pma.root_output_value() {
                return Some(Match {
                    length: 0,
                    end: 0,
                    value,
                });
            }
        }
        let haystack = self.haystack.as_ref();
        let bytes = haystack.as_bytes();
        let mut state_id = self.state_id;
        let mut pos = self.pos;
        // A single transition, unrolled ahead of the prefilter dispatch in scan(): pattern
        // sets that match at almost every position return here on most calls, paying no
        // prefilter cost (routing even this single step through scan() measurably slows them
        // down). This is harmless to the prefilter, which can skip ahead only from the root
        // state.
        {
            // No field has changed yet, so nothing needs to be written back on this exit.
            if pos >= bytes.len() {
                return None;
            }
            // pos is always on a character boundary: it advances by whole characters, and the
            // prefilter only reports positions at character boundaries.
            let (c, char_len) = unsafe { decode_char_unchecked(bytes, pos) };
            // state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            state_id = unsafe { self.pma.next_state_id_unchecked(state_id, c) };
            pos += char_len;
            if let Some(output_pos) = unsafe { self.pma.output_pos_unchecked(state_id) } {
                self.state_id = state_id;
                self.pos = pos;
                let out = unsafe { self.pma.output_at(output_pos) };
                return Some(out.to_match(pos));
            }
        }
        let output_pos = scan(
            self.pma,
            &mut self.prefilter,
            &mut self.gate,
            haystack,
            &mut state_id,
            &mut pos,
        );
        self.state_id = state_id;
        self.pos = pos;
        let out = unsafe { self.pma.output_at(output_pos?) };
        Some(out.to_match(pos))
    }
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::leftmost_find_iter()`].
pub struct LeftmostFindIterator<'a, P, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) haystack: P,
    pub(crate) pos: usize,
    // Cached ROOT state's output_pos.
    // Used to detect the presence of a zero-length pattern ("") and to treat it as a match
    // at every boundary between chars under leftmost semantics.
    pub(crate) init_output_pos: Option<NonZeroU32>,

    // When a zero-length pattern is enabled, we may encounter the ROOT output again without
    // consuming input. This flag ensures we advance/loop without yielding duplicate empty matches.
    pub(crate) skip_empty: bool,

    pub(crate) gate: PrefilterGate,
}

impl<P, V> LeftmostFindIterator<'_, P, V>
where
    P: AsRef<str>,
    V: Copy,
{
    /// The body of `next()` when no prefilter is used. This is kept identical to the
    /// prefilter-less implementation, since the `chars()`-based loop is faster than the
    /// position-based one of `next_filtered()`. This must always be inlined; an actual function
    /// call here would force the compiler to keep the iterator fields in memory within the loop.
    #[inline(always)]
    fn next_plain(&mut self) -> Option<Match<V>> {
        let mut state_id = ROOT_STATE_IDX;
        let mut last_output_pos: Option<NonZeroU32> = self.init_output_pos;

        'a: loop {
            let mut skips = 0;
            for c in unsafe { self.haystack.as_ref().get_unchecked(self.pos..) }.chars() {
                skips += c.len_utf8();

                // state_id is always smaller than self.pma.states.len() because
                // self.pma.next_state_id_leftmost_unchecked() ensures to return such a value.
                state_id = unsafe { self.pma.next_state_id_leftmost_unchecked(state_id, c) };
                if state_id == ROOT_STATE_IDX {
                    if let Some(output_pos) = last_output_pos {
                        let end = self.pos;
                        if last_output_pos == self.init_output_pos {
                            self.pos += c.len_utf8();
                            if self.skip_empty {
                                self.skip_empty = false;
                                continue 'a;
                            }
                        } else {
                            self.skip_empty = true;
                        }
                        let out = unsafe { self.pma.output_at(output_pos) };
                        return Some(out.to_match(end));
                    }
                } else if let Some(output_pos) = unsafe { self.pma.output_pos_unchecked(state_id) }
                {
                    last_output_pos.replace(output_pos);
                    self.pos += skips;
                    skips = 0;
                }
            }
            break;
        }

        if self.pos == self.haystack.as_ref().len() {
            self.init_output_pos.take();
        }
        if let Some(output_pos) = last_output_pos {
            let out = unsafe { self.pma.output_at(output_pos) };
            Some(out.to_match(self.pos))
        } else {
            self.pos = self.haystack.as_ref().len();
            None
        }
    }

    /// The body of `next()` while the prefilter is used. Scanning runs on byte positions so that
    /// the prefilter can skip ahead. This must always be inlined; an actual function call here
    /// would force the compiler to keep the iterator fields in memory within the loop.
    #[inline(always)]
    fn next_filtered(&mut self) -> Option<Match<V>> {
        let mut state_id = ROOT_STATE_IDX;
        let mut last_output_pos: Option<NonZeroU32> = self.init_output_pos;

        let haystack = self.haystack.as_ref();
        let bytes = haystack.as_bytes();
        let mut pos = self.pos;
        let mut prefilter = self.pma.prefilter.as_ref();
        loop {
            // The prefilter is applicable only when the automaton is in the root state with no
            // pending match, since no pattern occurrence starts before the found candidate
            // position. Note that the prefilter is never built when the pattern set contains the
            // empty string, in which case init_output_pos and last_output_pos are always Some.
            if let Some(pf) = prefilter {
                if state_id == ROOT_STATE_IDX && last_output_pos.is_none() {
                    let candidate_pos = pf.next_position_at_char_boundary(haystack, pos);
                    self.gate.record(candidate_pos - pos);
                    pos = candidate_pos;
                    if !self.gate.is_enabled() {
                        // The gate has closed; finish the current call without skipping.
                        // Subsequent calls take next_plain().
                        prefilter = None;
                    }
                }
            }
            if pos >= bytes.len() {
                break;
            }
            // pos is always on a character boundary: it advances by whole characters, and the
            // prefilter only reports positions at character boundaries.
            let (c, char_len) = unsafe { decode_char_unchecked(bytes, pos) };
            // state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_leftmost_unchecked() ensures to return such a value.
            state_id = unsafe { self.pma.next_state_id_leftmost_unchecked(state_id, c) };
            if state_id == ROOT_STATE_IDX {
                if let Some(output_pos) = last_output_pos {
                    let end = self.pos;
                    if last_output_pos == self.init_output_pos {
                        self.pos += char_len;
                        if self.skip_empty {
                            self.skip_empty = false;
                            pos = self.pos;
                            continue;
                        }
                    } else {
                        self.skip_empty = true;
                    }
                    let out = unsafe { self.pma.output_at(output_pos) };
                    return Some(out.to_match(end));
                }
            } else if let Some(output_pos) = unsafe { self.pma.output_pos_unchecked(state_id) } {
                last_output_pos.replace(output_pos);
                self.pos = pos + char_len;
            }
            pos += char_len;
        }

        if self.pos == haystack.len() {
            self.init_output_pos.take();
        }
        if let Some(output_pos) = last_output_pos {
            let out = unsafe { self.pma.output_at(output_pos) };
            Some(out.to_match(self.pos))
        } else {
            self.pos = haystack.len();
            None
        }
    }
}

impl<P, V> Iterator for LeftmostFindIterator<'_, P, V>
where
    P: AsRef<str>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        // Re-checked on every call: once the gate closes, all subsequent calls take the
        // prefilter-free variant.
        if self.pma.prefilter.is_some() && self.gate.is_enabled() {
            self.next_filtered()
        } else {
            self.next_plain()
        }
    }
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::leftmost_find_iter_experimental()`].
///
/// Matches are evaluated in linear time.
pub struct LeftmostFindIteratorExperimental<'a, P, V, B = Vec<Match<V>>, const V0: bool = false> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) haystack: P,
    pub(crate) pos: usize,
    pub(crate) state_id: u32,
    // Internal buffer storing matches to be emitted in chronological order.
    pub(crate) buf: B,
    pub(crate) gate: PrefilterGate,
    pub(crate) epsilon_emit_pos: Option<NonZeroU32>,
    pub(crate) epsilon_cursor: usize,
}

#[cold]
#[inline(never)]
fn push_cold_helper<V: Copy>(buf: &mut Vec<Match<V>>, m: Match<V>) {
    let mut tmp = core::mem::take(buf);
    tmp.push(m);
    *buf = tmp;
}

impl<'a, P, V, B, const V0: bool> LeftmostFindIteratorExperimental<'a, P, V, B, V0>
where
    P: AsRef<str>,
    V: Copy,
    B: BorrowMut<Vec<Match<V>>>,
{
    #[inline(always)]
    pub(crate) fn with_buf_impl(
        pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
        haystack: P,
        mut buf: B,
    ) -> Self {
        buf.borrow_mut().clear();
        // SAFETY: Any valid constructed PMA contains at least ROOT_STATE_IDX (0) and DEAD_STATE_IDX (1).
        let root_state = unsafe { pma.states.get_unchecked(usize::from_u32(ROOT_STATE_IDX)) };
        let pos = if root_state.base().is_none() {
            haystack.as_ref().len()
        } else {
            0
        };
        Self {
            pma,
            haystack,
            pos,
            state_id: ROOT_STATE_IDX,
            buf,
            gate: PrefilterGate::new(),
            epsilon_emit_pos: root_state.output_pos(),
            epsilon_cursor: 0,
        }
    }

    /// Core scanning engine that advances the automaton forward until a match is found or EOF is reached.
    #[inline(always)]
    fn scan_impl<const FILTERED: bool>(&mut self) -> Option<Match<V>> {
        let haystack = self.haystack.as_ref();
        let bytes = haystack.as_bytes();

        let mut pos = self.pos;
        let mut state_id = self.state_id;
        let states = self.pma.states.as_slice();
        let mapper = &self.pma.mapper;

        let mut prefilter = if FILTERED {
            self.pma.prefilter.as_ref()
        } else {
            None
        };

        // Main streaming scan: decode characters sequentially from text
        while pos < bytes.len() {
            // Optional prefilter acceleration when sitting at ROOT_STATE_IDX:
            if let Some(pf) = prefilter {
                if state_id == ROOT_STATE_IDX {
                    let candidate_pos = pf.next_position_at_char_boundary(haystack, pos);
                    self.gate.record(candidate_pos - pos);
                    pos = candidate_pos;
                    if !self.gate.is_enabled() {
                        prefilter = None;
                    }
                    if pos >= bytes.len() {
                        break;
                    }
                }
            }

            // SAFETY: pos < bytes.len() and pos sits on a valid character boundary.
            let (c, char_len) = unsafe { decode_char_unchecked(bytes, pos) };

            if let Some(code) = mapper.get(c) {
                // Character `c` is mapped to alphabet `code`.
                // Advance down the trie if transition exists on alphabet code, or follow failure links on mismatch.
                loop {
                    // SAFETY: state_id is a valid state index.
                    let state = unsafe { states.get_unchecked(usize::from_u32(state_id)) };
                    if let Some(base) = state.base() {
                        // Double-array child transition lookup: child_id = base ^ code
                        let child_id = base.get() ^ code;
                        // SAFETY: In a double-array trie, for any allocated state with `base`,
                        // child_id = base ^ code is guaranteed to fall strictly within the allocated bounds of `states`.
                        if unsafe { states.get_unchecked(usize::from_u32(child_id)).check() }
                            == state_id
                        {
                            // Child transition found: advance state and break out of inner loop
                            // to consume `char_len` bytes in the text.
                            state_id = child_id;
                            break;
                        }
                    } else {
                        // Leaf states have no outgoing edges. In a trie, every leaf completes a
                        // pattern with a single-match emit (gap = 0, pred = None).
                        // The leaf match ends at pos; the next search begins with c at pos from ROOT.
                        // SAFETY: Every leaf state has a valid `output_pos` pointing to an emit.
                        // This invariant is guaranteed by construction and enforced in safe `deserialize()`.
                        let ep = unsafe { state.output_pos().unwrap_unchecked() };
                        let emit =
                            unsafe { self.pma.emits.get_unchecked(usize::from_u32(ep.get()) - 1) };
                        self.state_id = unsafe { Self::step_root(states, code) };
                        self.pos = pos + char_len;
                        return Some(emit.to_match(pos));
                    }

                    if state_id == ROOT_STATE_IDX {
                        // Root state cannot transition on `code`, and has no failure link to follow.
                        // Break from the inner transition loop so the outer loop advances to the next character.
                        break;
                    }
                    state_id = state.leftmost_experimental_fail();
                    if let Some(ep) = state.output_pos() {
                        // Mismatch occurred at `state`. Emit committed matches (`ep`) that precede
                        // the pending suffix `state.leftmost_experimental_fail()`.
                        // SAFETY: `ep` is a valid emit index from `state.output_pos()`, and `pos >= pattern_length`.
                        let m = unsafe {
                            Self::extract_emits(&self.pma.emits, ep, pos, self.buf.borrow_mut())
                        };
                        if state_id == ROOT_STATE_IDX {
                            // Pending suffix reached ROOT. Step `ROOT` on `code` and advance past `c`.
                            // SAFETY: `states` has ROOT_STATE_IDX and `code` is in alphabet.
                            self.state_id = unsafe { Self::step_root(states, code) };
                            self.pos = pos + char_len;
                        } else {
                            // Pending suffix is a non-root state. Character `c` at `pos` has not been
                            // consumed yet; retain `pos` so the next call attempts transition on `c`.
                            self.state_id = state_id;
                            self.pos = pos;
                        }
                        return Some(m);
                    }
                }
            } else {
                // Character `c` is not in the alphabet. Drain any pending matches along the failure chain.
                // When sitting at ROOT_STATE_IDX, there are no active pattern prefixes to drain,
                // so unmapped characters (spaces, punctuation) bypass failure traversal immediately.
                if state_id != ROOT_STATE_IDX {
                    // SAFETY: `state_id` is a valid state index, and pos sits on a valid character boundary.
                    if let Some(m) = unsafe {
                        Self::drain_fail_chain(
                            states,
                            &self.pma.emits,
                            self.buf.borrow_mut(),
                            &mut state_id,
                            pos,
                        )
                    } {
                        // Match found along the failure chain. Retain `pos` so further matches
                        // along the chain can be drained on subsequent calls.
                        self.pos = pos;
                        self.state_id = state_id;
                        return Some(m);
                    }
                    // All pending failure matches drained; state_id was reset to ROOT_STATE_IDX by drain_fail_chain.
                }
            }

            pos += char_len;
        }

        // Text boundary reached (EOF). Drain any remaining matches along the failure chain.
        if state_id == ROOT_STATE_IDX {
            self.pos = pos;
            return None;
        }
        // SAFETY: `state_id` is a valid state index, and pos sits on a valid character boundary.
        let m = unsafe {
            Self::drain_fail_chain(
                states,
                &self.pma.emits,
                self.buf.borrow_mut(),
                &mut state_id,
                pos,
            )
        };
        self.pos = pos;
        self.state_id = state_id;
        m
    }

    #[inline(always)]
    fn scan(&mut self) -> Option<Match<V>> {
        if self.pma.prefilter.is_some() && self.gate.is_enabled() {
            self.scan_impl::<true>()
        } else {
            self.scan_impl::<false>()
        }
    }

    /// Steps from `ROOT_STATE_IDX` on alphabet `code`, returning the child state or `ROOT_STATE_IDX`.
    ///
    /// Avoids loop re-entry overhead when resetting to root by advancing on the current character
    /// in the same cycle.
    ///
    /// # Safety
    ///
    /// - `states` must contain at least `ROOT_STATE_IDX + 1` elements.
    /// - `code` must be a valid mapped alphabet code (`code < mapper.alphabet_size()`).
    /// - `states` must be a valid double-array table constructed by `CharwiseDoubleArrayAhoCorasickBuilder`.
    #[inline(always)]
    unsafe fn step_root(states: &[State], code: u32) -> u32 {
        // SAFETY: caller guarantees `states` contains at least `ROOT_STATE_IDX + 1` elements.
        if let Some(base) = unsafe { states.get_unchecked(usize::from_u32(ROOT_STATE_IDX)).base() }
        {
            let child_id = base.get() ^ code;
            // SAFETY: caller guarantees `states` is a valid double-array table, ensuring that for any
            // valid `base` and mapped `code`, `child_id` falls strictly within the allocated bounds of `states`.
            if unsafe { states.get_unchecked(usize::from_u32(child_id)).check() } == ROOT_STATE_IDX
            {
                return child_id;
            }
        }
        ROOT_STATE_IDX
    }

    /// Extracts committed matches along the predecessor chain in chronological order.
    ///
    /// The earliest match is returned directly; any subsequent matches are pushed into `buf`.
    /// `anchor` is the byte offset ending the matched path so far (the start offset of the
    /// mismatched character). An invalid `anchor` or corrupt automaton causes subtraction to wrap,
    /// producing an out-of-bounds offset in [`Match`].
    ///
    /// # Safety
    ///
    /// `head_pos` and all reachable `pred` indices must be valid 1-based indices into `emits`.
    #[inline(always)]
    unsafe fn extract_emits(
        emits: &[crate::Emit<V>],
        head_pos: NonZeroU32,
        mut anchor: usize,
        buf: &mut Vec<Match<V>>,
    ) -> Match<V> {
        let mut curr_ep = head_pos;
        loop {
            // SAFETY: head_pos and all chained pred links are valid 1-based indices in emits.
            let emit = unsafe { emits.get_unchecked(usize::from_u32(curr_ep.get()) - 1) };
            let end = anchor - usize::from_u32(emit.gap);
            anchor = end - usize::from_u32(emit.length);
            let m = emit.to_match(end);
            let Some(pred) = emit.pred else {
                return m;
            };
            if V0 {
                if buf.len() < buf.capacity() {
                    let len = buf.len();
                    core::ptr::write(buf.as_mut_ptr().add(len), m);
                    buf.set_len(len + 1);
                } else {
                    push_cold_helper(buf, m);
                }
            } else {
                buf.push(m);
            }
            curr_ep = pred;
        }
    }

    /// Drains the failure chain from `*state_id`, returning the first reachable match if any.
    ///
    /// Uses bit 31 of `fail` to skip failure traversal when no states along the chain contain emits.
    ///
    /// # Safety
    ///
    /// - `*state_id` must be a valid state index in `states`.
    /// - All failure links reachable from `*state_id` must be valid state indices in `states`.
    /// - Any `output_pos` on reachable states must satisfy the safety contract of [`Self::extract_emits()`].
    #[inline(always)]
    unsafe fn drain_fail_chain(
        states: &[State],
        emits: &[crate::Emit<V>],
        buf: &mut Vec<Match<V>>,
        state_id: &mut u32,
        pos: usize,
    ) -> Option<Match<V>> {
        while *state_id != ROOT_STATE_IDX {
            // SAFETY: caller guarantees *state_id is a valid state index in states.
            let state = unsafe { states.get_unchecked(usize::from_u32(*state_id)) };
            if !state.leftmost_experimental_has_emit() {
                break;
            }
            *state_id = state.leftmost_experimental_fail();
            if let Some(ep) = state.output_pos() {
                // SAFETY: caller guarantees states and emits invariants are preserved.
                let m = unsafe { Self::extract_emits(emits, ep, pos, buf) };
                return Some(m);
            }
        }
        *state_id = ROOT_STATE_IDX;
        None
    }
}

impl<'a, P, V, B> LeftmostFindIteratorExperimental<'a, P, V, B, false>
where
    P: AsRef<str>,
    V: Copy,
    B: BorrowMut<Vec<Match<V>>>,
{
    /// Creates a new experimental leftmost iterator using a provided reusable buffer.
    #[inline(always)]
    pub fn with_buf(pma: &'a CharwiseDoubleArrayAhoCorasick<V>, haystack: P, buf: B) -> Self {
        Self::with_buf_impl(pma, haystack, buf)
    }
}

impl<'a, P, V, B> LeftmostFindIteratorExperimental<'a, P, V, B, true>
where
    P: AsRef<str>,
    V: Copy,
    B: BorrowMut<Vec<Match<V>>>,
{
    /// Creates a new experimental leftmost iterator using push_pull_on_grow.
    #[inline(always)]
    pub fn with_buf_push_pull(
        pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
        haystack: P,
        buf: B,
    ) -> Self {
        Self::with_buf_impl(pma, haystack, buf)
    }
}

impl<'a, P, V, B, const V0: bool> Iterator for LeftmostFindIteratorExperimental<'a, P, V, B, V0>
where
    P: AsRef<str>,
    V: Copy,
    B: BorrowMut<Vec<Match<V>>>,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        // When the empty pattern "" is absent, yield any buffered matches or scan forward.
        let Some(ep) = self.epsilon_emit_pos else {
            if let Some(m) = self.buf.borrow_mut().pop() {
                return Some(m);
            }
            return self.scan();
        };

        // When "" is present, interleave zero-length matches at character boundaries
        // not spanned by non-empty matches.
        if self.buf.borrow_mut().is_empty() {
            if let Some(m) = self.scan() {
                self.buf.borrow_mut().push(m);
            }
        }

        let bytes = self.haystack.as_ref().as_bytes();
        let target = self
            .buf
            .borrow_mut()
            .last()
            .map_or(bytes.len(), Match::start);
        // `deserialize()` for now does not validate match lengths or state depths to avoid
        // expensive trie traversal (malformed automata may return inaccurate ranges).
        // If a malformed emit causes `Match::start()` to wrap, clamping prevents OOB decoding.
        let target = target.min(bytes.len());
        // SAFETY: `ep` is verified during automaton construction to point to a valid emit node for the empty pattern.
        let epsilon = unsafe { self.pma.emits.get_unchecked(usize::from_u32(ep.get()) - 1) };

        debug_assert_eq!(epsilon.length, 0);
        debug_assert_eq!(epsilon.gap, 0);
        debug_assert!(epsilon.pred.is_none());

        // Emit zero-length matches at character boundaries prior to the start of the next non-empty match:
        if self.epsilon_cursor < target {
            let cursor = self.epsilon_cursor;
            // SAFETY: `cursor < target <= bytes.len()`.
            // Advances even for an invalid cursor resulting from a malformed automaton.
            self.epsilon_cursor +=
                utf8_char_len_from_first_byte(unsafe { *bytes.get_unchecked(cursor) }).unwrap_or(1);
            return Some(epsilon.to_match(cursor));
        }

        // Emit the non-empty match and advance cursor past its end:
        if let Some(m) = self.buf.borrow_mut().pop() {
            if m.end() < bytes.len() {
                // SAFETY: guarded by `m.end() < bytes.len()`.
                self.epsilon_cursor = m.end()
                    + utf8_char_len_from_first_byte(unsafe { *bytes.get_unchecked(m.end()) })
                        .unwrap_or(1);
            } else {
                self.epsilon_emit_pos.take();
            }
            return Some(m);
        }

        // No more non-empty matches and cursor >= bytes.len(). Epsilon matching is complete.
        self.epsilon_emit_pos.take();

        // Trailing zero-length match at EOF when the cursor lands exactly on the text boundary.
        if self.epsilon_cursor == bytes.len() {
            return Some(epsilon.to_match(bytes.len()));
        }

        // Cursor is past EOF due to a malformed automaton.
        None
    }
}

/// Iterator created by [`LeftmostFinderExperimental::find_iter()`],
/// borrowing the internal buffer held by [`LeftmostFinderExperimental`].
pub type LeftmostFindBorrowedIterator<'a, 'b, P, V> =
    LeftmostFindIteratorExperimental<'a, P, V, &'b mut Vec<Match<V>>>;

/// A reusable finder for non-overlapping leftmost matches that retains an internal buffer across searches.
///
/// This finder is created by [`CharwiseDoubleArrayAhoCorasick::leftmost_finder_experimental()`].
///
/// Matches are evaluated in linear time.
/// While [`leftmost_find_iter_experimental()`](crate::CharwiseDoubleArrayAhoCorasick::leftmost_find_iter_experimental)
/// allocates an internal buffer for each search, this finder retains its buffer across searches,
/// eliminating repeated heap allocations during repeated searches.
#[derive(Clone)]
pub struct LeftmostFinderExperimental<'a, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) buf: Vec<Match<V>>,
}

impl<'a, V: Copy> LeftmostFinderExperimental<'a, V> {
    pub(crate) fn new(pma: &'a CharwiseDoubleArrayAhoCorasick<V>) -> Self {
        assert!(
            pma.match_kind.is_leftmost_experimental(),
            "Error: match_kind must be leftmost_longest_experimental or leftmost_first_experimental."
        );
        Self {
            pma,
            buf: Vec::new(),
        }
    }

    /// Returns an iterator of non-overlapping leftmost matches in the given haystack,
    /// borrowing the internal buffer held by [`LeftmostFinderExperimental`] across searches.
    ///
    /// # Arguments
    ///
    /// * `haystack` - String to search in.
    #[inline(always)]
    pub fn find_iter<'b, P>(&'b mut self, haystack: P) -> LeftmostFindBorrowedIterator<'a, 'b, P, V>
    where
        P: AsRef<str>,
    {
        LeftmostFindIteratorExperimental::with_buf(self.pma, haystack, &mut self.buf)
    }

    /// Evaluates search using the unoptimized V0 logic (&mut state_id without EOF guard / root branch elimination).
    #[doc(hidden)]
    #[inline(always)]
    pub fn find_iter_v0<'b, P>(
        &'b mut self,
        haystack: P,
    ) -> LeftmostFindIteratorExperimental<'a, P, V, &'b mut Vec<Match<V>>, true>
    where
        P: AsRef<str>,
    {
        LeftmostFindIteratorExperimental::<P, V, &'b mut Vec<Match<V>>, true>::with_buf_impl(
            self.pma,
            haystack,
            &mut self.buf,
        )
    }
}

/// Stepper created by [`CharwiseDoubleArrayAhoCorasick::find_stepper()`].
#[derive(Clone)]
pub struct FindStepper<'a, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
    pub(crate) output_pos: Option<NonZeroU32>,
}

impl<V> FindStepper<'_, V>
where
    V: Copy,
{
    /// Consumes one character and transitions the state.
    #[inline(always)]
    pub fn consume(&mut self, c: char) {
        self.pos += c.len_utf8();
        if self.pma.root_output_value().is_some() {
            return;
        }
        // state_id is always smaller than self.pma.states.len() because
        // self.pma.next_state_id_unchecked() ensures to return such a value.
        unsafe {
            self.state_id = self.pma.next_state_id_unchecked(self.state_id, c);
            self.output_pos = self.pma.output_pos_unchecked(self.state_id);
        }
        if self.output_pos.is_some() {
            self.state_id = ROOT_STATE_IDX;
        }
    }

    /// Returns the match at the current state, if any.
    #[must_use]
    #[inline(always)]
    pub fn matches(&self) -> Option<Match<V>> {
        self.output_pos.map(|output_pos| unsafe {
            let out = self.pma.output_at(output_pos);
            out.to_match(self.pos)
        })
    }

    /// Returns the depth of the current state from the root state.
    ///
    /// If the depths have not been cached by [`CharwiseDoubleArrayAhoCorasick::cache_depths()`],
    /// `None` is returned.
    #[must_use]
    #[inline(always)]
    pub fn depth(&self) -> Option<u32> {
        self.pma.depths.get(usize::from_u32(self.state_id)).copied()
    }
}

/// Iterator created by [`FindOverlappingStepper::matches()`].
pub struct FindOverlappingStepperIterator<'a, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) pos: usize,
    pub(crate) output_pos: Option<NonZeroU32>,
}

impl<V> Iterator for FindOverlappingStepperIterator<'_, V>
where
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(output_pos) = self.output_pos {
            let out = unsafe { self.pma.output_at(output_pos) };
            self.output_pos = out.parent();
            return Some(out.to_match(self.pos));
        }
        None
    }
}

/// Stepper created by [`CharwiseDoubleArrayAhoCorasick::find_overlapping_stepper()`].
#[derive(Clone)]
pub struct FindOverlappingStepper<'a, V> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
}

impl<'a, V> FindOverlappingStepper<'a, V>
where
    V: Copy,
{
    /// Consumes one character and transitions the state.
    #[inline(always)]
    pub fn consume(&mut self, c: char) {
        // self.state_id is always smaller than self.pma.states.len() because
        // self.pma.next_state_id_unchecked() ensures to return such a value.
        self.state_id = unsafe { self.pma.next_state_id_unchecked(self.state_id, c) };
        self.pos += c.len_utf8();
    }

    /// Returns an iterator that yields matches at the current position.
    #[must_use]
    #[inline(always)]
    pub fn matches(&self) -> FindOverlappingStepperIterator<'a, V> {
        let output_pos = unsafe {
            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            self.pma.output_pos_unchecked(self.state_id)
        };
        FindOverlappingStepperIterator {
            pma: self.pma,
            pos: self.pos,
            output_pos,
        }
    }

    /// Returns the depth in characters of the current state from the root state.
    ///
    /// If the depths have not been cached by [`CharwiseDoubleArrayAhoCorasick::cache_depths()`],
    /// `None` is returned.
    #[must_use]
    #[inline(always)]
    pub fn depth(&self) -> Option<u32> {
        self.pma.depths.get(usize::from_u32(self.state_id)).copied()
    }
}

/// Returns the parent index of element `idx` with state `s`, or `None` if the element
/// is the root or is not reachable from its parent via a valid label.
#[inline(always)]
fn parent_of(states: &[State], chars: &[Option<char>], idx: u32, s: &State) -> Option<u32> {
    let parent = s.check();
    let base = states.get(usize::from_u32(parent))?.base()?;
    let label = usize::from_u32(base.get() ^ idx);
    (idx != ROOT_STATE_IDX && matches!(chars.get(label), Some(Some(_)))).then_some(parent)
}

/// Returns the transition character from the state with the given BASE value to element `idx`.
#[inline(always)]
fn label(chars: &[Option<char>], base: u32, idx: u32) -> char {
    // Elements in `PatternIterator::children` are guaranteed to have valid labels.
    chars[usize::from_u32(base ^ idx)].unwrap()
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::iter()`].
pub struct PatternIterator<'a, V> {
    pma: &'a CharwiseDoubleArrayAhoCorasick<V>,
    // Characters corresponding to mapped labels.
    chars: Vec<Option<char>>,
    // Children grouped by their parents. The children of a state with index `i` are stored in
    // `children[offsets[i]..offsets[i + 1]]`.
    offsets: Vec<u32>,
    children: Vec<u32>,
    // BASE values and ranges of unvisited children for states along the path from the root.
    stack: Vec<(u32, usize, usize)>,
    pattern: String,
    output_pos: Option<NonZeroU32>,
}

impl<'a, V> PatternIterator<'a, V> {
    /// Creates an iterator that yields patterns through a depth-first traversal of the trie.
    ///
    /// Because the double array does not maintain parent-to-child links, elements are grouped
    /// in advance by their parents (`check`). Children are visited in order of their
    /// characters, ensuring that patterns are yielded in lexicographical order. Each element
    /// belongs to at most one group and the root to none, bounding the traversal complexity to
    /// the number of elements even in malformed automata.
    pub(crate) fn new(pma: &'a CharwiseDoubleArrayAhoCorasick<V>) -> Self {
        // Restores characters from mapped labels.
        let alphabet_size = usize::from_u32(pma.mapper.alphabet_size());
        let mut chars = vec![None; alphabet_size.min(pma.mapper.table.len())];
        for (c, &code) in pma.mapper.table.iter().enumerate() {
            if let Some(slot) = chars.get_mut(usize::from_u32(code)) {
                *slot = u32::try_from(c).ok().and_then(char::from_u32);
            }
        }

        let (offsets, children) = Self::group_children(&pma.states, &chars);
        let mut it = Self {
            pma,
            chars,
            offsets,
            children,
            stack: vec![],
            pattern: String::new(),
            output_pos: None,
        };
        if let Some(s) = pma.states.get(usize::from_u32(ROOT_STATE_IDX)) {
            it.push_state(ROOT_STATE_IDX, s);
            it.output_pos = s.output_pos();
        }
        it
    }

    /// Groups all elements by their parents' indices using counting sort.
    fn group_children(states: &[State], chars: &[Option<char>]) -> (Vec<u32>, Vec<u32>) {
        let len = u32::try_from(states.len()).unwrap_or(u32::MAX);
        let mut offsets = vec![0; usize::from_u32(len) + 2];
        for (idx, s) in (0..len).zip(states) {
            if let Some(parent) = parent_of(states, chars, idx, s) {
                offsets[usize::from_u32(parent) + 2] += 1;
            }
        }
        for i in 1..offsets.len() {
            offsets[i] += offsets[i - 1];
        }
        let mut children = vec![0; usize::from_u32(offsets[usize::from_u32(len) + 1])];
        for (idx, s) in (0..len).zip(states) {
            if let Some(parent) = parent_of(states, chars, idx, s) {
                let pos = &mut offsets[usize::from_u32(parent) + 1];
                children[usize::from_u32(*pos)] = idx;
                *pos += 1;
            }
        }
        offsets.pop();
        (offsets, children)
    }

    /// Pushes the children of a state with the given index onto the stack.
    fn push_state(&mut self, state_id: u32, s: &State) {
        let base = s.base().map_or(0, NonZeroU32::get);
        let state_id = usize::from_u32(state_id);
        let start = usize::from_u32(self.offsets[state_id]);
        let end = usize::from_u32(self.offsets[state_id + 1]);
        let chars = &self.chars;
        self.children[start..end].sort_unstable_by_key(|&idx| label(chars, base, idx));
        self.stack.push((base, start, end));
    }
}

impl<V> Iterator for PatternIterator<'_, V>
where
    V: Copy,
{
    type Item = (String, V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // The output list of a state contains patterns ending at that state, followed by
            // shorter patterns registered for its suffixes, which must be skipped.
            if let Some(output_pos) = self.output_pos.take() {
                if self.pma.match_kind.is_leftmost_experimental() {
                    let Some(emit) = self.pma.emits.get(usize::from_u32(output_pos.get() - 1))
                    else {
                        // Reached only by malformed automata. Stops iteration permanently.
                        self.stack.clear();
                        return None;
                    };
                    if emit.gap == 0 && usize::from_u32(emit.length) == self.pattern.len() {
                        return Some((self.pattern.clone(), emit.value));
                    }
                } else {
                    let Some(out) = self.pma.outputs.get(usize::from_u32(output_pos.get() - 1))
                    else {
                        // Reached only by malformed automata. Stops iteration permanently.
                        self.stack.clear();
                        return None;
                    };
                    if usize::from_u32(out.length) == self.pattern.len() {
                        self.output_pos = out.parent();
                        return Some((self.pattern.clone(), out.value()));
                    }
                }
            }
            let (base, next, end) = self.stack.last_mut()?;
            if next < end {
                let child = self.children[*next];
                *next += 1;
                let c = label(&self.chars, *base, child);
                let s = &self.pma.states[usize::from_u32(child)];
                self.pattern.push(c);
                self.push_state(child, s);
                self.output_pos = s.output_pos();
            } else {
                self.stack.pop();
                self.pattern.pop();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

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

    #[test]
    fn test_overlapping_no_suffix_iter() {
        let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(["a", "ab", ""]).unwrap();
        let result = pma
            .find_overlapping_no_suffix_iter("ab")
            .collect::<Vec<_>>();
        assert_eq!(
            vec![
                Match {
                    length: 0,
                    end: 0,
                    value: 2
                },
                Match {
                    length: 1,
                    end: 1,
                    value: 0
                },
                Match {
                    length: 2,
                    end: 2,
                    value: 1
                },
            ],
            result
        );
    }

    #[test]
    fn test_overlapping_stepper_depth() {
        let mut pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(["世界", "界"]).unwrap();
        let stepper = pma.find_overlapping_stepper();
        assert_eq!(None, stepper.depth());
        pma.cache_depths().unwrap();
        let mut stepper = pma.find_overlapping_stepper();
        assert_eq!(Some(0), stepper.depth());
        stepper.consume('世');
        assert_eq!(Some(1), stepper.depth());
        stepper.consume('界');
        assert_eq!(Some(2), stepper.depth());
        stepper.consume('界');
        assert_eq!(Some(1), stepper.depth());
    }

    #[test]
    fn test_find_stepper_depth() {
        let mut pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(["世界"]).unwrap();
        let stepper = pma.find_stepper();
        assert_eq!(None, stepper.depth());
        pma.cache_depths().unwrap();
        let mut stepper = pma.find_stepper();
        assert_eq!(Some(0), stepper.depth());
        stepper.consume('世');
        assert_eq!(Some(1), stepper.depth());
        stepper.consume('界');
        assert!(stepper.matches().is_some());
        assert_eq!(Some(0), stepper.depth());
    }

    #[test]
    fn test_overlapping_stepper_lifetime() {
        let pma = CharwiseDoubleArrayAhoCorasick::new(["a", "ab"]).unwrap();
        let mut stepper = pma.find_overlapping_stepper();
        stepper.consume('a');
        let mut it1 = stepper.matches();
        stepper.consume('b');
        let mut it2 = stepper.matches();
        assert_eq!(
            Some(Match {
                length: 1,
                end: 1,
                value: 0
            }),
            it1.next()
        );
        assert_eq!(
            Some(Match {
                length: 2,
                end: 2,
                value: 1
            }),
            it2.next()
        );
    }
}
