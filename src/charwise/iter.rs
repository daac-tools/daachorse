//! Iterators for [`CharwiseDoubleArrayAhoCorasick`].

use core::iter::Enumerate;
use core::num::NonZeroU32;

use crate::charwise::CharwiseDoubleArrayAhoCorasick;
use crate::prefilter::{Prefilter, PrefilterGate};
use crate::utils::FromU32;
use crate::{Match, ROOT_STATE_IDX};

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
    /// `None`　is returned.
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
    /// `None`　is returned.
    #[must_use]
    #[inline(always)]
    pub fn depth(&self) -> Option<u32> {
        self.pma.depths.get(usize::from_u32(self.state_id)).copied()
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
