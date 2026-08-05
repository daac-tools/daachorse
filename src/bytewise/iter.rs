//! Iterators for [`DoubleArrayAhoCorasick`].

use core::iter::Enumerate;
use core::num::NonZeroU32;

use crate::bytewise::DoubleArrayAhoCorasick;
use crate::prefilter::{Prefilter, PrefilterGate};
use crate::utils::FromU32;
use crate::{Match, ROOT_STATE_IDX};

/// Runs the automaton over `haystack` and returns the output position of the next match, or
/// `None` when the end of the haystack is reached. While `*prefilter` is `Some`, whenever the
/// automaton is in the root state, scanning skips ahead to the next candidate position: no
/// pattern occurrence starts before it, so the bytes in between cannot affect the results.
/// Each skip length is recorded into `gate`; once the gate closes because the skips turned out
/// too short to pay off, `*prefilter` is cleared (disabling it for the callers' later calls as
/// well) and scanning falls through to the plain loop.
#[inline(always)]
fn scan<V>(
    pma: &DoubleArrayAhoCorasick<V>,
    prefilter: &mut Option<&Prefilter>,
    gate: &mut PrefilterGate,
    haystack: &[u8],
    state_id: &mut u32,
    pos: &mut usize,
) -> Option<NonZeroU32> {
    if let Some(pf) = *prefilter {
        loop {
            if *state_id == ROOT_STATE_IDX {
                let candidate_pos = pf.next_position(haystack, *pos);
                gate.record(candidate_pos - *pos);
                *pos = candidate_pos;
                if !gate.is_enabled() {
                    // The prefilter does not pay off on this haystack; drop it and continue
                    // with the plain loop below.
                    *prefilter = None;
                    break;
                }
            }
            let &c = haystack.get(*pos)?;
            // state_id is always smaller than pma.states.len() because
            // pma.next_state_id_unchecked() ensures to return such a value.
            *state_id = unsafe { pma.next_state_id_unchecked(*state_id, c) };
            *pos += 1;
            if let Some(output_pos) = unsafe { pma.output_pos_unchecked(*state_id) } {
                return Some(output_pos);
            }
        }
    }
    loop {
        let &c = haystack.get(*pos)?;
        // state_id is always smaller than pma.states.len() because
        // pma.next_state_id_unchecked() ensures to return such a value.
        *state_id = unsafe { pma.next_state_id_unchecked(*state_id, c) };
        *pos += 1;
        if let Some(output_pos) = unsafe { pma.output_pos_unchecked(*state_id) } {
            return Some(output_pos);
        }
    }
}

/// Iterator created by [`DoubleArrayAhoCorasick::find_iter_from_iter()`].
pub struct FindIterator<'a, P, V> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
    pub(crate) haystack: Enumerate<P>,
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
        if let Some(value) = unsafe { self.pma.root_output_value() } {
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
                    end: pos + 1,
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
                return Some(out.to_match(pos + 1));
            }
        }
        None
    }
}

/// Iterator created by [`DoubleArrayAhoCorasick::find_iter()`].
pub struct FindSliceIterator<'a, P, V> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
    pub(crate) haystack: P,
    pub(crate) pos: usize,
    pub(crate) first_call: bool,
    // The prefilter of `pma`, or None after the gate has closed.
    pub(crate) prefilter: Option<&'a Prefilter>,
    pub(crate) gate: PrefilterGate,
}

impl<P, V> Iterator for FindSliceIterator<'_, P, V>
where
    P: AsRef<[u8]>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let haystack = self.haystack.as_ref();
        // When the pattern set contains the empty string, it matches at every byte boundary
        // and this block handles all calls; the scanning loop below never runs. No prefilter
        // is built for such a pattern set.
        if let Some(value) = unsafe { self.pma.root_output_value() } {
            return if self.first_call {
                self.first_call = false;
                Some(Match {
                    length: 0,
                    end: 0,
                    value,
                })
            } else if self.pos < haystack.len() {
                self.pos += 1;
                Some(Match {
                    length: 0,
                    end: self.pos,
                    value,
                })
            } else {
                None
            };
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
            let c = *haystack.get(pos)?;
            // state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            state_id = unsafe { self.pma.next_state_id_unchecked(state_id, c) };
            pos += 1;
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

/// Iterator created by [`DoubleArrayAhoCorasick::find_overlapping_iter_from_iter()`].
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
            let out = unsafe { self.pma.output_at(output_pos) };
            self.output_pos = out.parent();
            return Some(out.to_match(self.pos));
        }
        for (pos, c) in self.haystack.by_ref() {
            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            self.state_id = unsafe { self.pma.next_state_id_unchecked(self.state_id, c) };
            if let Some(output_pos) = unsafe { self.pma.output_pos_unchecked(self.state_id) } {
                self.pos = pos + 1;
                let out = unsafe { self.pma.output_at(output_pos) };
                self.output_pos = out.parent();
                return Some(out.to_match(self.pos));
            }
        }
        None
    }
}

/// Iterator created by [`DoubleArrayAhoCorasick::find_overlapping_iter()`].
pub struct FindOverlappingSliceIterator<'a, P, V> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
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
    P: AsRef<[u8]>,
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
        let mut state_id = self.state_id;
        let mut pos = self.pos;
        // A single transition, unrolled ahead of the prefilter dispatch in scan(): pattern
        // sets that match at almost every position return here on most calls, paying no
        // prefilter cost (routing even this single step through scan() measurably slows them
        // down). This is harmless to the prefilter, which can skip ahead only from the root
        // state.
        {
            // No field has changed yet, so nothing needs to be written back on this exit.
            let c = *haystack.get(pos)?;
            // state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            state_id = unsafe { self.pma.next_state_id_unchecked(state_id, c) };
            pos += 1;
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

/// Iterator created by [`DoubleArrayAhoCorasick::find_overlapping_no_suffix_iter_from_iter()`].
pub struct FindOverlappingNoSuffixIterator<'a, P, V> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
    pub(crate) haystack: Enumerate<P>,
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
            // This iterator is created only for standard matching, as required by
            // root_output_value().
            if let Some(value) = unsafe { self.pma.root_output_value() } {
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
                return Some(out.to_match(pos + 1));
            }
        }
        None
    }
}

/// Iterator created by [`DoubleArrayAhoCorasick::find_overlapping_no_suffix_iter()`].
pub struct FindOverlappingNoSuffixSliceIterator<'a, P, V> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
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
    P: AsRef<[u8]>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.first_call {
            self.first_call = false;
            if let Some(value) = unsafe { self.pma.root_output_value() } {
                return Some(Match {
                    length: 0,
                    end: 0,
                    value,
                });
            }
        }
        let haystack = self.haystack.as_ref();
        let mut state_id = self.state_id;
        let mut pos = self.pos;
        // A single transition, unrolled ahead of the prefilter dispatch in scan(): pattern
        // sets that match at almost every position return here on most calls, paying no
        // prefilter cost (routing even this single step through scan() measurably slows them
        // down). This is harmless to the prefilter, which can skip ahead only from the root
        // state.
        {
            // No field has changed yet, so nothing needs to be written back on this exit.
            let c = *haystack.get(pos)?;
            // state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            state_id = unsafe { self.pma.next_state_id_unchecked(state_id, c) };
            pos += 1;
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

/// Iterator created by [`DoubleArrayAhoCorasick::leftmost_find_iter()`].
pub struct LeftmostFindIterator<'a, P, V>
where
    P: AsRef<[u8]>,
{
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
    pub(crate) haystack: P,
    pub(crate) pos: usize,
    // Cached ROOT state's output_pos.
    // Used to detect the presence of a zero-length pattern ("") and to treat it as a match
    // at every boundary between bytes under leftmost semantics.
    pub(crate) init_output_pos: Option<NonZeroU32>,

    // When a zero-length pattern is enabled, we may encounter the ROOT output again without
    // consuming input. This flag ensures we advance/loop without yielding duplicate empty matches.
    pub(crate) skip_empty: bool,

    pub(crate) gate: PrefilterGate,
}

impl<P, V> LeftmostFindIterator<'_, P, V>
where
    P: AsRef<[u8]>,
    V: Copy,
{
    /// The body of `next()`, compiled into two variants. With `FILTERED = false`, all the
    /// prefilter code folds away and the scanning loop is as fast as if the prefilter did not
    /// exist. This must always be inlined; an actual function call here would force the compiler
    /// to keep the iterator fields in memory within the loop.
    #[inline(always)]
    fn next_impl<const FILTERED: bool>(&mut self) -> Option<Match<V>> {
        let mut state_id = ROOT_STATE_IDX;
        let mut last_output_pos = self.init_output_pos;

        let haystack = self.haystack.as_ref();
        let mut pos = self.pos;
        let mut prefilter = if FILTERED {
            self.pma.prefilter.as_ref()
        } else {
            None
        };
        loop {
            // The prefilter is applicable only when the automaton is in the root state with no
            // pending match, since no pattern occurrence starts before the found candidate
            // position. Note that the prefilter is never built when the pattern set contains the
            // empty string, in which case init_output_pos and last_output_pos are always Some.
            if let Some(pf) = prefilter {
                if state_id == ROOT_STATE_IDX && last_output_pos.is_none() {
                    let candidate_pos = pf.next_position(haystack, pos);
                    self.gate.record(candidate_pos - pos);
                    pos = candidate_pos;
                    if !self.gate.is_enabled() {
                        // The gate has closed; finish the current call without skipping.
                        // Subsequent calls take the `FILTERED = false` variant.
                        prefilter = None;
                    }
                }
            }
            let Some(&c) = haystack.get(pos) else {
                break;
            };
            // SAFETY: `state_id` remains < self.pma.leftmost_states.len() for automata built by
            // the builder or validated by `DoubleArrayAhoCorasick::deserialize()`.
            state_id = unsafe { self.pma.next_state_id_leftmost_unchecked(state_id, c) };
            if state_id == ROOT_STATE_IDX {
                if let Some(output_pos) = last_output_pos {
                    let end = self.pos;
                    if last_output_pos == self.init_output_pos {
                        self.pos += 1;
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
            } else if let Some(output_pos) =
                unsafe { self.pma.leftmost_output_pos_unchecked(state_id) }
            {
                last_output_pos.replace(output_pos);
                self.pos = pos + 1;
            }
            pos += 1;
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
}

impl<P, V> Iterator for LeftmostFindIterator<'_, P, V>
where
    P: AsRef<[u8]>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        // Re-checked on every call: once the gate closes, all subsequent calls take the
        // prefilter-free variant.
        if self.pma.prefilter.is_some() && self.gate.is_enabled() {
            self.next_impl::<true>()
        } else {
            self.next_impl::<false>()
        }
    }
}

/// Stepper created by [`DoubleArrayAhoCorasick::find_stepper()`].
pub struct FindStepper<'a, V> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
    pub(crate) output_pos: Option<NonZeroU32>,
}

impl<V> FindStepper<'_, V>
where
    V: Copy,
{
    /// Consumes one byte and transitions the state.
    #[inline(always)]
    pub fn consume(&mut self, c: u8) {
        self.pos += 1;
        // state_id is always smaller than self.pma.states.len() because
        // self.pma.next_state_id_unchecked() ensures to return such a value.
        // This stepper is created only for standard matching, as required by
        // root_output_value().
        unsafe {
            if self.pma.root_output_value().is_some() {
                return;
            }
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
            // output_pos is always smaller than self.pma.outputs.len() because
            // State::output_pos() ensures to return such a value when it is Some.
            let out = self
                .pma
                .outputs
                .get_unchecked(usize::from_u32(output_pos.get() - 1));
            out.to_match(self.pos)
        })
    }
}

/// Iterator created by [`FindOverlappingStepper::matches()`].
pub struct FindOverlappingStepperIterator<'a, V> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
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

/// Stepper created by [`DoubleArrayAhoCorasick::find_overlapping_stepper()`].
pub struct FindOverlappingStepper<'a, V> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
}

impl<'a, V> FindOverlappingStepper<'a, V>
where
    V: Copy,
{
    /// Consumes one byte and transitions the state.
    #[inline(always)]
    pub fn consume(&mut self, c: u8) {
        // self.state_id is always smaller than self.pma.states.len() because
        // self.pma.next_state_id_unchecked() ensures to return such a value.
        self.state_id = unsafe { self.pma.next_state_id_unchecked(self.state_id, c) };
        self.pos += 1;
    }

    /// Returns an iterator that yields matches at the current position.
    #[must_use]
    #[inline(always)]
    pub fn matches(&self) -> FindOverlappingStepperIterator<'a, V> {
        let output_pos = unsafe {
            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.next_state_id_unchecked() ensures to return such a value.
            self.pma
                .states
                .get_unchecked(usize::from_u32(self.state_id))
                .output_pos()
        };
        FindOverlappingStepperIterator {
            pma: self.pma,
            pos: self.pos,
            output_pos,
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::*;

    #[test]
    fn test_overlapping_no_suffix_iter() {
        let pma = DoubleArrayAhoCorasick::<u32>::new(["a", "ab", ""]).unwrap();
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
    fn test_overlapping_stepper_lifetime() {
        let pma = DoubleArrayAhoCorasick::new(["a", "ab"]).unwrap();
        let mut stepper = pma.find_overlapping_stepper();
        stepper.consume(b'a');
        let mut it1 = stepper.matches();
        stepper.consume(b'b');
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
