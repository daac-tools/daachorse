//! Iterators for [`DoubleArrayAhoCorasick`].

use core::iter::Enumerate;
use core::num::NonZeroU32;

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
        unsafe {
            if let Some(output_pos) = self
                .pma
                .states
                .get_unchecked(usize::from_u32(ROOT_STATE_IDX))
                .output_pos()
            {
                let value = self
                    .pma
                    .outputs
                    .get_unchecked(usize::from_u32(output_pos.get() - 1))
                    .value();
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
        }
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
            unsafe {
                if let Some(output_pos) = self
                    .pma
                    .states
                    .get_unchecked(usize::from_u32(ROOT_STATE_IDX))
                    .output_pos()
                {
                    let value = self
                        .pma
                        .outputs
                        .get_unchecked(usize::from_u32(output_pos.get() - 1))
                        .value();
                    return Some(Match {
                        length: 0,
                        end: 0,
                        value,
                    });
                }
            }
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

/// Iterator created by [`DoubleArrayAhoCorasick::leftmost_find_iter()`].
pub struct LeftmostFindIterator<'a, P, V>
where
    P: AsRef<[u8]>,
{
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
    pub(crate) haystack: P,
    pub(crate) pos: usize,
    pub(crate) init_output_pos: Option<NonZeroU32>,
    pub(crate) skip_empty: bool,
}

impl<P, V> Iterator for LeftmostFindIterator<'_, P, V>
where
    P: AsRef<[u8]>,
    V: Copy,
{
    type Item = Match<V>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let mut state_id = ROOT_STATE_IDX;
        let mut last_output_pos = self.init_output_pos;

        let haystack = self.haystack.as_ref();
        'a: loop {
            for (pos, &c) in haystack.iter().enumerate().skip(self.pos) {
                // state_id is always smaller than self.pma.states.len() because
                // self.pma.next_state_id_leftmost_unchecked() ensures to return such a value.
                state_id = unsafe { self.pma.next_state_id_leftmost_unchecked(state_id, c) };
                if state_id == ROOT_STATE_IDX {
                    if let Some(output_pos) = last_output_pos {
                        let end = self.pos;
                        if last_output_pos == self.init_output_pos {
                            self.pos += 1;
                            if self.skip_empty {
                                self.skip_empty = false;
                                continue 'a;
                            }
                        } else {
                            self.skip_empty = true;
                        }
                        // last_output_pos is always smaller than self.pma.outputs.len() because
                        // State::output_pos() ensures to return such a value when it is Some.
                        let out = unsafe {
                            self.pma
                                .outputs
                                .get_unchecked(usize::from_u32(output_pos.get() - 1))
                        };
                        return Some(Match {
                            length: usize::from_u32(out.length()),
                            end,
                            value: out.value(),
                        });
                    }
                } else if let Some(output_pos) = unsafe {
                    self.pma
                        .states
                        .get_unchecked(usize::from_u32(state_id))
                        .output_pos()
                } {
                    last_output_pos.replace(output_pos);
                    self.pos = pos + 1;
                }
            }
            break;
        }

        if self.pos == self.haystack.as_ref().len() {
            self.init_output_pos.take();
        }
        if let Some(output_pos) = last_output_pos {
            // last_output_pos is always smaller than self.pma.outputs.len() because
            // State::output_pos() ensures to return such a value when it is Some.
            let out = unsafe {
                self.pma
                    .outputs
                    .get_unchecked(usize::from_u32(output_pos.get() - 1))
            };
            Some(Match {
                length: usize::from_u32(out.length()),
                end: self.pos,
                value: out.value(),
            })
        } else {
            self.pos = self.haystack.as_ref().len();
            None
        }
    }
}

/// Stepper created by [`DoubleArrayAhoCorasick::find_stepper()`].
pub struct FindStepper<'a, V> {
    pub(crate) pma: &'a DoubleArrayAhoCorasick<V>,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
}

impl<V> FindStepper<'_, V>
where
    V: Copy,
{
    /// Consumes a byte and returns a match if the current state has an output.
    #[inline(always)]
    pub fn consume(&mut self, c: u8) -> Option<Match<V>> {
        self.pos += 1;
        unsafe {
            if let Some(output_pos) = self
                .pma
                .states
                .get_unchecked(usize::from_u32(ROOT_STATE_IDX))
                .output_pos()
            {
                return Some(Match {
                    length: 0,
                    end: self.pos,
                    value: self
                        .pma
                        .outputs
                        .get_unchecked(usize::from_u32(output_pos.get() - 1))
                        .value(),
                });
            }
        }
        // state_id is always smaller than self.pma.states.len() because
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
            self.state_id = ROOT_STATE_IDX;
            return Some(Match {
                length: usize::from_u32(out.length()),
                end: self.pos,
                value: out.value(),
            });
        }
        None
    }
}

/// Iterator created by [`FindOverlappingStepper::consume()`].
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
    /// Consumes a byte and returns an iterator that yields matches.
    #[inline(always)]
    pub fn consume(&mut self, c: u8) -> FindOverlappingStepperIterator<'a, V> {
        // self.state_id is always smaller than self.pma.states.len() because
        // self.pma.next_state_id_unchecked() ensures to return such a value.
        self.state_id = unsafe { self.pma.next_state_id_unchecked(self.state_id, c) };
        let output_pos = unsafe {
            self.pma
                .states
                .get_unchecked(usize::from_u32(self.state_id))
                .output_pos()
        };
        self.pos += 1;
        FindOverlappingStepperIterator {
            pma: self.pma,
            pos: self.pos,
            output_pos,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_overlapping_stepper_lifetime() {
        let pma = DoubleArrayAhoCorasick::new(["a", "ab"]).unwrap();
        let (mut stepper, _) = pma.find_overlapping_stepper();
        let mut it1 = stepper.consume(b'a');
        let mut it2 = stepper.consume(b'b');
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
