use crate::charwise::CharwiseDoubleArrayAhoCorasick;
use crate::Match;
use crate::{DEAD_STATE_IDX, OUTPUT_POS_INVALID, ROOT_STATE_IDX};

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_iter()`].
pub struct FindOverlappingIterator<'a, P> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick,
    pub(crate) haystack: P,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
    pub(crate) output_pos: usize,
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_overlapping_iter()`].
pub struct FindIterator<'a, P> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick,
    pub(crate) haystack: P,
    pub(crate) pos: usize,
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::find_overlapping_no_suffix_iter()`].
pub struct FindOverlappingNoSuffixIterator<'a, P> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick,
    pub(crate) haystack: P,
    pub(crate) state_id: u32,
    pub(crate) pos: usize,
}

/// Iterator created by [`CharwiseDoubleArrayAhoCorasick::leftmost_find_iter()`].
pub struct LestmostFindIterator<'a, P> {
    pub(crate) pma: &'a CharwiseDoubleArrayAhoCorasick,
    pub(crate) haystack: P,
    pub(crate) pos: usize,
}

impl<'a, P> Iterator for FindOverlappingIterator<'a, P>
where
    P: AsRef<str>,
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

        for c in unsafe { self.haystack.as_ref().get_unchecked(self.pos..) }.chars() {
            self.pos += c.len_utf8();
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
                    end: self.pos,
                    value: out.value() as usize,
                });
            }
        }
        None
    }
}

impl<'a, P> Iterator for FindIterator<'a, P>
where
    P: AsRef<str>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let mut state_id = ROOT_STATE_IDX;
        for c in unsafe { self.haystack.as_ref().get_unchecked(self.pos..) }.chars() {
            self.pos += c.len_utf8();
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
                    end: self.pos,
                    value: out.value() as usize,
                });
            }
        }
        None
    }
}

impl<'a, P> Iterator for FindOverlappingNoSuffixIterator<'a, P>
where
    P: AsRef<str>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        for c in unsafe { self.haystack.as_ref().get_unchecked(self.pos..) }.chars() {
            self.pos += c.len_utf8();
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
                    end: self.pos,
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
