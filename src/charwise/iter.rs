use crate::charwise::CharwiseDoubleArrayAhoCorasick;
use crate::Match;
use crate::ROOT_STATE_IDX;

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
            self.state_id = self.pma.get_next_state_id(self.state_id, mapped_c);
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
            state_id = self.pma.get_next_state_id(state_id, mapped_c);
            if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(state_id as usize)
                    .output_pos()
            } {
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
            self.state_id = self.pma.get_next_state_id(self.state_id, mapped_c);
            if let Some(output_pos) = unsafe {
                self.pma
                    .states
                    .get_unchecked(self.state_id as usize)
                    .output_pos()
            } {
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
