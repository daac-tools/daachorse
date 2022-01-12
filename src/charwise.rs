pub mod iter;
pub mod mapper;

// The maximum BASE value used as an invalid value.
pub(crate) const BASE_INVALID: i32 = std::i32::MAX;
// The maximum output position value used as an invalid value.
pub(crate) const OUTPUT_POS_INVALID: u32 = std::u32::MAX;
// The root index position.
pub(crate) const ROOT_STATE_IDX: u32 = 0;
// The dead index position.
pub(crate) const DEAD_STATE_IDX: u32 = 1;

use crate::{MatchKind, Output};

pub use crate::charwise::iter::{
    FindIterator, FindOverlappingIterator, FindOverlappingNoSuffixIterator,
};
pub use crate::charwise::mapper::Mapper;

/// Fast multiple pattern match automaton implemented
/// with the Aho-Corasick algorithm and character-wise double-array data structure.
///
/// # Build instructions
///
/// [`CharwiseDoubleArrayAhoCorasick`] supports the following two types of input data:
///
/// - [`CharwiseDoubleArrayAhoCorasick::new`] builds an automaton from a set of UTF-8 strings
///    while assigning unique identifiers in the input order.
///
/// - [`CharwiseDoubleArrayAhoCorasick::with_values`] builds an automaton
///    from a set of pairs of a UTF-8 string and a `u32` value.
#[derive(Clone, Default)]
pub struct CharwiseDoubleArrayAhoCorasick<M> {
    states: Vec<State>,
    outputs: Vec<Output>,
    mapper: M,
    match_kind: MatchKind,
    num_states: usize,
}

impl<M> CharwiseDoubleArrayAhoCorasick<M>
where
    M: Mapper,
{
    /// Returns an iterator of non-overlapping matches in the given haystack.
    ///
    /// # Arguments
    ///
    /// * `haystack` - String to search for.
    ///
    /// # Panics
    ///
    /// When you specify `MatchKind::{LeftmostFirst,LeftmostLongest}` in the construction,
    /// the iterator is not supported and the function will call panic!.
    pub fn find_iter<P>(&self, haystack: P) -> FindIterator<M, P>
    where
        P: AsRef<str>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindIterator {
            pma: self,
            haystack,
            pos: 0,
        }
    }

    /// Returns an iterator of overlapping matches in the given haystack.
    ///
    /// # Arguments
    ///
    /// * `haystack` - String to search for.
    ///
    /// # Panics
    ///
    /// When you specify `MatchKind::{LeftmostFirst,LeftmostLongest}` in the construction,
    /// the iterator is not supported and the function will call panic!.
    pub fn find_overlapping_iter<P>(&self, haystack: P) -> FindOverlappingIterator<M, P>
    where
        P: AsRef<str>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindOverlappingIterator {
            pma: self,
            haystack,
            state_id: ROOT_STATE_IDX,
            pos: 0,
            output_pos: 0,
        }
    }

    /// Returns an iterator of overlapping matches without suffixes in the given haystack.
    ///
    /// The Aho-Corasick algorithm reads through the haystack from left to right and reports
    /// matches when it reaches the end of each pattern. In the overlapping match, more than one
    /// pattern can be returned per report.
    ///
    /// This iterator returns the first match on each report.
    ///
    /// # Arguments
    ///
    /// * `haystack` - String to search for.
    ///
    /// # Panics
    ///
    /// When you specify `MatchKind::{LeftmostFirst,LeftmostLongest}` in the construction,
    /// the iterator is not supported and the function will call panic!.
    pub fn find_overlapping_no_suffix_iter<P>(
        &self,
        haystack: P,
    ) -> FindOverlappingNoSuffixIterator<M, P>
    where
        P: AsRef<str>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindOverlappingNoSuffixIterator {
            pma: self,
            haystack,
            state_id: ROOT_STATE_IDX,
            pos: 0,
        }
    }

    /// Returns the total number of states this automaton has.
    pub fn num_states(&self) -> usize {
        self.num_states
    }

    /// Returns the total number of elements of the double array.
    pub fn num_elements(&self) -> usize {
        self.states.len()
    }

    /// Returns the total amount of heap used by this automaton in bytes.
    pub fn heap_bytes(&self) -> usize {
        self.states.len() * std::mem::size_of::<State>()
            + self.outputs.len() * std::mem::size_of::<Output>()
            + self.mapper.heap_bytes()
    }

    #[inline(always)]
    fn get_child_index(&self, state_id: u32, mapped_c: u32) -> Option<u32> {
        if let Some(base) = self.states[state_id as usize].base() {
            let child_idx = base + mapped_c as i32;
            if child_idx < 0 {
                return None;
            }
            if let Some(child) = self.states.get(child_idx as usize) {
                if child.check() == state_id {
                    return Some(child_idx as u32);
                }
            }
        }
        None
    }

    #[inline(always)]
    fn get_next_state_id(&self, mut state_id: u32, mapped_c: u32) -> u32 {
        loop {
            if let Some(state_id) = self.get_child_index(state_id, mapped_c) {
                return state_id;
            }
            if state_id == ROOT_STATE_IDX {
                return ROOT_STATE_IDX;
            }
            state_id = self.states[state_id as usize].fail();
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct State {
    base: i32,
    check: u32,
    fail: u32,
    output_pos: u32,
}

impl Default for State {
    fn default() -> Self {
        Self {
            base: BASE_INVALID,
            check: DEAD_STATE_IDX,
            fail: DEAD_STATE_IDX,
            output_pos: OUTPUT_POS_INVALID,
        }
    }
}

impl State {
    #[inline(always)]
    pub fn base(&self) -> Option<i32> {
        Some(self.base).filter(|&x| x != BASE_INVALID)
    }

    #[inline(always)]
    pub const fn check(&self) -> u32 {
        self.check
    }

    #[inline(always)]
    pub const fn fail(&self) -> u32 {
        self.fail
    }

    #[inline(always)]
    pub fn output_pos(&self) -> Option<u32> {
        Some(self.output_pos).filter(|&x| x != OUTPUT_POS_INVALID)
    }

    #[inline(always)]
    #[allow(dead_code)]
    pub fn set_base(&mut self, x: i32) {
        self.base = x;
    }

    #[inline(always)]
    #[allow(dead_code)]
    pub fn set_check(&mut self, x: u32) {
        self.check = x;
    }

    #[inline(always)]
    #[allow(dead_code)]
    pub fn set_fail(&mut self, x: u32) {
        self.fail = x;
    }

    #[inline(always)]
    #[allow(dead_code)]
    pub fn set_output_pos(&mut self, x: u32) {
        self.output_pos = x;
    }
}
