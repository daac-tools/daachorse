pub mod builder;
pub mod iter;

pub use crate::charwise::builder::CharwiseDoubleArrayAhoCorasickBuilder;
pub use crate::charwise::iter::{
    FindIterator, FindOverlappingIterator, FindOverlappingNoSuffixIterator,
};
use crate::errors::Result;
use crate::{MatchKind, Output};

// The maximum BASE value used as an invalid value.
pub(crate) const BASE_INVALID: i32 = std::i32::MAX;
// The maximum output position value used as an invalid value.
pub(crate) const OUTPUT_POS_INVALID: u32 = std::u32::MAX;
// The root index position.
pub(crate) const ROOT_STATE_IDX: u32 = 0;
// The dead index position.
pub(crate) const DEAD_STATE_IDX: u32 = 1;

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
#[derive(Clone)]
pub struct CharwiseDoubleArrayAhoCorasick {
    states: Vec<State>,
    outputs: Vec<Output>,
    match_kind: MatchKind,
    num_states: usize,
}

impl CharwiseDoubleArrayAhoCorasick {
    /// Creates a new [`CharwiseDoubleArrayAhoCorasick`] from input patterns.
    /// The value `i` is automatically associated with `patterns[i]`.
    ///
    /// # Arguments
    ///
    /// * `patterns` - List of patterns.
    ///
    /// # Errors
    ///
    /// [`DaachorseError`] is returned when
    ///   - `patterns` is empty,
    ///   - `patterns` contains entries of length zero,
    ///   - `patterns` contains duplicate entries,
    ///   - the scale of `patterns` exceeds the expected one, or
    ///   - the scale of the resulting automaton exceeds the expected one.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut it = pma.find_iter("全世界中に");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((12, 15, 2), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn new<I, P>(patterns: I) -> Result<Self>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<str>,
    {
        CharwiseDoubleArrayAhoCorasickBuilder::new().build(patterns)
    }

    /// Creates a new [`CharwiseDoubleArrayAhoCorasick`] from input pattern-value pairs.
    ///
    /// # Arguments
    ///
    /// * `patvals` - List of pattern-value pairs, in which the value is of type `u32` and less than `u32::MAX`.
    ///
    /// # Errors
    ///
    /// [`DaachorseError`] is returned when
    ///   - `patvals` is empty,
    ///   - `patvals` contains patterns of length zero,
    ///   - `patvals` contains duplicate patterns,
    ///   - `patvals` contains invalid values,
    ///   - the scale of `patvals` exceeds the expected one, or
    ///   - the scale of the resulting automaton exceeds the expected one.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patvals = vec![("全世界", 0), ("世界", 10), ("に", 100)];
    /// let pma = CharwiseDoubleArrayAhoCorasick::with_values(patvals).unwrap();
    ///
    /// let mut it = pma.find_iter("全世界中に");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((12, 15, 100), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn with_values<I, P>(patvals: I) -> Result<Self>
    where
        I: IntoIterator<Item = (P, u32)>,
        P: AsRef<str>,
    {
        CharwiseDoubleArrayAhoCorasickBuilder::new().build_with_values(patvals)
    }

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
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut it = pma.find_iter("全世界中に");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((12, 15, 2), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn find_iter<P>(&self, haystack: P) -> FindIterator<P>
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
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut it = pma.find_overlapping_iter("全世界中に");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((3, 9, 1), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((12, 15, 2), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn find_overlapping_iter<P>(&self, haystack: P) -> FindOverlappingIterator<P>
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
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut it = pma.find_overlapping_no_suffix_iter("全世界中に");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((12, 15, 2), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn find_overlapping_no_suffix_iter<P>(
        &self,
        haystack: P,
    ) -> FindOverlappingNoSuffixIterator<P>
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
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// assert_eq!(pma.num_states(), 6);
    /// ```
    pub const fn num_states(&self) -> usize {
        self.num_states
    }

    /// Returns the total number of elements of the double array.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// assert_eq!(pma.num_elements(), 7);
    /// ```
    pub fn num_elements(&self) -> usize {
        self.states.len()
    }

    /// Returns the total amount of heap used by this automaton in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// assert_eq!(pma.heap_bytes(), 144);
    /// ```
    pub fn heap_bytes(&self) -> usize {
        self.states.len() * std::mem::size_of::<State>()
            + self.outputs.len() * std::mem::size_of::<Output>()
    }

    /// TODO: Make unsafe
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

    /// TODO: Make unsafe
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
