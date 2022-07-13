//! A byte-wise version of the Double-Array Aho-Corasick.

mod builder;
pub mod iter;

use core::mem;
use core::num::NonZeroU32;

use alloc::vec::Vec;

use crate::build_helper::BuildHelper;
use crate::errors::{DaachorseError, Result};
use crate::intpack::{U24nU8, U24};
use crate::serializer::{Serializable, SerializableVec};
use crate::utils::FromU32;
use crate::{MatchKind, Output};
pub use builder::DoubleArrayAhoCorasickBuilder;
use iter::{
    FindIterator, FindOverlappingIterator, FindOverlappingNoSuffixIterator, LestmostFindIterator,
    U8SliceIterator,
};

// The root index position.
const ROOT_STATE_IDX: u32 = 0;
// The dead index position.
const DEAD_STATE_IDX: u32 = 1;

/// A fast multiple pattern match automaton implemented with the Aho-Corasick algorithm and compact
/// double-array data structure.
///
/// [`DoubleArrayAhoCorasick`] implements a pattern match automaton based on the
/// [Aho-Corasick algorithm](https://dl.acm.org/doi/10.1145/360825.360855), supporting linear-time
/// pattern matching. The internal data structure employs the
/// [compact double-array structure](https://doi.org/10.1016/j.ipm.2006.04.004), the fastest
/// trie representation technique. It supports constant-time state-to-state traversal, allowing for
/// very fast pattern matching. Moreover, each state is represented in the space of only 12 bytes.
///
/// # Build instructions
///
/// [`DoubleArrayAhoCorasick`] supports the following two types of input data:
///
/// - [`DoubleArrayAhoCorasick::new`] builds an automaton from a set of byte strings while
///   assigning unique identifiers in the input order.
///
/// - [`DoubleArrayAhoCorasick::with_values`] builds an automaton from a set of pairs of a byte
///   string and a user-defined value.
///
/// # Limitations
///
/// The maximum number of patterns is limited to 2^24-1. If a larger number of patterns is given,
/// [`DaachorseError`](super::errors::DaachorseError) will be reported.
#[derive(Clone, Eq, Hash, PartialEq)]
pub struct DoubleArrayAhoCorasick<V> {
    states: Vec<State>,
    outputs: Vec<Output<V>>,
    match_kind: MatchKind,
    num_states: u32,
}

impl<V> DoubleArrayAhoCorasick<V> {
    /// Creates a new [`DoubleArrayAhoCorasick`] from input patterns. The value `i` is
    /// automatically associated with `patterns[i]`.
    ///
    /// # Arguments
    ///
    /// * `patterns` - List of patterns.
    ///
    /// # Errors
    ///
    /// [`DaachorseError`](super::errors::DaachorseError) is returned when
    ///   - `patterns` is empty,
    ///   - `patterns` contains entries of length zero,
    ///   - `patterns` contains duplicate entries,
    ///   - the conversion from the index `i` to the specified type `V` fails,
    ///   - the scale of `patterns` exceeds the expected one, or
    ///   - the scale of the resulting automaton exceeds the expected one.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut it = pma.find_iter("abcd");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 1, 2), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn new<I, P>(patterns: I) -> Result<Self>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<[u8]>,
        V: Copy + TryFrom<usize>,
    {
        DoubleArrayAhoCorasickBuilder::new().build(patterns)
    }

    /// Creates a new [`DoubleArrayAhoCorasick`] from input pattern-value pairs.
    ///
    /// # Arguments
    ///
    /// * `patvals` - List of pattern-value pairs.
    ///
    /// # Errors
    ///
    /// [`DaachorseError`](super::errors::DaachorseError) is returned when
    ///   - `patvals` is empty,
    ///   - `patvals` contains patterns of length zero,
    ///   - `patvals` contains duplicate patterns,
    ///   - the scale of `patvals` exceeds the expected one, or
    ///   - the scale of the resulting automaton exceeds the expected one.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patvals = vec![("bcd", 0), ("ab", 1), ("a", 2), ("e", 1)];
    /// let pma = DoubleArrayAhoCorasick::with_values(patvals).unwrap();
    ///
    /// let mut it = pma.find_iter("abcde");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 1, 2), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((4, 5, 1), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn with_values<I, P>(patvals: I) -> Result<Self>
    where
        I: IntoIterator<Item = (P, V)>,
        P: AsRef<[u8]>,
        V: Copy,
    {
        DoubleArrayAhoCorasickBuilder::new().build_with_values(patvals)
    }

    /// Returns an iterator of non-overlapping matches in the given haystack.
    ///
    /// # Arguments
    ///
    /// * `haystack` - String to search for.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] in the construction, the iterator is not
    /// supported and the function will panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut it = pma.find_iter("abcd");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 1, 2), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn find_iter<P>(&self, haystack: P) -> FindIterator<U8SliceIterator<P>, V>
    where
        P: AsRef<[u8]>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindIterator {
            pma: self,
            haystack: U8SliceIterator::new(haystack).enumerate(),
        }
    }

    /// Returns an iterator of non-overlapping matches in the given haystack iterator.
    ///
    /// # Arguments
    ///
    /// * `haystack` - [`u8`] iterator to search for.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] in the construction, the iterator is not
    /// supported and the function will panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let haystack = "ab".as_bytes().iter().chain("cd".as_bytes()).copied();
    ///
    /// let mut it = pma.find_iter_from_iter(haystack);
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 1, 2), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn find_iter_from_iter<P>(&self, haystack: P) -> FindIterator<P, V>
    where
        P: Iterator<Item = u8>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindIterator {
            pma: self,
            haystack: haystack.enumerate(),
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
    /// If you do not specify [`MatchKind::Standard`] in the construction, the iterator is not
    /// supported and the function will panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut it = pma.find_overlapping_iter("abcd");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 1, 2), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 2, 1), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn find_overlapping_iter<P>(
        &self,
        haystack: P,
    ) -> FindOverlappingIterator<U8SliceIterator<P>, V>
    where
        P: AsRef<[u8]>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindOverlappingIterator {
            pma: self,
            haystack: U8SliceIterator::new(haystack).enumerate(),
            state_id: ROOT_STATE_IDX,
            output_pos: None,
            pos: 0,
        }
    }

    /// Returns an iterator of overlapping matches in the given haystack iterator.
    ///
    /// # Arguments
    ///
    /// * `haystack` - [`u8`] iterator to search for.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] in the construction, the iterator is not
    /// supported and the function will panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let haystack = "ab".as_bytes().iter().chain("cd".as_bytes()).copied();
    ///
    /// let mut it = pma.find_overlapping_iter_from_iter(haystack);
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 1, 2), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 2, 1), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn find_overlapping_iter_from_iter<P>(&self, haystack: P) -> FindOverlappingIterator<P, V>
    where
        P: Iterator<Item = u8>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindOverlappingIterator {
            pma: self,
            haystack: haystack.enumerate(),
            state_id: ROOT_STATE_IDX,
            output_pos: None,
            pos: 0,
        }
    }

    /// Returns an iterator of overlapping matches without suffixes in the given haystack iterator.
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
    /// If you do not specify [`MatchKind::Standard`] in the construction, the iterator is not
    /// supported and the function will panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "cd", "abc"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut it = pma.find_overlapping_no_suffix_iter("abcd");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 3, 2), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn find_overlapping_no_suffix_iter<P>(
        &self,
        haystack: P,
    ) -> FindOverlappingNoSuffixIterator<U8SliceIterator<P>, V>
    where
        P: AsRef<[u8]>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindOverlappingNoSuffixIterator {
            pma: self,
            haystack: U8SliceIterator::new(haystack).enumerate(),
            state_id: ROOT_STATE_IDX,
        }
    }

    /// Returns an iterator of overlapping matches without suffixes in the given haystack iterator.
    ///
    /// The Aho-Corasick algorithm reads through the haystack from left to right and reports
    /// matches when it reaches the end of each pattern. In the overlapping match, more than one
    /// pattern can be returned per report.
    ///
    /// This iterator returns the first match on each report.
    ///
    /// # Arguments
    ///
    /// * `haystack` - [`u8`] to search for.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] in the construction, the iterator is not
    /// supported and the function will panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "cd", "abc"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let haystack = "ab".as_bytes().iter().chain("cd".as_bytes()).copied();
    ///
    /// let mut it = pma.find_overlapping_no_suffix_iter_from_iter(haystack);
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 3, 2), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn find_overlapping_no_suffix_iter_from_iter<P>(
        &self,
        haystack: P,
    ) -> FindOverlappingNoSuffixIterator<P, V>
    where
        P: Iterator<Item = u8>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindOverlappingNoSuffixIterator {
            pma: self,
            haystack: haystack.enumerate(),
            state_id: ROOT_STATE_IDX,
        }
    }

    /// Returns an iterator of leftmost matches in the given haystack.
    ///
    /// The leftmost match greedily searches the longest possible match at each iteration, and
    /// the match results do not overlap positionally such as
    /// [`DoubleArrayAhoCorasick::find_iter()`].
    ///
    /// According to the [`MatchKind`] option you specified in the construction, the behavior is
    /// changed for multiple possible matches, as follows.
    ///
    ///  - If you set [`MatchKind::LeftmostLongest`], it reports the match
    ///    corresponding to the longest pattern.
    ///
    ///  - If you set [`MatchKind::LeftmostFirst`], it reports the match
    ///    corresponding to the pattern earlier registered to the automaton.
    ///
    /// # Arguments
    ///
    /// * `haystack` - String to search for.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::LeftmostFirst`] or [`MatchKind::LeftmostLongest`] in
    /// the construction, the iterator is not supported and the function will panic.
    ///
    /// # Examples
    ///
    /// ## LeftmostLongest
    ///
    /// ```
    /// use daachorse::{DoubleArrayAhoCorasickBuilder, MatchKind};
    ///
    /// let patterns = vec!["ab", "a", "abcd"];
    /// let pma = DoubleArrayAhoCorasickBuilder::new()
    ///     .match_kind(MatchKind::LeftmostLongest)
    ///     .build(&patterns)
    ///     .unwrap();
    ///
    /// let mut it = pma.leftmost_find_iter("abcd");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 4, 2), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    ///
    /// ## LeftmostFirst
    ///
    /// ```
    /// use daachorse::{DoubleArrayAhoCorasickBuilder, MatchKind};
    ///
    /// let patterns = vec!["ab", "a", "abcd"];
    /// let pma = DoubleArrayAhoCorasickBuilder::new()
    ///     .match_kind(MatchKind::LeftmostFirst)
    ///     .build(&patterns)
    ///     .unwrap();
    ///
    /// let mut it = pma.leftmost_find_iter("abcd");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 2, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn leftmost_find_iter<P>(&self, haystack: P) -> LestmostFindIterator<P, V>
    where
        P: AsRef<[u8]>,
    {
        assert!(
            self.match_kind.is_leftmost(),
            "Error: match_kind must be leftmost."
        );
        LestmostFindIterator {
            pma: self,
            haystack,
            pos: 0,
        }
    }

    /// Returns the total amount of heap used by this automaton in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
    ///
    /// assert_eq!(3108, pma.heap_bytes());
    /// ```
    #[must_use]
    pub fn heap_bytes(&self) -> usize {
        self.states.len() * mem::size_of::<State>()
            + self.outputs.len() * mem::size_of::<Output<V>>()
    }

    /// Returns the total number of states this automaton has.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::<usize>::new(patterns).unwrap();
    ///
    /// assert_eq!(pma.num_states(), 6);
    /// ```
    #[must_use]
    pub fn num_states(&self) -> usize {
        usize::from_u32(self.num_states)
    }

    /// Serializes the automaton into a [`Vec`].
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
    /// let bytes = pma.serialize();
    /// ```
    #[must_use]
    pub fn serialize(&self) -> Vec<u8>
    where
        V: Serializable,
    {
        let mut result = Vec::with_capacity(
            self.states.serialized_bytes()
                + self.outputs.serialized_bytes()
                + MatchKind::serialized_bytes()
                + u32::serialized_bytes(),
        );
        self.states.serialize_to_vec(&mut result);
        self.outputs.serialize_to_vec(&mut result);
        self.match_kind.serialize_to_vec(&mut result);
        self.num_states.serialize_to_vec(&mut result);
        result
    }

    /// Deserializes the automaton from a given slice.
    ///
    /// # Arguments
    ///
    /// * `source` - A source slice.
    ///
    /// # Returns
    ///
    /// A tuple of the automaton and the slice not used for the deserialization.
    ///
    /// # Safety
    ///
    /// The given data must be a correct automaton exported by
    /// [`DoubleArrayAhoCorasick::serialize()`] function.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
    /// let bytes = pma.serialize();
    ///
    /// let (pma, _) = unsafe { DoubleArrayAhoCorasick::<u32>::deserialize_unchecked(&bytes) };
    ///
    /// let mut it = pma.find_overlapping_iter("abcd");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 1, 2), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 2, 1), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    #[must_use]
    pub unsafe fn deserialize_unchecked(source: &[u8]) -> (Self, &[u8])
    where
        V: Serializable,
    {
        let (states, source) = Vec::<State>::deserialize_from_slice(source);
        let (outputs, source) = Vec::<Output<V>>::deserialize_from_slice(source);
        let (match_kind, source) = MatchKind::deserialize_from_slice(source);
        let (num_states, source) = u32::deserialize_from_slice(source);
        (
            Self {
                states,
                outputs,
                match_kind,
                num_states,
            },
            source,
        )
    }

    /// # Safety
    ///
    /// `state_id` must be smaller than the length of states.
    #[inline(always)]
    unsafe fn child_index_unchecked(&self, state_id: u32, c: u8) -> Option<u32> {
        // child_idx is always smaller than states.len() because
        //  - states.len() is 256 * k for some integer k, and
        //  - base() returns smaller than states.len() when it is Some.
        self.states
            .get_unchecked(usize::from_u32(state_id))
            .base()
            .and_then(|base| {
                let child_idx = base.get() ^ u32::from(c);
                Some(child_idx)
                    .filter(|&x| self.states.get_unchecked(usize::from_u32(x)).check() == c)
            })
    }

    /// # Safety
    ///
    /// `state_id` must be smaller than the length of states.
    #[inline(always)]
    unsafe fn next_state_id_unchecked(&self, mut state_id: u32, c: u8) -> u32 {
        // In the loop, state_id is always set to values smaller than states.len(),
        // because child_index_unchecked() and fail() return such values.
        loop {
            if let Some(state_id) = self.child_index_unchecked(state_id, c) {
                return state_id;
            }
            if state_id == ROOT_STATE_IDX {
                return ROOT_STATE_IDX;
            }
            state_id = self.states.get_unchecked(usize::from_u32(state_id)).fail();
        }
    }

    /// # Safety
    ///
    /// `state_id` must be smaller than the length of states.
    #[inline(always)]
    unsafe fn next_state_id_leftmost_unchecked(&self, mut state_id: u32, c: u8) -> u32 {
        // In the loop, state_id is always set to values smaller than states.len(),
        // because child_index_unchecked() and fail() return such values.
        loop {
            if let Some(state_id) = self.child_index_unchecked(state_id, c) {
                return state_id;
            }
            if state_id == ROOT_STATE_IDX {
                return ROOT_STATE_IDX;
            }
            let fail_id = self.states.get_unchecked(usize::from_u32(state_id)).fail();
            if fail_id == DEAD_STATE_IDX {
                return ROOT_STATE_IDX;
            }
            state_id = fail_id;
        }
    }
}

#[derive(Clone, Copy, Default, Eq, Hash, PartialEq)]
struct State {
    base: Option<NonZeroU32>,
    fail: u32,
    // 3 bytes for output_pos and 1 byte for check.
    opos_ch: U24nU8,
}

impl State {
    #[inline(always)]
    pub const fn base(&self) -> Option<NonZeroU32> {
        self.base
    }

    #[inline(always)]
    pub fn check(&self) -> u8 {
        self.opos_ch.b()
    }

    #[inline(always)]
    pub const fn fail(&self) -> u32 {
        self.fail
    }

    #[inline(always)]
    pub const fn output_pos(&self) -> Option<NonZeroU32> {
        NonZeroU32::new(self.opos_ch.a().get())
    }

    #[inline(always)]
    pub fn set_base(&mut self, x: NonZeroU32) {
        self.base = Some(x);
    }

    #[inline(always)]
    pub fn set_check(&mut self, x: u8) {
        self.opos_ch.set_b(x);
    }

    #[inline(always)]
    pub fn set_fail(&mut self, x: u32) {
        self.fail = x;
    }

    #[inline(always)]
    pub fn set_output_pos(&mut self, x: Option<NonZeroU32>) -> Result<()> {
        let x = x.map_or(0, NonZeroU32::get);
        if let Ok(x) = U24::try_from(x) {
            self.opos_ch.set_a(x);
            Ok(())
        } else {
            Err(DaachorseError::automaton_scale("output_pos", U24::MAX))
        }
    }
}

impl Serializable for State {
    #[inline(always)]
    fn serialize_to_vec(&self, dst: &mut Vec<u8>) {
        self.base.serialize_to_vec(dst);
        self.fail.serialize_to_vec(dst);
        self.opos_ch.serialize_to_vec(dst);
    }

    #[inline(always)]
    fn deserialize_from_slice(src: &[u8]) -> (Self, &[u8]) {
        let (base, src) = Option::<NonZeroU32>::deserialize_from_slice(src);
        let (fail, src) = u32::deserialize_from_slice(src);
        let (opos_ch, src) = U24nU8::deserialize_from_slice(src);
        (
            Self {
                base,
                fail,
                opos_ch,
            },
            src,
        )
    }

    #[inline(always)]
    fn serialized_bytes() -> usize {
        Option::<NonZeroU32>::serialized_bytes()
            + u32::serialized_bytes()
            + U24nU8::serialized_bytes()
    }
}

impl core::fmt::Debug for State {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("State")
            .field("base", &self.base())
            .field("check", &self.check())
            .field("fail", &self.fail())
            .field("output_pos", &self.output_pos())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_double_array() {
        /*
         *          a--> 4
         *         /
         *   a--> 1 --c--> 5
         *  /
         * 0 --b--> 2 --c--> 6
         *  \
         *   c--> 3
         *
         *   a = 0
         *   b = 1
         *   c = 2
         */
        let patterns = vec![vec![0, 0], vec![0, 2], vec![1, 2], vec![2]];
        let pma = DoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();

        let base_expected = vec![
            NonZeroU32::new(4), // 0  (state=0)
            None,               // 1  (reserved)
            None,               // 2
            None,               // 3  (state=6)
            NonZeroU32::new(8), // 4  (state=1)
            NonZeroU32::new(1), // 5  (state=2)
            None,               // 6  (state=3)
            None,               // 7
            None,               // 8  (state=4)
            None,               // 9
            None,               // 10 (state=5)
        ];
        let check_expected = vec![
            0, // 0  (state=0)
            1, // 1
            2, // 2
            2, // 3  (state=6)
            0, // 4  (state=1)
            1, // 5  (state=2)
            2, // 6  (state=3)
            7, // 7
            0, // 8  (state=4)
            9, // 9
            2, // 10 (state=5)
        ];
        let fail_expected = vec![
            ROOT_STATE_IDX, // 0  (state=0)
            ROOT_STATE_IDX, // 1  (reserved)
            ROOT_STATE_IDX, // 2
            6,              // 3  (state=6)
            ROOT_STATE_IDX, // 4  (state=1)
            ROOT_STATE_IDX, // 5  (state=2)
            ROOT_STATE_IDX, // 6  (state=3)
            ROOT_STATE_IDX, // 7
            4,              // 8  (state=4)
            ROOT_STATE_IDX, // 9
            6,              // 10 (state=5)
        ];

        let pma_base: Vec<_> = pma.states[0..11].iter().map(|state| state.base()).collect();
        let pma_check: Vec<_> = pma.states[0..11]
            .iter()
            .map(|state| state.check())
            .collect();
        let pma_fail: Vec<_> = pma.states[0..11].iter().map(|state| state.fail()).collect();

        assert_eq!(base_expected, pma_base);
        assert_eq!(check_expected, pma_check);
        assert_eq!(fail_expected, pma_fail);
    }

    #[test]
    fn test_num_states() {
        /*
         *   b-*-a-*-a-*-b-*-a-*
         *  /
         * *-a-*-b-*-b-*-a-*
         *          \
         *           a-*-b-*-a-*
         */
        let patterns = vec!["abba", "baaba", "ababa"];
        let pma = DoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();

        assert_eq!(13, pma.num_states());
    }

    #[test]
    fn test_input_order() {
        let patvals_sorted = vec![("ababa", 0), ("abba", 1), ("baaba", 2)];
        let patvals_unsorted = vec![("abba", 1), ("baaba", 2), ("ababa", 0)];

        let pma_sorted = DoubleArrayAhoCorasick::with_values(patvals_sorted).unwrap();
        let pma_unsorted = DoubleArrayAhoCorasick::with_values(patvals_unsorted).unwrap();

        assert_eq!(pma_sorted.states, pma_unsorted.states);
        assert_eq!(pma_sorted.outputs, pma_unsorted.outputs);
    }

    #[test]
    fn test_n_blocks_1_1() {
        let mut patterns = vec![];
        // state 0: reserved for the root state
        // state 1: reserved for the dead state
        // base = 0xfe; fills 0x02..=0xff
        for i in 0x00..=0xfd {
            let pattern = vec![i];
            patterns.push(pattern);
        }
        let pma = DoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
        assert_eq!(255, pma.num_states());
        assert_eq!(256, pma.states.len());
        assert_eq!(0xfe, pma.states[0].base().unwrap().get());
    }

    #[test]
    fn test_n_blocks_1_2() {
        let mut patterns = vec![];
        // state 0: reserved for the root state
        // state 1: reserved for the dead state
        // base = 0x100; fills 0x100, 0x102, 0x104..=0x1ff
        patterns.push(vec![0x00]);
        patterns.push(vec![0x02]);
        for i in 0x04..=0xff {
            patterns.push(vec![i]);
        }
        let pma = DoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
        assert_eq!(255, pma.num_states());
        assert_eq!(512, pma.states.len());
        assert_eq!(0x100, pma.states[0].base().unwrap().get());
    }

    #[test]
    fn test_n_blocks_2_1() {
        let mut patterns = vec![];
        // state 0: reserved for the root state
        // state 1: reserved for the dead state
        // base = 0x80; fills 0x80..=0xff
        for i in 0x00..=0x7f {
            let pattern = vec![i];
            patterns.push(pattern);
        }
        // base = 0x7e; fills 0x02..=0x7f
        for i in 0x00..=0x7d {
            let pattern = vec![0x00, i];
            patterns.push(pattern);
        }
        let pma = DoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
        assert_eq!(255, pma.num_states());
        assert_eq!(256, pma.states.len());
        assert_eq!(0x80, pma.states[0].base().unwrap().get());
        assert_eq!(0x7e, pma.states[0x80].base().unwrap().get());
    }

    #[test]
    fn test_n_blocks_2_2() {
        let mut patterns = vec![];
        // state 0: reserved for the root state
        // state 1: reserved for the dead state
        // base = 0x80; fills 0x80..=0xff
        for i in 0..=0x7f {
            let pattern = vec![i];
            patterns.push(pattern);
        }
        // base = 0x100; fills 0x100, 0x102, 0x104..=0x17f
        patterns.push(vec![0, 0x00]);
        patterns.push(vec![0, 0x02]);
        for i in 0x04..=0x7f {
            let pattern = vec![0x00, i];
            patterns.push(pattern);
        }
        let pma = DoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
        assert_eq!(255, pma.num_states());
        assert_eq!(512, pma.states.len());
        assert_eq!(0x80, pma.states[0].base().unwrap().get());
        assert_eq!(0x100, pma.states[0x80].base().unwrap().get());
    }

    #[test]
    fn test_serialize_state() {
        let mut opos_ch = U24nU8::default();
        opos_ch.set_a(U24::try_from(57).unwrap());
        opos_ch.set_b(77);
        let x = State {
            base: NonZeroU32::new(42),
            fail: 13,
            opos_ch,
        };
        let mut data = vec![];
        x.serialize_to_vec(&mut data);
        assert_eq!(data.len(), State::serialized_bytes());
        let (y, rest) = State::deserialize_from_slice(&data);
        assert!(rest.is_empty());
        assert_eq!(x, y);
    }

    #[test]
    fn test_serialize_pma() {
        let patterns = vec!["abba", "baaba", "ababa"];
        let pma = DoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
        let bytes = pma.serialize();
        let (other, rest) = unsafe { DoubleArrayAhoCorasick::deserialize_unchecked(&bytes) };
        assert!(rest.is_empty());
        assert_eq!(pma.states, other.states);
        assert_eq!(pma.outputs, other.outputs);
        assert_eq!(pma.match_kind, other.match_kind);
        assert_eq!(pma.num_states, other.num_states);
    }
}
