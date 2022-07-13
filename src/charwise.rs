//! A character-wise version for faster matching on multibyte characters.

mod builder;
pub mod iter;
mod mapper;

use core::mem;
use core::num::NonZeroU32;

use alloc::vec::Vec;

use crate::errors::Result;
use crate::serializer::{Serializable, SerializableVec};
use crate::utils::FromU32;
use crate::{MatchKind, Output};
pub use builder::CharwiseDoubleArrayAhoCorasickBuilder;
use iter::{
    CharWithEndOffsetIterator, FindIterator, FindOverlappingIterator,
    FindOverlappingNoSuffixIterator, LestmostFindIterator, StrIterator,
};
use mapper::CodeMapper;

// The root index position.
const ROOT_STATE_IDX: u32 = 0;
// The dead index position.
const DEAD_STATE_IDX: u32 = 1;

/// A fast multiple pattern match automaton implemented with the Aho-Corasick algorithm and
/// character-wise double-array data structure.
///
/// The standard version [`DoubleArrayAhoCorasick`](super::DoubleArrayAhoCorasick) handles strings
/// as UTF-8 sequences and defines transition labels using byte integers. On the other hand, the
/// character-wise version uses Unicode code point values, reducing the number of transitions and
/// faster matching on multibyte characters.
///
/// # Features
///
/// Compared to [`DoubleArrayAhoCorasick`](super::DoubleArrayAhoCorasick),
/// [`CharwiseDoubleArrayAhoCorasick`] has the following features
/// if it is built from multibyte strings such as CJK characters:
///
///  - Faster matching can be expected.
///  - The construction time can be slower.
///  - The memory efficiency depends on input patterns.
///    - If the scale is large, the memory efficiency can be competitive.
///    - If the scale is small, the double array can be sparse and memory inefficiency.
///
/// # Build instructions
///
/// [`CharwiseDoubleArrayAhoCorasick`] supports the following two types of input data:
///
/// - [`CharwiseDoubleArrayAhoCorasick::new`] builds an automaton from a set of UTF-8 strings while
///   assigning unique identifiers in the input order.
///
/// - [`CharwiseDoubleArrayAhoCorasick::with_values`] builds an automaton
///   from a set of pairs of a UTF-8 string and a user-defined value.
#[derive(Clone, Eq, Hash, PartialEq)]
pub struct CharwiseDoubleArrayAhoCorasick<V> {
    states: Vec<State>,
    mapper: CodeMapper,
    outputs: Vec<Output<V>>,
    match_kind: MatchKind,
    num_states: u32,
}

impl<V> CharwiseDoubleArrayAhoCorasick<V> {
    /// Creates a new [`CharwiseDoubleArrayAhoCorasick`] from input patterns. The value `i` is
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
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
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
        V: Copy + TryFrom<usize>,
    {
        CharwiseDoubleArrayAhoCorasickBuilder::new().build(patterns)
    }

    /// Creates a new [`CharwiseDoubleArrayAhoCorasick`] from input pattern-value pairs.
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
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
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
        I: IntoIterator<Item = (P, V)>,
        P: AsRef<str>,
        V: Copy,
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
    /// If you do not specify [`MatchKind::Standard`] in the construction, the iterator is not
    /// supported and the function will panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
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
    pub fn find_iter<P>(&self, haystack: P) -> FindIterator<StrIterator<P>, V>
    where
        P: AsRef<str>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindIterator {
            pma: self,
            haystack: unsafe { CharWithEndOffsetIterator::new(StrIterator::new(haystack)) },
        }
    }

    /// Returns an iterator of non-overlapping matches in the given haystack iterator.
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
    /// # Safety
    ///
    /// `haystack` must represent a valid UTF-8 string.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let haystack = "全世界".as_bytes().iter().chain("中に".as_bytes()).copied();
    ///
    /// let mut it = unsafe { pma.find_iter_from_iter(haystack) };
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((12, 15, 2), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub unsafe fn find_iter_from_iter<P>(&self, haystack: P) -> FindIterator<P, V>
    where
        P: Iterator<Item = u8>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindIterator {
            pma: self,
            haystack: CharWithEndOffsetIterator::new(haystack),
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
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
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
    pub fn find_overlapping_iter<P>(
        &self,
        haystack: P,
    ) -> FindOverlappingIterator<StrIterator<P>, V>
    where
        P: AsRef<str>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindOverlappingIterator {
            pma: self,
            haystack: unsafe { CharWithEndOffsetIterator::new(StrIterator::new(haystack)) },
            state_id: ROOT_STATE_IDX,
            pos: 0,
            output_pos: None,
        }
    }

    /// Returns an iterator of overlapping matches in the given haystack iterator.
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
    /// # Safety
    ///
    /// `haystack` must represent a valid UTF-8 string.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let haystack = "全世界".as_bytes().iter().chain("中に".as_bytes()).copied();
    ///
    /// let mut it = unsafe { pma.find_overlapping_iter_from_iter(haystack) };
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
    pub unsafe fn find_overlapping_iter_from_iter<P>(
        &self,
        haystack: P,
    ) -> FindOverlappingIterator<P, V>
    where
        P: Iterator<Item = u8>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindOverlappingIterator {
            pma: self,
            haystack: CharWithEndOffsetIterator::new(haystack),
            state_id: ROOT_STATE_IDX,
            pos: 0,
            output_pos: None,
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
    /// If you do not specify [`MatchKind::Standard`] in the construction, the iterator is not
    /// supported and the function will call panic!.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
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
    ) -> FindOverlappingNoSuffixIterator<StrIterator<P>, V>
    where
        P: AsRef<str>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindOverlappingNoSuffixIterator {
            pma: self,
            haystack: unsafe { CharWithEndOffsetIterator::new(StrIterator::new(haystack)) },
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
    /// * `haystack` - String to search for.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] in the construction, the iterator is not
    /// supported and the function will panic.
    ///
    /// # Safety
    ///
    /// `haystack` must represent a valid UTF-8 string.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let haystack = "全世界".as_bytes().iter().chain("中に".as_bytes()).copied();
    ///
    /// let mut it = unsafe { pma.find_overlapping_no_suffix_iter_from_iter(haystack) };
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((12, 15, 2), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub unsafe fn find_overlapping_no_suffix_iter_from_iter<P>(
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
            haystack: CharWithEndOffsetIterator::new(haystack),
            state_id: ROOT_STATE_IDX,
        }
    }

    /// Returns an iterator of leftmost matches in the given haystack.
    ///
    /// The leftmost match greedily searches the longest possible match at each iteration, and the
    /// match results do not overlap positionally such as
    /// [`CharwiseDoubleArrayAhoCorasick::find_iter()`].
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
    /// If you do not specify [`MatchKind::LeftmostFirst`] or [`MatchKind::LeftmostLongest`] in the
    /// construction, the iterator is not supported and the function will call panic!.
    ///
    /// # Examples
    ///
    /// ## LeftmostLongest
    ///
    /// ```
    /// use daachorse::{CharwiseDoubleArrayAhoCorasickBuilder, MatchKind};
    ///
    /// let patterns = vec!["世界", "世", "世界中に"];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
    ///     .match_kind(MatchKind::LeftmostLongest)
    ///     .build(&patterns)
    ///     .unwrap();
    ///
    /// let mut it = pma.leftmost_find_iter("世界中に");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 12, 2), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    ///
    /// ## LeftmostFirst
    ///
    /// ```
    /// use daachorse::{CharwiseDoubleArrayAhoCorasickBuilder, MatchKind};
    ///
    /// let patterns = vec!["世界", "世", "世界中に"];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
    ///     .match_kind(MatchKind::LeftmostFirst)
    ///     .build(&patterns)
    ///     .unwrap();
    ///
    /// let mut it = pma.leftmost_find_iter("世界中に");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 6, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn leftmost_find_iter<P>(&self, haystack: P) -> LestmostFindIterator<P, V>
    where
        P: AsRef<str>,
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

    /// Returns the total number of states this automaton has.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::<usize>::new(patterns).unwrap();
    ///
    /// assert_eq!(pma.num_states(), 6);
    /// ```
    #[must_use]
    pub fn num_states(&self) -> usize {
        usize::from_u32(self.num_states)
    }

    /// Returns the total number of elements of the double array.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::<usize>::new(patterns).unwrap();
    ///
    /// assert_eq!(pma.num_elements(), 8);
    /// ```
    #[must_use]
    pub fn num_elements(&self) -> usize {
        self.states.len()
    }

    /// Returns the total amount of heap used by this automaton in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
    ///
    /// assert_eq!(568, pma.heap_bytes());
    /// ```
    #[must_use]
    pub fn heap_bytes(&self) -> usize {
        self.states.len() * mem::size_of::<State>()
            + self.mapper.heap_bytes()
            + self.outputs.len() * mem::size_of::<Output<V>>()
    }

    /// Serializes the automaton into a [`Vec`].
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
    /// let bytes = pma.serialize();
    /// ```
    #[must_use]
    pub fn serialize(&self) -> Vec<u8>
    where
        V: Serializable,
    {
        let mut result = Vec::with_capacity(
            self.states.serialized_bytes()
                + self.mapper.serialized_bytes()
                + self.outputs.serialized_bytes()
                + MatchKind::serialized_bytes()
                + u32::serialized_bytes(),
        );
        self.states.serialize_to_vec(&mut result);
        self.mapper.serialize_to_vec(&mut result);
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
    /// [`CharwiseDoubleArrayAhoCorasick::serialize()`] function.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
    /// let bytes = pma.serialize();
    ///
    /// let (pma, _) = unsafe { CharwiseDoubleArrayAhoCorasick::<u32>::deserialize_unchecked(&bytes) };
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
    #[must_use]
    pub unsafe fn deserialize_unchecked(source: &[u8]) -> (Self, &[u8])
    where
        V: Serializable,
    {
        let (states, source) = Vec::<State>::deserialize_from_slice(source);
        let (mapper, source) = CodeMapper::deserialize_from_slice(source);
        let (outputs, source) = Vec::<Output<V>>::deserialize_from_slice(source);
        let (match_kind, source) = MatchKind::deserialize_from_slice(source);
        let (num_states, source) = u32::deserialize_from_slice(source);
        (
            Self {
                states,
                mapper,
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
    #[allow(clippy::cast_possible_wrap)]
    #[inline(always)]
    unsafe fn child_index_unchecked(&self, state_id: u32, mapped_c: u32) -> Option<u32> {
        let base = self
            .states
            .get_unchecked(usize::from_u32(state_id))
            .base()?;
        // child_idx is always smaller than states.len() because
        //  - states.len() is a multiple of (1 << k),
        //    where k is the number of bits needed to represent mapped_c.
        //  - base() is always smaller than states.len() when it is Some.
        let child_idx = base.get() ^ mapped_c;
        if self
            .states
            .get_unchecked(usize::from_u32(child_idx))
            .check()
            == state_id
        {
            Some(child_idx)
        } else {
            None
        }
    }

    /// # Safety
    ///
    /// `state_id` must be smaller than the length of states.
    #[inline(always)]
    unsafe fn next_state_id_unchecked(&self, mut state_id: u32, c: char) -> u32 {
        if let Some(mapped_c) = self.mapper.get(c) {
            loop {
                if let Some(state_id) = self.child_index_unchecked(state_id, mapped_c) {
                    return state_id;
                }
                if state_id == ROOT_STATE_IDX {
                    return ROOT_STATE_IDX;
                }
                state_id = self.states.get_unchecked(usize::from_u32(state_id)).fail();
            }
        } else {
            ROOT_STATE_IDX
        }
    }

    /// # Safety
    ///
    /// `state_id` must be smaller than the length of states.
    #[inline(always)]
    unsafe fn next_state_id_leftmost_unchecked(&self, mut state_id: u32, c: char) -> u32 {
        if let Some(mapped_c) = self.mapper.get(c) {
            loop {
                if let Some(state_id) = self.child_index_unchecked(state_id, mapped_c) {
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
        } else {
            ROOT_STATE_IDX
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct State {
    base: Option<NonZeroU32>,
    check: u32,
    fail: u32,
    output_pos: Option<NonZeroU32>,
}

impl Default for State {
    fn default() -> Self {
        Self {
            base: None,
            check: DEAD_STATE_IDX,
            fail: DEAD_STATE_IDX,
            output_pos: None,
        }
    }
}

impl State {
    #[inline(always)]
    pub const fn base(&self) -> Option<NonZeroU32> {
        self.base
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
    pub const fn output_pos(&self) -> Option<NonZeroU32> {
        self.output_pos
    }

    #[inline(always)]
    #[allow(dead_code)]
    pub fn set_base(&mut self, x: NonZeroU32) {
        self.base = Some(x);
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
    pub fn set_output_pos(&mut self, x: Option<NonZeroU32>) {
        self.output_pos = x;
    }
}

impl Serializable for State {
    #[inline(always)]
    fn serialize_to_vec(&self, dst: &mut Vec<u8>) {
        self.base.serialize_to_vec(dst);
        self.check.serialize_to_vec(dst);
        self.fail.serialize_to_vec(dst);
        self.output_pos.serialize_to_vec(dst);
    }

    #[inline(always)]
    fn deserialize_from_slice(src: &[u8]) -> (Self, &[u8]) {
        let (base, src) = Option::<NonZeroU32>::deserialize_from_slice(src);
        let (check, src) = u32::deserialize_from_slice(src);
        let (fail, src) = u32::deserialize_from_slice(src);
        let (output_pos, src) = Option::<NonZeroU32>::deserialize_from_slice(src);
        (
            Self {
                base,
                check,
                fail,
                output_pos,
            },
            src,
        )
    }

    #[inline(always)]
    fn serialized_bytes() -> usize {
        Option::<NonZeroU32>::serialized_bytes()
            + u32::serialized_bytes()
            + u32::serialized_bytes()
            + Option::<NonZeroU32>::serialized_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_double_array() {
        /*
         *          Ａ--> 4
         *         /
         *   Ａ--> 1 --Ｃ--> 5
         *  /
         * 0 --Ｂ--> 3 --Ｃ--> 6
         *  \
         *   Ｃ--> 2
         *
         *   Ａ= 0
         *   Ｃ= 1
         *   Ｂ= 2
         */
        let patterns = vec!["ＡＡ", "ＡＣ", "ＢＣ", "Ｃ"];
        let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();

        let base_expected = vec![
            NonZeroU32::new(4), // 0  (state=0)
            None,               // 1  (reserved)
            None,               // 2  (state=6)
            None,               // 3
            NonZeroU32::new(8), // 4  (state=1)
            None,               // 5  (state=2)
            NonZeroU32::new(3), // 6  (state=3)
            None,               // 7
            None,               // 8  (state=4)
            None,               // 9  (state=5)
            None,               // 10
        ];
        let check_expected = vec![
            1, // 0  (state=0)
            1, // 1
            6, // 2  (state=6)
            1, // 3
            0, // 4  (state=1)
            0, // 5  (state=2)
            0, // 6  (state=3)
            1, // 7
            4, // 8  (state=4)
            4, // 9  (state=5)
            1, // 10
        ];
        let fail_expected = vec![
            ROOT_STATE_IDX, // 0  (state=0)
            DEAD_STATE_IDX, // 1  (reserved)
            5,              // 2  (state=6)
            DEAD_STATE_IDX, // 3
            ROOT_STATE_IDX, // 4  (state=1)
            ROOT_STATE_IDX, // 5  (state=2)
            ROOT_STATE_IDX, // 6  (state=3)
            DEAD_STATE_IDX, // 7
            4,              // 8  (state=4)
            5,              // 9  (state=5)
            DEAD_STATE_IDX, // 10
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
        let patterns = vec!["ａｂｂａ", "ｂａａｂａ", "ａｂａｂａ"];
        let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();

        assert_eq!(13, pma.num_states());
    }

    #[test]
    fn test_input_order() {
        let patvals_sorted = vec![("ａｂａｂａ", 0), ("ａｂｂａ", 1), ("ｂａａｂａ", 2)];
        let patvals_unsorted = vec![("ａｂｂａ", 1), ("ｂａａｂａ", 2), ("ａｂａｂａ", 0)];

        let pma_sorted = CharwiseDoubleArrayAhoCorasick::with_values(patvals_sorted).unwrap();
        let pma_unsorted = CharwiseDoubleArrayAhoCorasick::with_values(patvals_unsorted).unwrap();

        assert_eq!(pma_sorted.states, pma_unsorted.states);
        assert_eq!(pma_sorted.outputs, pma_unsorted.outputs);
    }

    #[test]
    fn test_n_blocks_1_1() {
        let mut patterns = vec![];
        // state 0: reserved for the root state
        // state 1: reserved for the dead state
        // base = 0x7e; fills 0x02..=0x7f
        for i in '\u{0}'..='\u{7d}' {
            let pattern: alloc::string::String = core::iter::once(i).collect();
            patterns.push(pattern);
        }
        let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
        assert_eq!(127, pma.num_states());
        assert_eq!(128, pma.states.len());
        assert_eq!(0x7e, pma.states[0].base().unwrap().get());
    }

    #[test]
    fn test_n_blocks_1_2() {
        let mut patterns = vec![];
        // state 0: reserved for the root state
        // state 1: reserved for the dead state
        // base = 0x80; fills 0x80..=0xfe
        for i in '\u{0}'..='\u{7e}' {
            let pattern: alloc::string::String = core::iter::once(i).collect();
            patterns.push(pattern);
        }
        let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
        assert_eq!(128, pma.num_states());
        assert_eq!(256, pma.states.len());
        assert_eq!(0x80, pma.states[0].base().unwrap().get());
    }

    #[test]
    fn test_n_blocks_2_1() {
        let mut patterns = vec![];
        // state 0: reserved for the root state
        // state 1: reserved for the dead state
        // base = 0x80; fills 0x80..=0xff
        for i in '\u{0}'..='\u{7f}' {
            let pattern: alloc::string::String = core::iter::once(i).collect();
            patterns.push(pattern);
        }
        // base = 0x7e; fills 0x02..=0x7f
        for i in '\u{0}'..='\u{7d}' {
            let pattern = ['\u{0}', i].into_iter().collect();
            patterns.push(pattern);
        }
        let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
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
        for i in '\u{0}'..='\u{7f}' {
            let pattern: alloc::string::String = core::iter::once(i).collect();
            patterns.push(pattern);
        }
        // base = 0x100; fills 0x100..=0x7e
        for i in '\u{0}'..='\u{7e}' {
            let pattern = ['\u{0}', i].into_iter().collect();
            patterns.push(pattern);
        }
        let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
        assert_eq!(256, pma.num_states());
        assert_eq!(384, pma.states.len());
        assert_eq!(0x80, pma.states[0].base().unwrap().get());
        assert_eq!(0x100, pma.states[0x80].base().unwrap().get());
    }

    #[test]
    fn test_serialize_state() {
        let x = State {
            base: NonZeroU32::new(42),
            check: 57,
            fail: 13,
            output_pos: NonZeroU32::new(100),
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
        let patterns = vec!["全世界", "世界", "に"];
        let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
        let bytes = pma.serialize();
        let (other, rest) =
            unsafe { CharwiseDoubleArrayAhoCorasick::deserialize_unchecked(&bytes) };
        assert!(rest.is_empty());
        assert_eq!(pma.states, other.states);
        assert_eq!(pma.mapper, other.mapper);
        assert_eq!(pma.outputs, other.outputs);
        assert_eq!(pma.match_kind, other.match_kind);
        assert_eq!(pma.num_states, other.num_states);
    }
}
