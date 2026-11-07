//! A character-wise version for faster matching on multibyte characters.

mod builder;
pub mod iter;
mod mapper;

use core::mem;
use core::num::NonZeroU32;

use alloc::vec::Vec;

pub use crate::charwise::builder::CharwiseDoubleArrayAhoCorasickBuilder;
use crate::charwise::iter::{
    CharWithEndOffsetIterator, FindIterator, FindOverlappingIterator,
    FindOverlappingNoSuffixIterator, FindOverlappingNoSuffixSliceIterator,
    FindOverlappingSliceIterator, FindOverlappingStepper, FindSliceIterator, FindStepper,
    LeftmostFindIterator, LeftmostFindIteratorExperimental, LeftmostFinderExperimental,
    PatternIterator,
};
use crate::charwise::mapper::CodeMapper;
use crate::errors::{DaachorseError, Result};
use crate::prefilter::{Prefilter, PrefilterGate};
use crate::serializer::{Serializable, SerializableVec};
use crate::utils::FromU32;
use crate::{Emit, MatchKind, Output, DEAD_STATE_IDX, ROOT_STATE_IDX};

/// Maximum number of states supported in experimental leftmost matching.
pub(crate) const LEFTMOST_EXPERIMENTAL_MAX_NUM_STATES: u32 =
    State::LEFTMOST_EXPERIMENTAL_FAIL_STATE_MASK;

/// A fast multiple pattern match automaton implemented with the Aho-Corasick algorithm and
/// character-wise double-array data structure.
///
/// The standard version [`DoubleArrayAhoCorasick`](super::DoubleArrayAhoCorasick) handles strings
/// as UTF-8 sequences and defines transition labels using byte values. In contrast, the
/// character-wise version uses Unicode code point values, reducing the number of transitions and
/// enabling faster matching on multibyte characters.
///
/// # Features
///
/// Compared to [`DoubleArrayAhoCorasick`](super::DoubleArrayAhoCorasick),
/// [`CharwiseDoubleArrayAhoCorasick`] has the following features
/// if it is built from multibyte strings such as CJK characters:
///
///  - Matching speed is generally faster.
///  - Construction time may be slower.
///  - Memory usage depends on the pattern set.
///    - If the scale is large, the memory efficiency can be competitive.
///    - If the scale is small, the double array can be sparse and memory-inefficient.
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
    /// Committed match chains for experimental leftmost matching.
    emits: Vec<Emit<V>>,
    match_kind: MatchKind,
    num_states: u32,
    prefilter: Option<Prefilter>,
    depths: Vec<u32>,
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
    /// [`DaachorseError`] is returned when
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

    /// Creates a new [`CharwiseDoubleArrayAhoCorasick`] from pattern-value pairs.
    ///
    /// # Arguments
    ///
    /// * `patvals` - List of pattern-value pairs.
    ///
    /// # Errors
    ///
    /// [`DaachorseError`] is returned when
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
    /// The iterator searches from the beginning of the input string, yielding a value immediately
    /// when a pattern is found. The next search resumes from the end of the previously found
    /// pattern.
    ///
    /// If the set contains an empty string (length 0), all other patterns are ignored, and it will
    /// only match at every character boundary, including the start and end of the haystack.
    ///
    /// # Arguments
    ///
    /// * `haystack` - String to search in.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] during construction, the iterator is not
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
    pub fn find_iter<P>(&self, haystack: P) -> FindSliceIterator<'_, P, V>
    where
        P: AsRef<str>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindSliceIterator {
            pma: self,
            haystack,
            pos: 0,
            first_call: true,
            prefilter: self.prefilter.as_ref(),
            gate: PrefilterGate::new(),
        }
    }

    /// Returns an iterator of non-overlapping matches in the given haystack iterator.
    ///
    /// The algorithm used is the same as the [`CharwiseDoubleArrayAhoCorasick::find_iter()`]
    /// function. However, the match-candidate prefilter is not available in this function because
    /// it requires random access to the haystack; the search is always performed on the
    /// Aho-Corasick automaton alone, even if the automaton has a prefilter.
    ///
    /// # Arguments
    ///
    /// * `haystack` - [`u8`] iterator representing a valid UTF-8 string to search in.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] during construction, the iterator is not
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
    pub unsafe fn find_iter_from_iter<P>(&self, haystack: P) -> FindIterator<'_, P, V>
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
            first_call: true,
        }
    }

    /// Returns an iterator of overlapping matches in the given haystack.
    ///
    /// The iterator follows the standard behavior of the Aho-Corasick algorithm. It searches from
    /// the beginning of the input string, and upon reaching a given position, it yields the
    /// patterns ending at that position in descending order of length.
    ///
    /// If the pattern set contains duplicate patterns, they are yielded in the order they were
    /// registered.
    ///
    /// # Arguments
    ///
    /// * `haystack` - String to search in.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] during construction, the iterator is not
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
    pub fn find_overlapping_iter<P>(&self, haystack: P) -> FindOverlappingSliceIterator<'_, P, V>
    where
        P: AsRef<str>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindOverlappingSliceIterator {
            pma: self,
            haystack,
            state_id: ROOT_STATE_IDX,
            pos: 0,
            output_pos: unsafe {
                self.states
                    .get_unchecked(usize::from_u32(ROOT_STATE_IDX))
                    .output_pos()
            },
            prefilter: self.prefilter.as_ref(),
            gate: PrefilterGate::new(),
        }
    }

    /// Returns an iterator of overlapping matches in the given haystack iterator.
    ///
    /// The algorithm used is the same as the
    /// [`CharwiseDoubleArrayAhoCorasick::find_overlapping_iter()`] function. However, the
    /// match-candidate prefilter is not available in this function because it requires random
    /// access to the haystack; the search is always performed on the Aho-Corasick automaton
    /// alone, even if the automaton has a prefilter.
    ///
    /// # Arguments
    ///
    /// * `haystack` - [`u8`] iterator representing a valid UTF-8 string to search in.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] during construction, the iterator is not
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
    ) -> FindOverlappingIterator<'_, P, V>
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
            output_pos: unsafe {
                self.states
                    .get_unchecked(usize::from_u32(ROOT_STATE_IDX))
                    .output_pos()
            },
        }
    }

    /// Returns an iterator of overlapping matches without suffixes in the given haystack.
    ///
    /// The behavior of the iterator returned by this function is similar to
    /// [`CharwiseDoubleArrayAhoCorasick::find_overlapping_iter()`], except that upon reaching a
    /// given position, it yields only the single longest pattern ending at that position.
    ///
    /// # Arguments
    ///
    /// * `haystack` - String to search in.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] during construction, the iterator is not
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
    ) -> FindOverlappingNoSuffixSliceIterator<'_, P, V>
    where
        P: AsRef<str>,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindOverlappingNoSuffixSliceIterator {
            pma: self,
            haystack,
            state_id: ROOT_STATE_IDX,
            pos: 0,
            first_call: true,
            prefilter: self.prefilter.as_ref(),
            gate: PrefilterGate::new(),
        }
    }

    /// Returns an iterator of overlapping matches without suffixes in the given haystack iterator.
    ///
    /// The algorithm used is the same as the
    /// [`CharwiseDoubleArrayAhoCorasick::find_overlapping_no_suffix_iter()`] function. However,
    /// the match-candidate prefilter is not available in this function because it requires random
    /// access to the haystack; the search is always performed on the Aho-Corasick automaton
    /// alone, even if the automaton has a prefilter.
    ///
    /// # Arguments
    ///
    /// * `haystack` - [`u8`] iterator representing a valid UTF-8 string to search in.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] during construction, the iterator is not
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
    ) -> FindOverlappingNoSuffixIterator<'_, P, V>
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
            first_call: true,
        }
    }

    /// Returns an iterator of leftmost matches in the given haystack.
    ///
    /// The iterator greedily searches from the beginning of the input string. The next search
    /// resumes from the end of the previously found pattern.
    ///
    /// Depending on the [`MatchKind`] option specified during construction, the behavior differs
    /// for multiple possible matches, as follows.
    ///
    ///  - If you set [`MatchKind::LeftmostLongest`], it reports the match corresponding to the
    ///    longest pattern.
    ///
    ///  - If you set [`MatchKind::LeftmostFirst`], it reports the match corresponding to the
    ///    pattern that was registered earlier in the automaton.
    ///
    /// If the pattern set contains an empty string (length 0), the empty string matches at all
    /// positions between characters that do not overlap with other patterns.
    ///
    /// # Arguments
    ///
    /// * `haystack` - String to search in.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::LeftmostFirst`] or [`MatchKind::LeftmostLongest`] in the
    /// construction, the iterator is not supported and the function will panic.
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
    pub fn leftmost_find_iter<P>(&self, haystack: P) -> LeftmostFindIterator<'_, P, V>
    where
        P: AsRef<str>,
    {
        assert!(
            self.match_kind == MatchKind::LeftmostFirst
                || self.match_kind == MatchKind::LeftmostLongest,
            "Error: match_kind must be leftmost_first or leftmost_longest. For experimental leftmost, use leftmost_find_iter_experimental() or leftmost_finder_experimental()."
        );
        LeftmostFindIterator {
            pma: self,
            haystack,
            pos: 0,
            init_output_pos: unsafe {
                self.states
                    .get_unchecked(usize::from_u32(ROOT_STATE_IDX))
                    .output_pos()
            },
            skip_empty: false,
            gate: PrefilterGate::new(),
        }
    }

    /// Returns an iterator of non-overlapping leftmost matches in the given haystack.
    ///
    /// Matches are evaluated in linear time.
    ///
    /// Depending on the [`MatchKind`] option specified during construction, the behavior differs
    /// for multiple possible matches, as follows.
    ///
    ///  - If you set [`MatchKind::LeftmostLongestExperimental`], it reports the match corresponding to
    ///    the longest pattern.
    ///
    ///  - If you set [`MatchKind::LeftmostFirstExperimental`], it reports the match corresponding to
    ///    the pattern that was registered earlier in the automaton.
    ///
    /// If the pattern set contains an empty string (length 0), the empty string matches at all
    /// positions between characters that do not overlap with other patterns.
    ///
    /// This iterator maintains an internal buffer and may allocate heap memory during search.
    /// For repeated searches, consider using
    /// [`leftmost_finder_experimental()`](Self::leftmost_finder_experimental) to retain a buffer
    /// across searches and avoid repeated allocations.
    ///
    /// # Arguments
    ///
    /// * `haystack` - String to search in.
    ///
    /// # Panics
    ///
    /// Panics if the automaton was not constructed with [`MatchKind::LeftmostLongestExperimental`]
    /// or [`MatchKind::LeftmostFirstExperimental`].
    ///
    /// # Examples
    ///
    /// ## LeftmostLongestExperimental
    ///
    /// ```
    /// use daachorse::{CharwiseDoubleArrayAhoCorasickBuilder, MatchKind};
    ///
    /// let patterns = vec!["ab", "abcd"];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
    ///     .match_kind(MatchKind::LeftmostLongestExperimental)
    ///     .build(&patterns)
    ///     .unwrap();
    ///
    /// let mut it = pma.leftmost_find_iter_experimental("abcd");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 4, 1), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    ///
    /// ## LeftmostFirstExperimental
    ///
    /// ```
    /// use daachorse::{CharwiseDoubleArrayAhoCorasickBuilder, MatchKind};
    ///
    /// let patterns = vec!["ab", "abcd"];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
    ///     .match_kind(MatchKind::LeftmostFirstExperimental)
    ///     .build(&patterns)
    ///     .unwrap();
    ///
    /// let mut it = pma.leftmost_find_iter_experimental("abcd");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 2, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn leftmost_find_iter_experimental<P>(
        &self,
        haystack: P,
    ) -> LeftmostFindIteratorExperimental<'_, P, V>
    where
        P: AsRef<str>,
        V: Copy,
    {
        assert!(
            self.match_kind.is_leftmost_experimental(),
            "Error: match_kind must be leftmost_longest_experimental or leftmost_first_experimental."
        );
        LeftmostFindIteratorExperimental::with_buf(self, haystack, Vec::new())
    }

    /// Returns a finder for non-overlapping leftmost matches that retains an internal buffer across searches.
    ///
    /// Matches are evaluated in linear time.
    ///
    /// While [`leftmost_find_iter_experimental()`](Self::leftmost_find_iter_experimental)
    /// allocates an internal buffer for each search, this finder retains its buffer across searches,
    /// eliminating repeated heap allocations during repeated searches.
    ///
    /// # Panics
    ///
    /// Panics if the automaton was not constructed with [`MatchKind::LeftmostLongestExperimental`]
    /// or [`MatchKind::LeftmostFirstExperimental`].
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::{CharwiseDoubleArrayAhoCorasickBuilder, MatchKind};
    ///
    /// let patterns = vec!["ab", "abcd"];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
    ///     .match_kind(MatchKind::LeftmostLongestExperimental)
    ///     .build(&patterns)
    ///     .unwrap();
    ///
    /// let mut finder = pma.leftmost_finder_experimental();
    ///
    /// let mut it = finder.find_iter("abcd");
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 4, 1), (m.start(), m.end(), m.value()));
    /// assert_eq!(None, it.next());
    ///
    /// // The finder can be reused across subsequent searches without reallocation:
    /// let mut it = finder.find_iter("ab");
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 2, 0), (m.start(), m.end(), m.value()));
    /// assert_eq!(None, it.next());
    /// ```
    #[must_use]
    pub fn leftmost_finder_experimental(&self) -> LeftmostFinderExperimental<'_, V>
    where
        V: Copy,
    {
        LeftmostFinderExperimental::new(self)
    }

    /// Returns a stepper of non-overlapping matches that consumes characters one by one.
    ///
    /// The algorithm used is the same as the [`CharwiseDoubleArrayAhoCorasick::find_iter()`]
    /// function.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] during construction, the stepper is not
    /// supported and the function will panic.
    ///
    /// # Examples
    ///
    /// ## Example 1: Basic usage
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut stepper = pma.find_stepper();
    ///
    /// let m = stepper.matches();
    /// assert_eq!(None, m);
    ///
    /// stepper.consume('全');
    /// let m = stepper.matches();
    /// assert_eq!(None, m);
    ///
    /// stepper.consume('世');
    /// let m = stepper.matches();
    /// assert_eq!(None, m);
    ///
    /// stepper.consume('界');
    /// let m = stepper.matches().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value())); // 全世界
    ///
    /// stepper.consume('中');
    /// let m = stepper.matches();
    /// assert_eq!(None, m);
    ///
    /// stepper.consume('に');
    /// let m = stepper.matches().unwrap();
    /// assert_eq!((12, 15, 2), (m.start(), m.end(), m.value())); // に
    /// ```
    ///
    /// ## Example 2: Behavior with zero-length pattern
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に", ""];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut stepper = pma.find_stepper();
    ///
    /// let m = stepper.matches().unwrap();
    /// assert_eq!((0, 0, 3), (m.start(), m.end(), m.value())); // ""
    ///
    /// stepper.consume('全');
    /// let m = stepper.matches().unwrap();
    /// assert_eq!((3, 3, 3), (m.start(), m.end(), m.value())); // ""
    /// ```
    ///
    /// ## Example 3: Cloning stepper
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["アリア", "アリス"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut stepper = pma.find_stepper();
    ///
    /// stepper.consume('ア');
    /// stepper.consume('リ');
    ///
    /// let mut stepper2 = stepper.clone();
    ///
    /// stepper.consume('ア');
    /// let m = stepper.matches().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value())); // アリア
    ///
    /// stepper2.consume('ス');
    /// let m = stepper2.matches().unwrap();
    /// assert_eq!((0, 9, 1), (m.start(), m.end(), m.value())); // アリス
    /// ```
    #[must_use]
    pub fn find_stepper(&self) -> FindStepper<'_, V>
    where
        V: Copy,
    {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindStepper {
            pma: self,
            state_id: ROOT_STATE_IDX,
            pos: 0,
            output_pos: unsafe {
                self.states
                    .get_unchecked(usize::from_u32(ROOT_STATE_IDX))
                    .output_pos()
            },
        }
    }

    /// Returns a stepper of overlapping matches that consumes characters one by one.
    ///
    /// The algorithm used is the same as the
    /// [`CharwiseDoubleArrayAhoCorasick::find_overlapping_iter()`] function.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] during construction, the stepper is not
    /// supported and the function will panic.
    ///
    /// # Examples
    ///
    /// ## Example 1: Basic usage
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut stepper = pma.find_overlapping_stepper();
    ///
    /// let mut it = stepper.matches();
    /// assert_eq!(None, it.next());
    ///
    /// stepper.consume('全');
    /// let mut it = stepper.matches();
    /// assert_eq!(None, it.next());
    ///
    /// stepper.consume('世');
    /// let mut it = stepper.matches();
    /// assert_eq!(None, it.next());
    ///
    /// stepper.consume('界');
    /// let mut it = stepper.matches();
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value())); // 全世界
    /// let m = it.next().unwrap();
    /// assert_eq!((3, 9, 1), (m.start(), m.end(), m.value())); // 世界
    /// assert_eq!(None, it.next());
    ///
    /// stepper.consume('中');
    /// let mut it = stepper.matches();
    /// assert_eq!(None, it.next());
    ///
    /// stepper.consume('に');
    /// let mut it = stepper.matches();
    /// let m = it.next().unwrap();
    /// assert_eq!((12, 15, 2), (m.start(), m.end(), m.value())); // に
    /// assert_eq!(None, it.next());
    /// ```
    ///
    /// ## Example 2: Behavior with zero-length pattern
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に", ""];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut stepper = pma.find_overlapping_stepper();
    ///
    /// let mut it = stepper.matches();
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 0, 3), (m.start(), m.end(), m.value())); // ""
    /// assert_eq!(None, it.next());
    ///
    /// stepper.consume('に');
    /// let mut it = stepper.matches();
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 3, 2), (m.start(), m.end(), m.value())); // に
    /// let m = it.next().unwrap();
    /// assert_eq!((3, 3, 3), (m.start(), m.end(), m.value())); // ""
    /// assert_eq!(None, it.next());
    /// ```
    ///
    /// ## Example 3: Cloning stepper
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["アリア", "アリス"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut stepper = pma.find_overlapping_stepper();
    ///
    /// stepper.consume('ア');
    /// stepper.consume('リ');
    ///
    /// let mut stepper2 = stepper.clone();
    ///
    /// stepper.consume('ア');
    /// let mut it = stepper.matches();
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value())); // アリア
    /// assert_eq!(None, it.next());
    ///
    /// stepper2.consume('ス');
    /// let mut it = stepper2.matches();
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 1), (m.start(), m.end(), m.value())); // アリス
    /// assert_eq!(None, it.next());
    /// ```
    #[must_use]
    pub fn find_overlapping_stepper(&self) -> FindOverlappingStepper<'_, V> {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        FindOverlappingStepper {
            pma: self,
            state_id: ROOT_STATE_IDX,
            pos: 0,
        }
    }

    /// Returns the match kind for this automaton.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::{CharwiseDoubleArrayAhoCorasickBuilder, MatchKind};
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
    ///     .match_kind(MatchKind::LeftmostLongest)
    ///     .build::<_, _, u32>(&patterns)
    ///     .unwrap();
    ///
    /// assert_eq!(MatchKind::LeftmostLongest, pma.match_kind());
    /// ```
    #[must_use]
    pub const fn match_kind(&self) -> MatchKind {
        self.match_kind
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

    /// Returns an iterator that yields all registered pattern-value pairs in lexicographical order.
    ///
    /// When using [`MatchKind::LeftmostFirst`] or [`MatchKind::LeftmostFirstExperimental`], patterns
    /// registered after any of their proper prefixes can never be matched. Consequently, they are
    /// not stored in the automaton and will not be yielded. Under experimental leftmost matching,
    /// duplicate pattern strings yield only the first-registered value.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
    ///
    /// let mut it = pma.iter();
    /// assert_eq!(Some(("に".to_string(), 2)), it.next());
    /// assert_eq!(Some(("世界".to_string(), 1)), it.next());
    /// assert_eq!(Some(("全世界".to_string(), 0)), it.next());
    /// assert_eq!(None, it.next());
    /// ```
    #[must_use]
    pub fn iter(&self) -> PatternIterator<'_, V> {
        PatternIterator::new(self)
    }

    /// Computes and caches depths of states to enable [`FindStepper::depth()`] and
    /// [`FindOverlappingStepper::depth()`].
    ///
    /// This cache is not serialized, so you need to call this function again after deserialization.
    ///
    /// # Errors
    ///
    /// [`DaachorseError`] is returned when the automaton is invalid. This can occur with
    /// malformed automata that pose no safety issue but cannot be fully validated during
    /// deserialization.
    ///
    /// # Panics
    ///
    /// If you do not specify [`MatchKind::Standard`] during construction, the stepper is not
    /// supported and the function will panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["世界", "界"];
    /// let mut pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
    /// pma.cache_depths().unwrap();
    ///
    /// let mut stepper = pma.find_overlapping_stepper();
    /// stepper.consume('世');
    /// stepper.consume('界');
    /// assert_eq!(Some(2), stepper.depth());
    /// ```
    pub fn cache_depths(&mut self) -> Result<()> {
        assert!(
            self.match_kind.is_standard(),
            "Error: match_kind must be standard."
        );
        let alphabet_size = self.mapper.alphabet_size();
        self.depths = vec![0; self.states.len()];
        unsafe {
            let mut path = vec![];
            for mut state_id in 0..self.states.len() {
                if *self.depths.get_unchecked(state_id) != 0 {
                    continue;
                }
                let mut depth = loop {
                    let depth = *self.depths.get_unchecked(state_id);
                    if depth != 0 || state_id == usize::from_u32(ROOT_STATE_IDX) {
                        break depth;
                    }
                    if path.len() > self.states.len() {
                        return Err(DaachorseError::invalid_automaton());
                    }
                    let parent_id = usize::from_u32(self.states.get_unchecked(state_id).check());
                    let is_child = self
                        .states
                        .get(parent_id)
                        .and_then(State::base)
                        .is_some_and(|base| {
                            base.get() ^ u32::try_from(state_id).unwrap() < alphabet_size
                        });
                    if !is_child {
                        *self.depths.get_unchecked_mut(state_id) = u32::MAX;
                        break u32::MAX;
                    }
                    path.push(state_id);
                    state_id = parent_id;
                };
                if depth == u32::MAX && !path.is_empty() {
                    return Err(DaachorseError::invalid_automaton());
                }
                while let Some(idx) = path.pop() {
                    depth += 1;
                    *self.depths.get_unchecked_mut(idx) = depth;
                }
            }
        }
        Ok(())
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
            + self.emits.len() * mem::size_of::<Emit<V>>()
            + self.prefilter.as_ref().map_or(0, Prefilter::heap_bytes)
            + self.depths.len() * mem::size_of::<u32>()
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
                + u32::serialized_bytes()
                // A serialized None is a single flag byte; see the Serializable impl of Option.
                + self
                    .prefilter
                    .as_ref()
                    .map_or_else(u8::serialized_bytes, |_| {
                        Option::<Prefilter>::serialized_bytes()
                    })
                + if self.match_kind.is_leftmost_experimental() {
                    self.emits.serialized_bytes()
                } else {
                    0
                },
        );
        self.states.serialize_to_vec(&mut result);
        self.mapper.serialize_to_vec(&mut result);
        self.outputs.serialize_to_vec(&mut result);
        self.match_kind.serialize_to_vec(&mut result);
        self.num_states.serialize_to_vec(&mut result);
        self.prefilter.serialize_to_vec(&mut result);
        if self.match_kind.is_leftmost_experimental() {
            self.emits.serialize_to_vec(&mut result);
        }
        result
    }

    /// Deserializes the automaton from the given slice.
    ///
    /// # Warning
    ///
    /// This function verifies that the input automaton data will not cause out-of-bounds memory
    /// access within this crate; however, it does not verify that the data is a valid
    /// Aho-Corasick automaton. Consequently, if malformed data is provided, it may lead to
    /// infinite loops or cause [`Match`](crate::Match) to return inaccurate ranges. Use this
    /// function only if you can tolerate such errors.
    ///
    /// # Arguments
    ///
    /// * `source` - A source slice.
    ///
    /// # Returns
    ///
    /// A tuple of the automaton and the slice not used for the deserialization.
    ///
    /// # Errors
    ///
    /// [`DaachorseError`] is returned when the given data is an invalid automaton.
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
    /// let (pma, _) = CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes).unwrap();
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
    pub fn deserialize(source: &[u8]) -> Result<(Self, &[u8])>
    where
        V: Serializable,
    {
        let (states, source) = Vec::<State>::deserialize_from_slice(source)?;
        let (mapper, source) = CodeMapper::deserialize_from_slice(source)?;
        let (outputs, source) = Vec::<Output<V>>::deserialize_from_slice(source)?;
        let (match_kind, source) = MatchKind::deserialize_from_slice(source)?;
        let (num_states, source) = u32::deserialize_from_slice(source)?;
        let (prefilter, source) = Option::<Prefilter>::deserialize_from_slice(source)?;
        let (emits, source) = if match_kind.is_leftmost_experimental() {
            Vec::<Emit<V>>::deserialize_from_slice(source)?
        } else {
            (vec![], source)
        };
        let pma = Self {
            states,
            mapper,
            outputs,
            emits,
            match_kind,
            num_states,
            prefilter,
            depths: vec![],
        };
        for &id in &pma.mapper.table {
            if id == crate::charwise::mapper::INVALID_CODE {
                continue;
            }
            if id >= pma.mapper.alphabet_size() {
                return Err(DaachorseError::invalid_automaton());
            }
        }
        // `next_state_id_unchecked()` relies on that each block covers all codes in the alphabet.
        let Some(block_len) = pma.mapper.block_len() else {
            return Err(DaachorseError::invalid_automaton());
        };
        let block_len = usize::from_u32(block_len);
        if pma.states.is_empty() {
            return Err(DaachorseError::invalid_automaton());
        }
        if pma.states.len() % block_len != 0 {
            return Err(DaachorseError::invalid_automaton());
        }
        let states_len = pma.states.len();
        let pool_len = if pma.match_kind.is_leftmost_experimental() {
            pma.emits.len()
        } else {
            pma.outputs.len()
        };
        for state in &pma.states {
            if let Some(base) = state.base() {
                if usize::from_u32(base.get()) >= states_len {
                    return Err(DaachorseError::invalid_automaton());
                }
            };
            let fail_id = if pma.match_kind.is_leftmost_experimental() {
                state.leftmost_experimental_fail()
            } else {
                state.fail()
            };
            if usize::from_u32(fail_id) >= states_len {
                return Err(DaachorseError::invalid_automaton());
            }
            if let Some(output_pos) = state.output_pos() {
                if usize::from_u32(output_pos.get() - 1) >= pool_len {
                    return Err(DaachorseError::invalid_automaton());
                }
            };
        }
        for (i, output) in pma.outputs.iter().enumerate() {
            if let Some(parent) = output.parent {
                if usize::from_u32(parent.get() - 1) >= i {
                    return Err(DaachorseError::invalid_automaton());
                }
            };
        }
        for (i, emit) in pma.emits.iter().enumerate() {
            if let Some(pred) = emit.pred {
                if usize::from_u32(pred.get() - 1) >= i {
                    return Err(DaachorseError::invalid_automaton());
                }
            };
        }
        if pma.match_kind.is_leftmost_experimental() {
            pma.leftmost_experimental_validate_states()?;
        }
        Ok((pma, source))
    }

    /// Deserializes the automaton from the given slice without performing any validation.
    ///
    /// Prefer [`CharwiseDoubleArrayAhoCorasick::deserialize()`] unless maximum performance is
    /// critical, as this function skips all validation.
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
    /// The given data must be a valid automaton exported by
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
        let (states, source) = Vec::<State>::deserialize_from_slice(source).unwrap_unchecked();
        let (mapper, source) = CodeMapper::deserialize_from_slice(source).unwrap_unchecked();
        let (outputs, source) = Vec::<Output<V>>::deserialize_from_slice(source).unwrap_unchecked();
        let (match_kind, source) = MatchKind::deserialize_from_slice(source).unwrap_unchecked();
        let (num_states, source) = u32::deserialize_from_slice(source).unwrap_unchecked();
        let (prefilter, source) =
            Option::<Prefilter>::deserialize_from_slice(source).unwrap_unchecked();
        let (emits, source) = if match_kind.is_leftmost_experimental() {
            Vec::<Emit<V>>::deserialize_from_slice(source).unwrap_unchecked()
        } else {
            (vec![], source)
        };
        (
            Self {
                states,
                mapper,
                outputs,
                emits,
                match_kind,
                num_states,
                prefilter,
                depths: vec![],
            },
            source,
        )
    }

    /// Returns the position of the output entries of the given state.
    ///
    /// # Safety
    ///
    /// `state_id` must be smaller than the length of `states`.
    #[inline(always)]
    unsafe fn output_pos_unchecked(&self, state_id: u32) -> Option<NonZeroU32> {
        self.states
            .get_unchecked(usize::from_u32(state_id))
            .output_pos()
    }

    /// Returns the output entry at the given position.
    ///
    /// # Safety
    ///
    /// `output_pos` must be obtained from [`State::output_pos()`] or [`Output::parent()`] of
    /// this automaton, which guarantees `output_pos.get() - 1` to be a valid index of `outputs`.
    #[inline(always)]
    unsafe fn output_at(&self, output_pos: NonZeroU32) -> &Output<V> {
        self.outputs
            .get_unchecked(usize::from_u32(output_pos.get() - 1))
    }

    /// Returns the value to report when the pattern set contains the empty string, which is
    /// registered as an output of the root state.
    #[inline(always)]
    fn root_output_value(&self) -> Option<V>
    where
        V: Copy,
    {
        // The states of an automaton are never empty, so the root state always exists.
        unsafe {
            self.output_pos_unchecked(ROOT_STATE_IDX)
                .map(|output_pos| self.output_at(output_pos).value())
        }
    }

    /// # Safety
    ///
    /// `state_id` must be smaller than the length of states.
    #[inline(always)]
    unsafe fn next_state_id_unchecked(&self, mut state_id: u32, c: char) -> u32 {
        // Map the character to its integer label, if it exists in the mapper.
        if let Some(mapped_c) = self.mapper.get(c) {
            loop {
                // Get the current state.
                let state = self.states.get_unchecked(usize::from_u32(state_id));

                // If the state has transitions (indicated by a non-None base value):
                if let Some(base) = state.base() {
                    // Calculate the child index in the double-array using base ^ mapped_c.
                    let child_idx = base.get() ^ mapped_c;
                    let child = self.states.get_unchecked(usize::from_u32(child_idx));
                    // Verify if the transition exists by checking if the child's check value matches state_id.
                    if child.check() == state_id {
                        return child_idx;
                    }
                }

                // If no transition is found and we are already at the root state, stay/reset at the root state.
                if state_id == ROOT_STATE_IDX {
                    return ROOT_STATE_IDX;
                }

                // Follow the failure transition to the next candidate state.
                state_id = state.fail();
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
        // Map the character to its integer label, if it exists in the mapper.
        if let Some(mapped_c) = self.mapper.get(c) {
            loop {
                // Get the current state.
                let state = self.states.get_unchecked(usize::from_u32(state_id));

                // If the state has transitions (indicated by a non-None base value):
                if let Some(base) = state.base() {
                    // Calculate the child index in the double-array using base ^ mapped_c.
                    let child_idx = base.get() ^ mapped_c;
                    let child = self.states.get_unchecked(usize::from_u32(child_idx));
                    // Verify if the transition exists by checking if the child's check value matches state_id.
                    if child.check() == state_id {
                        return child_idx;
                    }
                }

                // If no transition is found and we are already at the root state, stay/reset at the root state.
                if state_id == ROOT_STATE_IDX {
                    return ROOT_STATE_IDX;
                }

                // In leftmost matching, we stop searching if the failure path hits the dead state.
                let fail_id = state.fail();
                if fail_id == DEAD_STATE_IDX {
                    return ROOT_STATE_IDX;
                }

                // Follow the failure transition to the next candidate state.
                state_id = fail_id;
            }
        } else {
            ROOT_STATE_IDX
        }
    }

    /// Validates failure targets and leaf emit presence for experimental leftmost matching.
    fn leftmost_experimental_validate_states(&self) -> Result<()> {
        for (i, state) in self.states.iter().enumerate() {
            if i != usize::from_u32(ROOT_STATE_IDX) && state.check() == DEAD_STATE_IDX {
                continue;
            }
            // Failure link must point to a valid state.
            let fail_id = state.leftmost_experimental_fail();
            if fail_id != ROOT_STATE_IDX
                && self.states[usize::from_u32(fail_id)].check() == DEAD_STATE_IDX
            {
                return Err(DaachorseError::invalid_automaton());
            }
            // Every leaf state must have an emit.
            if i != usize::from_u32(ROOT_STATE_IDX)
                && state.base().is_none()
                && state.output_pos().is_none()
            {
                return Err(DaachorseError::invalid_automaton());
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct State {
    base: Option<NonZeroU32>,
    check: u32,
    // Failure state index. In experimental leftmost matching, bit 31 flags if the failure chain has emits.
    fail: u32,
    // 1-based index into `outputs` (standard/legacy) or `emits` (experimental).
    output_pos: Option<NonZeroU32>,
}

impl Default for State {
    fn default() -> Self {
        Self {
            base: None,
            // DEAD_STATE_IDX (1) serves as the sentinel marking unused double-array slots.
            check: DEAD_STATE_IDX,
            fail: DEAD_STATE_IDX,
            output_pos: None,
        }
    }
}

impl State {
    pub(crate) const LEFTMOST_EXPERIMENTAL_FAIL_STATE_MASK: u32 = 0x7FFF_FFFF;
    pub(crate) const LEFTMOST_EXPERIMENTAL_FAIL_HAS_EMIT_BIT: u32 = 0x8000_0000;

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

    /// Returns the target failure state index with bit 31 (`LEFTMOST_EXPERIMENTAL_FAIL_HAS_EMIT_BIT`) masked out.
    #[inline(always)]
    pub const fn leftmost_experimental_fail(&self) -> u32 {
        self.fail & Self::LEFTMOST_EXPERIMENTAL_FAIL_STATE_MASK
    }

    /// Returns `true` if this state or any state along its failure chain has a match emit.
    #[inline(always)]
    pub const fn leftmost_experimental_has_emit(&self) -> bool {
        (self.fail & Self::LEFTMOST_EXPERIMENTAL_FAIL_HAS_EMIT_BIT) != 0
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
    pub fn set_leftmost_experimental_fail(&mut self, fail_id: u32, has_emit: bool) {
        debug_assert_eq!(fail_id & !Self::LEFTMOST_EXPERIMENTAL_FAIL_STATE_MASK, 0);
        let flag = if has_emit {
            Self::LEFTMOST_EXPERIMENTAL_FAIL_HAS_EMIT_BIT
        } else {
            0
        };
        self.fail = (fail_id & Self::LEFTMOST_EXPERIMENTAL_FAIL_STATE_MASK) | flag;
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
    fn deserialize_from_slice(src: &[u8]) -> Result<(Self, &[u8])> {
        let (base, src) = Option::<NonZeroU32>::deserialize_from_slice(src)?;
        let (check, src) = u32::deserialize_from_slice(src)?;
        let (fail, src) = u32::deserialize_from_slice(src)?;
        let (output_pos, src) = Option::<NonZeroU32>::deserialize_from_slice(src)?;
        Ok((
            Self {
                base,
                check,
                fail,
                output_pos,
            },
            src,
        ))
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
    fn test_multibyte_overlapping_zerolength_pattern() {
        let patterns = vec!["a", "æ", "あ", ""];
        let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
        let results = pma
            .find_overlapping_iter("いあabcÆæう")
            .map(|m| (m.start(), m.end(), m.value()))
            .collect::<Vec<_>>();
        /*
         *  い 0..3
         *  あ 3..6
         *  a  6..7
         *  b  7..8
         *  c  8..9
         *  Æ  9..11
         *  æ  11..13
         *  う 13..16
         */
        assert_eq!(
            vec![
                (0, 0, 3),
                (3, 3, 3),
                (3, 6, 2),
                (6, 6, 3),
                (6, 7, 0),
                (7, 7, 3),
                (8, 8, 3),
                (9, 9, 3),
                (11, 11, 3),
                (11, 13, 1),
                (13, 13, 3),
                (16, 16, 3),
            ],
            results,
        )
    }

    #[test]
    fn test_multibyte_standard_zerolength_pattern() {
        let patterns = vec!["a", "æ", "あ", ""];
        let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
        let results = pma
            .find_iter("いあabcÆæう")
            .map(|m| (m.start(), m.end(), m.value()))
            .collect::<Vec<_>>();
        assert_eq!(
            vec![
                (0, 0, 3),
                (3, 3, 3),
                (6, 6, 3),
                (7, 7, 3),
                (8, 8, 3),
                (9, 9, 3),
                (11, 11, 3),
                (13, 13, 3),
                (16, 16, 3),
            ],
            results,
        )
    }

    #[test]
    fn test_multibyte_leftmost_zerolength_pattern() {
        let patterns = vec!["a", "æ", "あ", ""];
        let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongest)
            .build(patterns)
            .unwrap();
        let results = pma
            .leftmost_find_iter("いあabcÆæう")
            .map(|m| (m.start(), m.end(), m.value()))
            .collect::<Vec<_>>();
        assert_eq!(
            vec![
                (0, 0, 3),
                (3, 6, 2),
                (6, 7, 0),
                (8, 8, 3),
                (9, 9, 3),
                (11, 13, 1),
                (16, 16, 3),
            ],
            results,
        )
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
        let (y, rest) = State::deserialize_from_slice(&data).unwrap();
        assert!(rest.is_empty());
        assert_eq!(x, y);
    }

    #[test]
    fn test_serialize_pma() {
        let patterns = vec!["全世界", "世界", "に"];
        let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
        let bytes = pma.serialize();
        let (other, rest) = CharwiseDoubleArrayAhoCorasick::deserialize(&bytes).unwrap();
        assert!(rest.is_empty());
        assert_eq!(pma.states, other.states);
        assert_eq!(pma.mapper, other.mapper);
        assert_eq!(pma.outputs, other.outputs);
        assert_eq!(pma.match_kind, other.match_kind);
        assert_eq!(pma.num_states, other.num_states);
    }

    #[test]
    fn test_serialize_empty_pma() {
        let patterns: [&str; 0] = [];
        let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
        let bytes = pma.serialize();
        let (other, rest) = CharwiseDoubleArrayAhoCorasick::deserialize(&bytes).unwrap();
        assert!(rest.is_empty());
        assert_eq!(pma.states, other.states);
        assert_eq!(pma.mapper, other.mapper);
        assert_eq!(pma.outputs, other.outputs);
        assert_eq!(pma.match_kind, other.match_kind);
        assert_eq!(pma.num_states, other.num_states);
    }

    #[test]
    fn test_deserialize_invalid_pma() {
        let bytes = [
            0, 0, 0, 0, // states
            0, 0, 0, 0, // table
            0, 0, 0, 0, // alphabet_size
            0, 0, 0, 0, // outputs
            0, // match_kind
            0, 0, 0, 0, // num_states
        ];
        let pma = CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes);
        assert!(pma.is_err());
    }

    #[test]
    fn test_deserialize_overflowing_alphabet_size() {
        // The block length, i.e., the alphabet size rounded up to a power of two, overflows u32.
        // If it were wrapped, the states would pass the length check, and transitions with the
        // code 0x7fffffff would access out of the states.
        let mut bytes = [
            2, 0, 0, 0, // states
            1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // states[0]
            0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // states[1]
            1, 0, 0, 0, // table
            0xff, 0xff, 0xff, 0x7f, // table[0]
            1, 0, 0, 0x80, // alphabet_size
            0, 0, 0, 0, // outputs
            0, // match_kind
            1, 0, 0, 0, // num_states
            0, // prefilter
        ];
        let pma = CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes);
        assert!(pma.is_err());

        // The other fields are valid: the automaton is accepted with the code 0 and the alphabet
        // size 1.
        bytes[40..44].copy_from_slice(&0u32.to_le_bytes());
        bytes[44..48].copy_from_slice(&1u32.to_le_bytes());
        let pma = CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes);
        assert!(pma.is_ok());
    }

    fn get_state(bytes: &[u8], idx: u32) -> (u32, u32, u32, u32) {
        let off = 4 + usize::try_from(idx).unwrap() * 16;
        (
            u32::from_le_bytes(bytes[off..off + 4].try_into().unwrap()),
            u32::from_le_bytes(bytes[off + 4..off + 8].try_into().unwrap()),
            u32::from_le_bytes(bytes[off + 8..off + 12].try_into().unwrap()),
            u32::from_le_bytes(bytes[off + 12..off + 16].try_into().unwrap()),
        )
    }

    fn patch_state(
        bytes: &mut [u8],
        idx: u32,
        base: Option<u32>,
        check: Option<u32>,
        fail: Option<u32>,
        output_pos: Option<u32>,
    ) {
        let off = 4 + usize::try_from(idx).unwrap() * 16;
        if let Some(b) = base {
            bytes[off..off + 4].copy_from_slice(&b.to_le_bytes());
        }
        if let Some(c) = check {
            bytes[off + 4..off + 8].copy_from_slice(&c.to_le_bytes());
        }
        if let Some(f) = fail {
            bytes[off + 8..off + 12].copy_from_slice(&f.to_le_bytes());
        }
        if let Some(o) = output_pos {
            bytes[off + 12..off + 16].copy_from_slice(&o.to_le_bytes());
        }
    }

    #[test]
    fn test_deserialize_leaf_without_output_leftmost_experimental() {
        let pma: CharwiseDoubleArrayAhoCorasick<u32> = CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongestExperimental)
            .build(["ab"])
            .unwrap();
        let mut bytes = pma.serialize();
        let num_states = u32::from_le_bytes(bytes[..4].try_into().unwrap());
        let mut leaf_found = false;
        for idx in 1..num_states {
            let (base, check, _, output_pos) = get_state(&bytes, idx);
            if base == 0 && check != DEAD_STATE_IDX && output_pos != 0 {
                patch_state(&mut bytes, idx, None, None, None, Some(0));
                leaf_found = true;
                break;
            }
        }
        assert!(leaf_found);
        assert!(CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes).is_err());
    }

    #[test]
    fn test_deserialize_fail_to_dead_state_leftmost_experimental() {
        let pma: CharwiseDoubleArrayAhoCorasick<u32> = CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongestExperimental)
            .build(["ab", "c"])
            .unwrap();
        let mut bytes = pma.serialize();
        let num_states = u32::from_le_bytes(bytes[..4].try_into().unwrap());
        let mut patched = false;
        for idx in 1..num_states {
            let (base, check, _, _) = get_state(&bytes, idx);
            if check == ROOT_STATE_IDX && base != 0 {
                patch_state(&mut bytes, idx, None, None, Some(DEAD_STATE_IDX), None);
                patched = true;
                break;
            }
        }
        assert!(patched);
        assert!(CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes).is_err());
    }

    #[test]
    fn test_deserialize_fail_with_emit_flag_to_dead_state_leftmost_experimental() {
        let pma: CharwiseDoubleArrayAhoCorasick<u32> = CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongestExperimental)
            .build(["ab", "c"])
            .unwrap();
        let mut bytes = pma.serialize();
        let num_states = u32::from_le_bytes(bytes[..4].try_into().unwrap());
        let mut patched = false;
        for idx in 1..num_states {
            let (base, check, _, _) = get_state(&bytes, idx);
            if check == ROOT_STATE_IDX && base != 0 {
                patch_state(
                    &mut bytes,
                    idx,
                    None,
                    None,
                    Some(DEAD_STATE_IDX | State::LEFTMOST_EXPERIMENTAL_FAIL_HAS_EMIT_BIT),
                    None,
                );
                patched = true;
                break;
            }
        }
        assert!(patched);
        assert!(CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes).is_err());
    }

    #[test]
    fn test_deserialize_fail_to_unused_state_leftmost_experimental() {
        let pma: CharwiseDoubleArrayAhoCorasick<u32> = CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongestExperimental)
            .build(["ab", "c"])
            .unwrap();
        let mut bytes = pma.serialize();
        let num_states = u32::from_le_bytes(bytes[..4].try_into().unwrap());
        let mut unused_idx = None;
        let mut used_idx = None;
        for idx in 1..num_states {
            let (base, check, _, _) = get_state(&bytes, idx);
            if idx != DEAD_STATE_IDX && check == DEAD_STATE_IDX && unused_idx.is_none() {
                unused_idx = Some(idx);
            }
            if check == ROOT_STATE_IDX && base != 0 && used_idx.is_none() {
                used_idx = Some(idx);
            }
        }
        assert!(unused_idx.is_some() && used_idx.is_some());
        patch_state(&mut bytes, used_idx.unwrap(), None, None, unused_idx, None);
        assert!(CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes).is_err());
    }
}
