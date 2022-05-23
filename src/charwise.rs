//! A character-wise version for faster matching on multibyte characters.
//!
//! This sub-module provides a character-wise implementation of Daachorse,
//! [`CharwiseDoubleArrayAhoCorasick`].
//! The standard version [`DoubleArrayAhoCorasick`](super::DoubleArrayAhoCorasick)
//! handles strings as UTF-8 sequences
//! and defines transition labels using byte integers.
//! On the other hand, the character-wise version uses code point values of Unicode,
//! resulting in reducing the number of transitions and faster matching on multibyte characters.
//!
//! # Features
//!
//! Compared to [`DoubleArrayAhoCorasick`](super::DoubleArrayAhoCorasick),
//! [`CharwiseDoubleArrayAhoCorasick`] has the following features
//! if it is built from multibyte strings such as Japanese:
//!
//!  - Faster matching can be expected.
//!  - The construction time can be slower.
//!  - The memory efficiency depends on input patterns.
//!    - If the scale is large, the memory efficiency can be competitive.
//!    - If the scale is small, the double array can be sparse and memory inefficiency.
//!
//! # Examples
//!
//! The example finds non-overlapped occurrences with shortest matching
//! on UTF-8 strings.
//! Note that byte positions are reported.
//!
//! ```rust
//! use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
//!
//! let patterns = vec!["全世界", "世界", "に"];
//! let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
//!
//! let mut it = pma.find_iter("全世界中に");
//!
//! let m = it.next().unwrap();
//! assert_eq!((0, 9, 0), (m.start(), m.end(), m.value()));
//!
//! let m = it.next().unwrap();
//! assert_eq!((12, 15, 2), (m.start(), m.end(), m.value()));
//!
//! assert_eq!(None, it.next());
//! ```

mod builder;
pub mod iter;
pub(crate) mod mapper;

#[cfg(feature = "std")]
use std::io::{self, Read, Write};

use core::mem;
use core::num::NonZeroU32;

use alloc::vec::Vec;

pub use crate::charwise::builder::CharwiseDoubleArrayAhoCorasickBuilder;
use crate::charwise::iter::{
    CharWithEndOffsetIterator, FindIterator, FindOverlappingIterator,
    FindOverlappingNoSuffixIterator, LestmostFindIterator, StrIterator,
};
use crate::charwise::mapper::CodeMapper;
use crate::errors::Result;
use crate::{MatchKind, Output};

// The maximum BASE value used as an invalid value.
pub(crate) const BASE_INVALID: u32 = u32::MAX;
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
    mapper: CodeMapper,
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
    /// [`DaachorseError`](super::errors::DaachorseError) is returned when
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
    /// [`DaachorseError`](super::errors::DaachorseError) is returned when
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
    pub fn find_iter<P>(&self, haystack: P) -> FindIterator<StrIterator<P>>
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
    /// When you specify `MatchKind::{LeftmostFirst,LeftmostLongest}` in the construction,
    /// the iterator is not supported and the function will call panic!.
    ///
    /// # Safety
    ///
    /// `haystack` must represent a valid UTF-8 string.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
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
    pub unsafe fn find_iter_from_iter<P>(&self, haystack: P) -> FindIterator<P>
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
    pub fn find_overlapping_iter<P>(&self, haystack: P) -> FindOverlappingIterator<StrIterator<P>>
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
    /// When you specify `MatchKind::{LeftmostFirst,LeftmostLongest}` in the construction,
    /// the iterator is not supported and the function will call panic!.
    ///
    /// # Safety
    ///
    /// `haystack` must represent a valid UTF-8 string.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
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
    ) -> FindOverlappingIterator<P>
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
    ) -> FindOverlappingNoSuffixIterator<StrIterator<P>>
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
    /// When you specify `MatchKind::{LeftmostFirst,LeftmostLongest}` in the construction,
    /// the iterator is not supported and the function will call panic!.
    ///
    /// # Safety
    ///
    /// `haystack` must represent a valid UTF-8 string.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
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
    ) -> FindOverlappingNoSuffixIterator<P>
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
    /// The leftmost match greedily searches the longest possible match at each iteration, and
    /// the match results do not overlap positionally such as [`CharwiseDoubleArrayAhoCorasick::find_iter()`].
    ///
    /// According to the [`MatchKind`] option you specified in the construction,
    /// the behavior is changed for multiple possible matches, as follows.
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
    /// When you do not specify `MatchKind::{LeftmostFirst,LeftmostLongest}` in the construction,
    /// the iterator is not supported and the function will call panic!.
    ///
    /// # Examples
    ///
    /// ## LeftmostLongest
    ///
    /// ```
    /// use daachorse::MatchKind;
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasickBuilder;
    ///
    /// let patterns = vec!["世界", "世", "世界中に"];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
    ///           .match_kind(MatchKind::LeftmostLongest)
    ///           .build(&patterns)
    ///           .unwrap();
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
    /// use daachorse::MatchKind;
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasickBuilder;
    ///
    /// let patterns = vec!["世界", "世", "世界中に"];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
    ///           .match_kind(MatchKind::LeftmostFirst)
    ///           .build(&patterns)
    ///           .unwrap();
    ///
    /// let mut it = pma.leftmost_find_iter("世界中に");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 6, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn leftmost_find_iter<P>(&self, haystack: P) -> LestmostFindIterator<P>
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
    /// assert_eq!(pma.num_elements(), 8);
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
    /// assert_eq!(580, pma.heap_bytes());
    /// ```
    pub fn heap_bytes(&self) -> usize {
        self.states.len() * mem::size_of::<State>()
            + self.mapper.heap_bytes()
            + self.outputs.len() * mem::size_of::<Output>()
    }

    /// Serializes the automaton into a given target.
    ///
    /// # Arguments
    ///
    /// * `wtr` - A writable target.
    ///
    /// # Errors
    ///
    /// This function will return errors thrown by the given `wtr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let mut bytes = vec![];
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    /// pma.serialize(&mut bytes).unwrap();
    /// ```
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn serialize<W>(&self, mut wtr: W) -> io::Result<()>
    where
        W: Write,
    {
        wtr.write_all(&u32::try_from(self.states.len()).unwrap().to_le_bytes())?;
        for state in &self.states {
            wtr.write_all(&state.serialize())?;
        }
        self.mapper.serialize(&mut wtr)?;
        wtr.write_all(&u32::try_from(self.outputs.len()).unwrap().to_le_bytes())?;
        for output in &self.outputs {
            wtr.write_all(&output.serialize())?;
        }
        wtr.write_all(&[self.match_kind as u8])?;
        wtr.write_all(&u32::try_from(self.num_states).unwrap().to_le_bytes())?;
        Ok(())
    }

    /// Serializes the automaton into a [`Vec`].
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    /// let bytes = pma.serialize_to_vec();
    /// ```
    pub fn serialize_to_vec(&self) -> Vec<u8> {
        let mut result = Vec::with_capacity(
            mem::size_of::<u32>() * 3
                + mem::size_of::<u8>()
                + 16 * self.states.len()
                + self.mapper.serialized_bytes()
                + 8 * self.outputs.len(),
        );
        result.extend_from_slice(&u32::try_from(self.states.len()).unwrap().to_le_bytes());
        for state in &self.states {
            result.extend_from_slice(&state.serialize());
        }
        self.mapper.serialize_into_vec(&mut result);
        result.extend_from_slice(&u32::try_from(self.outputs.len()).unwrap().to_le_bytes());
        for output in &self.outputs {
            result.extend_from_slice(&output.serialize());
        }
        result.push(self.match_kind as u8);
        result.extend_from_slice(&u32::try_from(self.num_states).unwrap().to_le_bytes());
        result
    }

    /// Deserializes the automaton from a given source.
    ///
    /// # Arguments
    ///
    /// * `rdr` - A readable source.
    ///
    /// # Errors
    ///
    /// This function will return errors thrown by the given `rdr`.
    ///
    /// # Safety
    ///
    /// The given data must be a correct automaton exported by
    /// [`CharwiseDoubleArrayAhoCorasick::serialize()`] or
    /// [`CharwiseDoubleArrayAhoCorasick::serialize_to_vec()`] functions.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::Read;
    ///
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let mut bytes = vec![];
    ///
    /// {
    ///     let patterns = vec!["全世界", "世界", "に"];
    ///     let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    ///     pma.serialize(&mut bytes).unwrap();
    /// }
    ///
    /// let pma = unsafe {
    ///     CharwiseDoubleArrayAhoCorasick::deserialize_unchecked(&mut bytes.as_slice()).unwrap()
    /// };
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
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub unsafe fn deserialize_unchecked<R>(mut rdr: R) -> io::Result<Self>
    where
        R: Read,
    {
        let mut states_len_array = [0; 4];
        rdr.read_exact(&mut states_len_array)?;
        let states_len = u32::from_le_bytes(states_len_array) as usize;
        let mut states = Vec::with_capacity(states_len);
        for _ in 0..states_len {
            let mut state_array = [0; 16];
            rdr.read_exact(&mut state_array)?;
            states.push(State::deserialize(state_array));
        }

        let mapper = CodeMapper::deserialize_unchecked(&mut rdr)?;

        let mut outputs_len_array = [0; 4];
        rdr.read_exact(&mut outputs_len_array)?;
        let outputs_len = u32::from_le_bytes(outputs_len_array) as usize;
        let mut outputs = Vec::with_capacity(outputs_len);
        for _ in 0..outputs_len {
            let mut output_array = [0; 12];
            rdr.read_exact(&mut output_array)?;
            outputs.push(Output::deserialize(output_array));
        }

        let mut match_kind_array = [0];
        rdr.read_exact(&mut match_kind_array)?;
        let match_kind = MatchKind::from(match_kind_array[0]);

        let mut num_states_array = [0; 4];
        rdr.read_exact(&mut num_states_array)?;
        let num_states = u32::from_le_bytes(num_states_array) as usize;

        Ok(Self {
            states,
            mapper,
            outputs,
            match_kind,
            num_states,
        })
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
    /// [`CharwiseDoubleArrayAhoCorasick::serialize()`] or
    /// [`CharwiseDoubleArrayAhoCorasick::serialize_to_vec()`] functions.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    /// let bytes = pma.serialize_to_vec();
    ///
    /// let (pma, _) = unsafe {
    ///     CharwiseDoubleArrayAhoCorasick::deserialize_from_slice_unchecked(&bytes)
    /// };
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
    pub unsafe fn deserialize_from_slice_unchecked(mut source: &[u8]) -> (Self, &[u8]) {
        let states_len = u32::from_le_bytes(source[0..4].try_into().unwrap()) as usize;
        source = &source[4..];
        let mut states = Vec::with_capacity(states_len);
        for _ in 0..states_len {
            states.push(State::deserialize(source[0..16].try_into().unwrap()));
            source = &source[16..];
        }

        let (mapper, mut source) = CodeMapper::deserialize_from_slice_unchecked(source);

        let outputs_len = u32::from_le_bytes(source[0..4].try_into().unwrap()) as usize;
        source = &source[4..];
        let mut outputs = Vec::with_capacity(outputs_len);
        for _ in 0..outputs_len {
            outputs.push(Output::deserialize(source[0..12].try_into().unwrap()));
            source = &source[12..];
        }

        let match_kind = MatchKind::from(source[0]);
        let num_states_array: [u8; 4] = source[1..5].try_into().unwrap();
        let num_states = u32::from_le_bytes(num_states_array) as usize;

        (
            Self {
                states,
                mapper,
                outputs,
                match_kind,
                num_states,
            },
            &source[5..],
        )
    }

    /// # Safety
    ///
    /// `state_id` must be smaller than the length of states.
    #[allow(clippy::cast_possible_wrap)]
    #[inline(always)]
    unsafe fn get_child_index_unchecked(&self, state_id: u32, c: char) -> Option<u32> {
        let mapped_c = self.mapper.get(c)?;
        let base = self.states.get_unchecked(state_id as usize).base()?;
        let child_id = base ^ mapped_c;
        if self.states.get_unchecked(child_id as usize).check() == state_id {
            Some(child_id as u32)
        } else {
            None
        }
    }

    /// # Safety
    ///
    /// `state_id` must be smaller than the length of states.
    #[inline(always)]
    unsafe fn get_next_state_id_unchecked(&self, mut state_id: u32, c: char) -> u32 {
        loop {
            if let Some(state_id) = self.get_child_index_unchecked(state_id, c) {
                return state_id;
            }
            if state_id == ROOT_STATE_IDX {
                return ROOT_STATE_IDX;
            }
            state_id = self.states.get_unchecked(state_id as usize).fail();
        }
    }

    /// # Safety
    ///
    /// `state_id` must be smaller than the length of states.
    #[inline(always)]
    unsafe fn get_next_state_id_leftmost_unchecked(&self, mut state_id: u32, c: char) -> u32 {
        loop {
            if let Some(state_id) = self.get_child_index_unchecked(state_id, c) {
                return state_id;
            }
            if state_id == ROOT_STATE_IDX {
                return ROOT_STATE_IDX;
            }
            let fail_id = self.states.get_unchecked(state_id as usize).fail();
            if fail_id == DEAD_STATE_IDX {
                return DEAD_STATE_IDX;
            }
            state_id = fail_id;
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct State {
    base: u32,
    check: u32,
    fail: u32,
    output_pos: Option<NonZeroU32>,
}

impl Default for State {
    fn default() -> Self {
        Self {
            base: BASE_INVALID,
            check: DEAD_STATE_IDX,
            fail: DEAD_STATE_IDX,
            output_pos: None,
        }
    }
}

impl State {
    #[inline(always)]
    pub fn base(&self) -> Option<u32> {
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
    pub const fn output_pos(&self) -> Option<NonZeroU32> {
        self.output_pos
    }

    #[inline(always)]
    #[allow(dead_code)]
    pub fn set_base(&mut self, x: u32) {
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
    pub fn set_output_pos(&mut self, x: Option<NonZeroU32>) {
        self.output_pos = x;
    }

    #[inline(always)]
    fn serialize(&self) -> [u8; 16] {
        let mut result = [0; 16];
        result[0..4].copy_from_slice(&self.base.to_le_bytes());
        result[4..8].copy_from_slice(&self.check.to_le_bytes());
        result[8..12].copy_from_slice(&self.fail.to_le_bytes());
        result[12..16].copy_from_slice(&self.output_pos.map_or(0, NonZeroU32::get).to_le_bytes());
        result
    }

    #[inline(always)]
    fn deserialize(input: [u8; 16]) -> Self {
        Self {
            base: u32::from_le_bytes(input[0..4].try_into().unwrap()),
            check: u32::from_le_bytes(input[4..8].try_into().unwrap()),
            fail: u32::from_le_bytes(input[8..12].try_into().unwrap()),
            output_pos: NonZeroU32::new(u32::from_le_bytes(input[12..16].try_into().unwrap())),
        }
    }
}
