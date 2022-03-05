//! # 🐎 daachorse: Double-Array Aho-Corasick
//!
//! A fast implementation of the Aho-Corasick algorithm
//! using the compact double-array data structure.
//!
//! ## Overview
//!
//! `daachorse` is a crate for fast multiple pattern matching using
//! the [Aho-Corasick algorithm](https://dl.acm.org/doi/10.1145/360825.360855),
//! running in linear time over the length of the input text.
//! For time- and memory-efficiency, the pattern match automaton is implemented using
//! the [compact double-array data structure](https://doi.org/10.1016/j.ipm.2006.04.004).
//! The data structure not only supports constant-time state-to-state traversal,
//! but also represents each state in a compact space of only 12 bytes.
//!
//! ## Example: Finding overlapped occurrences
//!
//! To search for all occurrences of registered patterns that allow for positional overlap in the
//! input text, use [`DoubleArrayAhoCorasick::find_overlapping_iter()`].
//!
//! When you use [`DoubleArrayAhoCorasick::new()`] for constraction,
//! unique identifiers are assigned to each pattern in the input order.
//! The match result has the byte positions of the occurrence and its identifier.
//!
//! ```
//! use daachorse::DoubleArrayAhoCorasick;
//!
//! let patterns = vec!["bcd", "ab", "a"];
//! let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
//!
//! let mut it = pma.find_overlapping_iter("abcd");
//!
//! let m = it.next().unwrap();
//! assert_eq!((0, 1, 2), (m.start(), m.end(), m.value()));
//!
//! let m = it.next().unwrap();
//! assert_eq!((0, 2, 1), (m.start(), m.end(), m.value()));
//!
//! let m = it.next().unwrap();
//! assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));
//!
//! assert_eq!(None, it.next());
//! ```
//!
//! ## Example: Finding non-overlapped occurrences with shortest matching
//!
//! If you do not want to allow positional overlap,
//! use [`DoubleArrayAhoCorasick::find_iter()`] instead.
//!
//! It reports the first pattern found in each iteration,
//! which is the shortest pattern starting from each search position.
//!
//! ```
//! use daachorse::DoubleArrayAhoCorasick;
//!
//! let patterns = vec!["bcd", "ab", "a"];
//! let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
//!
//! let mut it = pma.find_iter("abcd");
//!
//! let m = it.next().unwrap();
//! assert_eq!((0, 1, 2), (m.start(), m.end(), m.value()));
//!
//! let m = it.next().unwrap();
//! assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));
//!
//! assert_eq!(None, it.next());
//! ```
//!
//! ## Example: Finding non-overlapped occurrences with longest matching
//!
//! If you want to search for the longest pattern
//! without positional overlap in each iteration,
//! use [`DoubleArrayAhoCorasick::leftmost_find_iter()`] with specifying
//! [`MatchKind::LeftmostLongest`] in the construction.
//!
//! ```
//! use daachorse::{DoubleArrayAhoCorasickBuilder, MatchKind};
//!
//! let patterns = vec!["ab", "a", "abcd"];
//! let pma = DoubleArrayAhoCorasickBuilder::new()
//!           .match_kind(MatchKind::LeftmostLongest)
//!           .build(&patterns)
//!           .unwrap();
//!
//! let mut it = pma.leftmost_find_iter("abcd");
//!
//! let m = it.next().unwrap();
//! assert_eq!((0, 4, 2), (m.start(), m.end(), m.value()));
//!
//! assert_eq!(None, it.next());
//! ```
//!
//! ## Example: Finding non-overlapped occurrences with leftmost-first matching
//!
//! If you want to find the the earliest registered pattern
//! among ones starting from the search position,
//! use [`DoubleArrayAhoCorasick::leftmost_find_iter()`]
//! with specifying [`MatchKind::LeftmostFirst`].
//!
//! This is so-called *the leftmost first match*,
//! a bit tricky search option that is also supported in the
//! [aho-corasick](https://github.com/BurntSushi/aho-corasick) crate.
//! For example, in the following code,
//! `ab` is reported because it is the earliest registered one.
//!
//! ```
//! use daachorse::{DoubleArrayAhoCorasickBuilder, MatchKind};
//!
//! let patterns = vec!["ab", "a", "abcd"];
//! let pma = DoubleArrayAhoCorasickBuilder::new()
//!           .match_kind(MatchKind::LeftmostFirst)
//!           .build(&patterns)
//!           .unwrap();
//!
//! let mut it = pma.leftmost_find_iter("abcd");
//!
//! let m = it.next().unwrap();
//! assert_eq!((0, 2, 0), (m.start(), m.end(), m.value()));
//!
//! assert_eq!(None, it.next());
//! ```
//!
//! ## Example: Associating arbitrary values with patterns
//!
//! To build the automaton from pairs of a pattern and integer value instead of assigning
//! identifiers automatically, use [`DoubleArrayAhoCorasick::with_values()`].
//!
//! ```
//! use daachorse::DoubleArrayAhoCorasick;
//!
//! let patvals = vec![("bcd", 0), ("ab", 10), ("a", 20)];
//! let pma = DoubleArrayAhoCorasick::with_values(patvals).unwrap();
//!
//! let mut it = pma.find_overlapping_iter("abcd");
//!
//! let m = it.next().unwrap();
//! assert_eq!((0, 1, 20), (m.start(), m.end(), m.value()));
//!
//! let m = it.next().unwrap();
//! assert_eq!((0, 2, 10), (m.start(), m.end(), m.value()));
//!
//! let m = it.next().unwrap();
//! assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));
//!
//! assert_eq!(None, it.next());
//! ```

#![deny(missing_docs)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(target_pointer_width = "16")]
compile_error!("`target_pointer_width` must be larger than or equal to 32");

#[macro_use]
extern crate alloc;

mod builder;
pub mod charwise;
pub mod errors;
pub mod iter;
mod nfa_builder;

#[cfg(test)]
mod tests;

#[cfg(feature = "std")]
use std::io::{self, Read, Write};

use core::mem;

use alloc::vec::Vec;

pub use builder::DoubleArrayAhoCorasickBuilder;
use errors::Result;
use iter::{
    FindIterator, FindOverlappingIterator, FindOverlappingNoSuffixIterator, LestmostFindIterator,
    U8SliceIterator,
};

// The maximum BASE value used as an invalid value.
pub(crate) const BASE_INVALID: u32 = u32::MAX;
// The maximum output position value used as an invalid value.
pub(crate) const OUTPUT_POS_INVALID: u32 = u32::MAX;
// The maximum FAIL value.
pub(crate) const FAIL_MAX: u32 = 0xFF_FFFF;
// The mask value of FAIL for `State::fach`.
const FAIL_MASK: u32 = FAIL_MAX << 8;
// The mask value of CEHCK for `State::fach`.
const CHECK_MASK: u32 = 0xFF;
// The root index position.
pub(crate) const ROOT_STATE_IDX: u32 = 0;
// The dead index position.
pub(crate) const DEAD_STATE_IDX: u32 = 1;

#[derive(Clone, Copy, PartialEq, Eq)]
struct State {
    base: u32,
    fach: u32,
    output_pos: u32,
}

impl Default for State {
    fn default() -> Self {
        Self {
            base: BASE_INVALID,
            fach: 0,
            output_pos: OUTPUT_POS_INVALID,
        }
    }
}

impl State {
    #[inline(always)]
    pub fn base(&self) -> Option<u32> {
        Some(self.base).filter(|&x| x != BASE_INVALID)
    }

    #[inline(always)]
    pub const fn check(&self) -> u8 {
        #![allow(clippy::cast_possible_truncation)]
        (self.fach & 0xFF) as u8
    }

    #[inline(always)]
    pub const fn fail(&self) -> u32 {
        self.fach >> 8
    }

    #[inline(always)]
    pub fn output_pos(&self) -> Option<u32> {
        Some(self.output_pos).filter(|&x| x != OUTPUT_POS_INVALID)
    }

    #[inline(always)]
    pub fn set_base(&mut self, x: u32) {
        self.base = x;
    }

    #[inline(always)]
    pub fn set_check(&mut self, x: u8) {
        self.fach &= !CHECK_MASK;
        self.fach |= u32::from(x);
    }

    #[inline(always)]
    pub fn set_fail(&mut self, x: u32) {
        self.fach &= !FAIL_MASK;
        self.fach |= x << 8;
    }

    #[inline(always)]
    pub fn set_output_pos(&mut self, x: u32) {
        self.output_pos = x;
    }

    #[inline(always)]
    fn serialize(&self) -> [u8; 12] {
        let mut result = [0; 12];
        result[0..4].copy_from_slice(&self.base.to_le_bytes());
        result[4..8].copy_from_slice(&self.fach.to_le_bytes());
        result[8..12].copy_from_slice(&self.output_pos.to_le_bytes());
        result
    }

    #[inline(always)]
    fn deserialize(input: [u8; 12]) -> Self {
        Self {
            base: u32::from_le_bytes(input[0..4].try_into().unwrap()),
            fach: u32::from_le_bytes(input[4..8].try_into().unwrap()),
            output_pos: u32::from_le_bytes(input[8..12].try_into().unwrap()),
        }
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

#[derive(Copy, Clone, PartialEq, Eq)]
struct Output {
    value: u32,
    length: u32, // 1 bit is borrowed by a beginning flag
}

impl Output {
    #[inline(always)]
    pub fn new(value: u32, length: u32, is_begin: bool) -> Self {
        Self {
            value,
            length: (length << 1) | u32::from(is_begin),
        }
    }

    #[inline(always)]
    pub const fn value(self) -> u32 {
        self.value
    }

    #[inline(always)]
    pub const fn length(self) -> u32 {
        self.length >> 1
    }

    #[inline(always)]
    pub const fn is_begin(self) -> bool {
        self.length & 1 == 1
    }

    #[inline(always)]
    fn serialize(&self) -> [u8; 8] {
        let mut result = [0; 8];
        result[0..4].copy_from_slice(&self.value.to_le_bytes());
        result[4..8].copy_from_slice(&self.length.to_le_bytes());
        result
    }

    #[inline(always)]
    fn deserialize(input: [u8; 8]) -> Self {
        Self {
            value: u32::from_le_bytes(input[0..4].try_into().unwrap()),
            length: u32::from_le_bytes(input[4..8].try_into().unwrap()),
        }
    }
}

impl core::fmt::Debug for Output {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Output")
            .field("value", &self.value())
            .field("length", &self.length())
            .field("is_begin", &self.is_begin())
            .finish()
    }
}

/// Match result.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Match {
    length: usize,
    end: usize,
    value: usize,
}

impl Match {
    /// Starting position of the match.
    #[inline(always)]
    pub const fn start(&self) -> usize {
        self.end - self.length
    }

    /// Ending position of the match.
    #[inline(always)]
    pub const fn end(&self) -> usize {
        self.end
    }

    /// Value associated with the pattern.
    #[inline(always)]
    pub const fn value(&self) -> usize {
        self.value
    }
}

/// Fast multiple pattern match automaton implemented
/// with the Aho-Corasick algorithm and compact double-array data structure.
///
/// [`DoubleArrayAhoCorasick`] implements a pattern match automaton based on
/// the [Aho-Corasick algorithm](https://dl.acm.org/doi/10.1145/360825.360855),
/// supporting linear-time pattern matching.
/// The internal data structure employs
/// the [compact double-array structure](https://doi.org/10.1016/j.ipm.2006.04.004)
/// that is the fastest trie representation technique.
/// It supports constant-time state-to-state traversal,
/// allowing for very fast pattern matching.
/// Moreover, each state is represented in a compact space of only 12 bytes.
///
/// # Build instructions
///
/// [`DoubleArrayAhoCorasick`] supports the following two types of input data:
///
/// - [`DoubleArrayAhoCorasick::new`] builds an automaton from a set of byte strings
///    while assigning unique identifiers in the input order.
///
/// - [`DoubleArrayAhoCorasick::with_values`] builds an automaton
///    from a set of pairs of a byte string and a `u32` value.
///
/// # Limitations
///
/// For memory- and cache-efficiency, a FAIL pointer is represented in 24 bits.
/// Thus, if a very large pattern set is given,
/// [`DaachorseError`](errors::DaachorseError) will be reported.
pub struct DoubleArrayAhoCorasick {
    states: Vec<State>,
    outputs: Vec<Output>,
    match_kind: MatchKind,
    num_states: usize,
}

impl DoubleArrayAhoCorasick {
    /// Creates a new [`DoubleArrayAhoCorasick`] from input patterns.
    /// The value `i` is automatically associated with `patterns[i]`.
    ///
    /// # Arguments
    ///
    /// * `patterns` - List of patterns.
    ///
    /// # Errors
    ///
    /// [`DaachorseError`](errors::DaachorseError) is returned when
    ///   - `patterns` is empty,
    ///   - `patterns` contains entries of length zero,
    ///   - `patterns` contains duplicate entries,
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
    {
        DoubleArrayAhoCorasickBuilder::new().build(patterns)
    }

    /// Creates a new [`DoubleArrayAhoCorasick`] from input pattern-value pairs.
    ///
    /// # Arguments
    ///
    /// * `patvals` - List of pattern-value pairs, in which the value is of type `u32` and less than `u32::MAX`.
    ///
    /// # Errors
    ///
    /// [`DaachorseError`](errors::DaachorseError) is returned when
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
        I: IntoIterator<Item = (P, u32)>,
        P: AsRef<[u8]>,
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
    /// When you specify `MatchKind::{LeftmostFirst,LeftmostLongest}` in the construction,
    /// the iterator is not supported and the function will call panic!.
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
    pub fn find_iter<P>(&self, haystack: P) -> FindIterator<U8SliceIterator<P>>
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
    /// When you specify `MatchKind::{LeftmostFirst,LeftmostLongest}` in the construction,
    /// the iterator is not supported and the function will call panic!.
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
    pub fn find_iter_from_iter<P>(&self, haystack: P) -> FindIterator<P>
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
    /// When you specify `MatchKind::{LeftmostFirst,LeftmostLongest}` in the construction,
    /// the iterator is not supported and the function will call panic!.
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
    ) -> FindOverlappingIterator<U8SliceIterator<P>>
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
            output_pos: 0,
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
    /// When you specify `MatchKind::{LeftmostFirst,LeftmostLongest}` in the construction,
    /// the iterator is not supported and the function will call panic!.
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
    pub fn find_overlapping_iter_from_iter<P>(&self, haystack: P) -> FindOverlappingIterator<P>
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
            output_pos: 0,
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
    /// When you specify `MatchKind::{LeftmostFirst,LeftmostLongest}` in the construction,
    /// the iterator is not supported and the function will call panic!.
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
    ) -> FindOverlappingNoSuffixIterator<U8SliceIterator<P>>
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
    /// When you specify `MatchKind::{LeftmostFirst,LeftmostLongest}` in the construction,
    /// the iterator is not supported and the function will call panic!.
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
            haystack: haystack.enumerate(),
            state_id: ROOT_STATE_IDX,
        }
    }

    /// Returns an iterator of leftmost matches in the given haystack.
    ///
    /// The leftmost match greedily searches the longest possible match at each iteration, and
    /// the match results do not overlap positionally such as [`DoubleArrayAhoCorasick::find_iter()`].
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
    /// use daachorse::{DoubleArrayAhoCorasickBuilder, MatchKind};
    ///
    /// let patterns = vec!["ab", "a", "abcd"];
    /// let pma = DoubleArrayAhoCorasickBuilder::new()
    ///           .match_kind(MatchKind::LeftmostLongest)
    ///           .build(&patterns)
    ///           .unwrap();
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
    ///           .match_kind(MatchKind::LeftmostFirst)
    ///           .build(&patterns)
    ///           .unwrap();
    ///
    /// let mut it = pma.leftmost_find_iter("abcd");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 2, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn leftmost_find_iter<P>(&self, haystack: P) -> LestmostFindIterator<P>
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
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// assert_eq!(pma.heap_bytes(), 3104);
    /// ```
    pub fn heap_bytes(&self) -> usize {
        self.states.len() * mem::size_of::<State>() + self.outputs.len() * mem::size_of::<Output>()
    }

    /// Returns the total number of states this automaton has.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// assert_eq!(pma.num_states(), 6);
    /// ```
    pub const fn num_states(&self) -> usize {
        self.num_states
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
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let mut bytes = vec![];
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
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
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    /// let bytes = pma.serialize_to_vec();
    /// ```
    pub fn serialize_to_vec(&self) -> Vec<u8> {
        let mut result = Vec::with_capacity(
            mem::size_of::<u32>() * 3
                + mem::size_of::<u8>()
                + 12 * self.states.len()
                + 8 * self.outputs.len(),
        );
        result.extend_from_slice(&u32::try_from(self.states.len()).unwrap().to_le_bytes());
        for state in &self.states {
            result.extend_from_slice(&state.serialize());
        }
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
    /// [`DoubleArrayAhoCorasick::serialize()`] or
    /// [`DoubleArrayAhoCorasick::serialize_to_vec()`] functions.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::Read;
    ///
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let mut bytes = vec![];
    ///
    /// {
    ///     let patterns = vec!["bcd", "ab", "a"];
    ///     let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    ///     pma.serialize(&mut bytes).unwrap();
    /// }
    ///
    /// let pma = unsafe {
    ///     DoubleArrayAhoCorasick::deserialize_unchecked(&mut bytes.as_slice()).unwrap()
    /// };
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
            let mut state_array = [0; 12];
            rdr.read_exact(&mut state_array)?;
            states.push(State::deserialize(state_array));
        }
        let mut outputs_len_array = [0; 4];
        rdr.read_exact(&mut outputs_len_array)?;
        let outputs_len = u32::from_le_bytes(outputs_len_array) as usize;
        let mut outputs = Vec::with_capacity(outputs_len);
        for _ in 0..outputs_len {
            let mut output_array = [0; 8];
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
    /// # Safety
    ///
    /// The given data must be a correct automaton exported by
    /// [`DoubleArrayAhoCorasick::serialize()`] or
    /// [`DoubleArrayAhoCorasick::serialize_to_vec()`] functions.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    /// let bytes = pma.serialize_to_vec();
    ///
    /// let pma = unsafe {
    ///     DoubleArrayAhoCorasick::deserialize_from_slice_unchecked(&bytes)
    /// };
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
    pub unsafe fn deserialize_from_slice_unchecked(mut source: &[u8]) -> Self {
        let states_len = u32::from_le_bytes(source[0..4].try_into().unwrap()) as usize;
        source = &source[4..];
        let mut states = Vec::with_capacity(states_len);
        for _ in 0..states_len {
            states.push(State::deserialize(source[0..12].try_into().unwrap()));
            source = &source[12..];
        }
        let outputs_len = u32::from_le_bytes(source[0..4].try_into().unwrap()) as usize;
        source = &source[4..];
        let mut outputs = Vec::with_capacity(outputs_len);
        for _ in 0..outputs_len {
            outputs.push(Output::deserialize(source[0..8].try_into().unwrap()));
            source = &source[8..];
        }

        let match_kind = MatchKind::from(source[0]);
        let num_states_array: [u8; 4] = source[1..5].try_into().unwrap();
        let num_states = u32::from_le_bytes(num_states_array) as usize;

        Self {
            states,
            outputs,
            match_kind,
            num_states,
        }
    }

    /// # Safety
    ///
    /// `state_id` must be smaller than the length of states.
    #[inline(always)]
    unsafe fn get_child_index_unchecked(&self, state_id: u32, c: u8) -> Option<u32> {
        // child_idx is always smaller than states.len() because
        //  - states.len() is 256 * k for some integer k, and
        //  - base() returns smaller than states.len() when it is Some.
        self.states
            .get_unchecked(state_id as usize)
            .base()
            .and_then(|base| {
                let child_idx = base ^ u32::from(c);
                Some(child_idx).filter(|&x| self.states.get_unchecked(x as usize).check() == c)
            })
    }

    /// # Safety
    ///
    /// `state_id` must be smaller than the length of states.
    #[inline(always)]
    unsafe fn get_next_state_id_unchecked(&self, mut state_id: u32, c: u8) -> u32 {
        // In the loop, state_id is always set to values smaller than states.len(),
        // because get_child_index_unchecked() and fail() return such values.
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
    unsafe fn get_next_state_id_leftmost_unchecked(&self, mut state_id: u32, c: u8) -> u32 {
        // In the loop, state_id is always set to values smaller than states.len(),
        // because get_child_index_unchecked() and fail() return such values.
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

/// An search option of the Aho-Corasick automaton
/// specified in [`DoubleArrayAhoCorasickBuilder::match_kind`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum MatchKind {
    /// The standard match semantics, which enables
    /// [`find_iter()`](DoubleArrayAhoCorasick::find_iter()),\
    /// [`find_overlapping_iter()`](DoubleArrayAhoCorasick::find_overlapping_iter()), and
    /// [`find_overlapping_no_suffix_iter()`](DoubleArrayAhoCorasick::find_overlapping_no_suffix_iter()).
    /// Patterns are reported in the order that follows the normal behaviour of the Aho-Corasick
    /// algorithm.
    Standard = 0,

    /// The leftmost-longest match semantics, which enables
    /// [`leftmost_find_iter()`](DoubleArrayAhoCorasick::leftmost_find_iter()).
    /// When multiple patterns are started from the same positions, the longest pattern will be
    /// reported. For example, when matching patterns `ab|a|abcd` over `abcd`, `abcd` will be
    /// reported.
    LeftmostLongest = 1,

    /// The leftmost-first match semantics, which enables
    /// [`leftmost_find_iter()`](DoubleArrayAhoCorasick::leftmost_find_iter()).
    /// When multiple patterns are started from the same positions, the pattern that is registered
    /// earlier will be reported. For example, when matching patterns `ab|a|abcd` over `abcd`,
    /// `ab` will be reported.
    LeftmostFirst = 2,
}

impl MatchKind {
    fn is_standard(self) -> bool {
        self == Self::Standard
    }

    fn is_leftmost(self) -> bool {
        self == Self::LeftmostFirst || self == Self::LeftmostLongest
    }

    pub(crate) fn is_leftmost_first(self) -> bool {
        self == Self::LeftmostFirst
    }
}

impl From<u8> for MatchKind {
    fn from(src: u8) -> Self {
        match src {
            1 => Self::LeftmostLongest,
            2 => Self::LeftmostFirst,
            _ => Self::Standard,
        }
    }
}
