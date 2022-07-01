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
//! ## Example: Finding non-overlapped occurrences with standard matching
//!
//! If you do not want to allow positional overlap,
//! use [`DoubleArrayAhoCorasick::find_iter()`] instead.
//!
//! It performs the search on the Aho-Corasick automaton and
//! reports patterns first found in each iteration.
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
//!
//! ## Example: Building faster automaton on multibyte characters
//!
//! To build a faster automaton on multibyte characters, use [`CharwiseDoubleArrayAhoCorasick`]
//! instead.
//!
//! The standard version [`DoubleArrayAhoCorasick`] handles strings as UTF-8 sequences and defines
//! transition labels using byte values. On the other hand, [`CharwiseDoubleArrayAhoCorasick`] uses
//! code point values of Unicode, resulting in reducing the number of transitions and faster
//! matching.
//!
//! ```
//! use daachorse::CharwiseDoubleArrayAhoCorasick;
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

#![deny(missing_docs)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![no_std]

#[cfg(not(feature = "alloc"))]
compile_error!("`alloc` feature is currently required to build this crate");

#[cfg(target_pointer_width = "16")]
compile_error!("`target_pointer_width` must be larger than or equal to 32");

#[macro_use]
extern crate alloc;

mod build_helper;
pub mod bytewise;
pub mod charwise;
pub mod errors;
mod intpack;
mod nfa_builder;

use core::num::NonZeroU32;

use build_helper::BuildHelper;
pub use bytewise::{DoubleArrayAhoCorasick, DoubleArrayAhoCorasickBuilder};
pub use charwise::{CharwiseDoubleArrayAhoCorasick, CharwiseDoubleArrayAhoCorasickBuilder};

#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
struct Output {
    value: u32,
    length: u32,
    parent: Option<NonZeroU32>,
}

impl Output {
    #[inline(always)]
    pub const fn new(value: u32, length: u32, parent: Option<NonZeroU32>) -> Self {
        Self {
            value,
            length,
            parent,
        }
    }

    #[inline(always)]
    pub const fn value(self) -> u32 {
        self.value
    }

    #[inline(always)]
    pub const fn length(self) -> u32 {
        self.length
    }

    #[inline(always)]
    pub const fn parent(self) -> Option<NonZeroU32> {
        self.parent
    }

    #[inline(always)]
    fn serialize(&self) -> [u8; 12] {
        let mut result = [0; 12];
        result[0..4].copy_from_slice(&self.value.to_le_bytes());
        result[4..8].copy_from_slice(&self.length.to_le_bytes());
        result[8..12].copy_from_slice(&self.parent.map_or(0, NonZeroU32::get).to_le_bytes());
        result
    }

    #[inline(always)]
    fn deserialize(input: [u8; 12]) -> Self {
        Self {
            value: u32::from_le_bytes(input[0..4].try_into().unwrap()),
            length: u32::from_le_bytes(input[4..8].try_into().unwrap()),
            parent: NonZeroU32::new(u32::from_le_bytes(input[8..12].try_into().unwrap())),
        }
    }
}

/// Match result.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Match {
    length: usize,
    end: usize,
    value: usize,
}

impl Match {
    /// Starting position of the match.
    #[inline(always)]
    #[must_use]
    pub const fn start(&self) -> usize {
        self.end - self.length
    }

    /// Ending position of the match.
    #[inline(always)]
    #[must_use]
    pub const fn end(&self) -> usize {
        self.end
    }

    /// Value associated with the pattern.
    #[inline(always)]
    #[must_use]
    pub const fn value(&self) -> usize {
        self.value
    }
}

/// A search option of the Aho-Corasick automaton
/// specified in [`DoubleArrayAhoCorasickBuilder::match_kind`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
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
