//! Shift-OR q-gram prefilter based on the bit-parallel approach described in:
//!
//! > Ricardo Baeza-Yates and Gaston H. Gonnet.
//! > "A new approach to text searching."
//! > *Communications of the ACM*, 35(10): 74–82, 1992.
//! > <https://doi.org/10.1145/135239.135243>
//!
//! The algorithm represents the state of a multi-pattern search as a bit-vector
//! and updates it using only shift and bitwise-logic operations per input byte.
//! When the state indicates that no pattern can match at any active position, the
//! scanner can skip ahead — providing a fast prefilter before running the full
//! automaton.
//!
//! # How it works
//!
//! For each 2-byte q-gram (bigram) we build a bitmask `b[q]` where bit P is 0
//! if that q-gram appears at byte-offset P inside any registered pattern.  The
//! companion mask `end[q]` has bit P clear if `q` can be the *terminal* bigram
//! of a pattern (i.e. the pattern ends at `P + 2`).
//!
//! At search time we maintain an 8-bit state:
//!
//! ```text
//! state = (state << 1) | b[bigram];
//! ```
//!
//! A candidate region is signalled when `(state | end[bigram]) != 0xFF` —
//! meaning some pattern's bigram sequence matches the current window of the
//! input.

use alloc::boxed::Box;
use alloc::vec::Vec;

/// A single-level Shift-OR prefilter that tracks 2-gram (bigram) positions.
///
/// `b[q]` has bit P clear if bigram `q` can appear at byte-offset P of some
/// pattern.  `end[q]` has bit P clear if `q` can be the terminal bigram of a
/// pattern (the pattern ends at `P + 2`).
///
/// The prefilter only handles exact-case bigrams — no case folding.  For
/// large or case-insensitive pattern sets use [`MultiQgramPrefilter`] which
/// buckets patterns by length to keep each per-bucket filter sparse.
///
/// Reference: Section 3 (Shift-OR) of Baeza-Yates & Gonnet (1992).
#[derive(Clone)]
pub struct QgramPrefilter {
    b: Box<[u8; 65536]>,
    end: Box<[u8; 65536]>,
}

impl core::fmt::Debug for QgramPrefilter {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("QgramPrefilter").finish()
    }
}

impl QgramPrefilter {
    /// Build a prefilter from a list of exact-case byte patterns.
    ///
    /// Patterns shorter than 3 bytes are ignored (they cannot form a bigram).
    /// Only the first 9 bytes of each pattern contribute to the bitmask,
    /// matching the 8-bit state width.
    pub fn from_patterns(patterns: &[Vec<u8>]) -> Self {
        let mut b = Box::new([0xFFu8; 65536]);
        let mut end = Box::new([0xFFu8; 65536]);
        for pat in patterns {
            let n = pat.len().min(9);
            if n < 3 {
                continue;
            }
            for j in 0..n - 1 {
                let q = u16::from_le_bytes([pat[j], pat[j + 1]]) as usize;
                b[q] &= !(1u8 << j);
                if j == n - 2 {
                    end[q] &= !(1u8 << j);
                }
            }
        }
        Self { b, end }
    }

    /// Create an empty prefilter (all bits set — never signals a candidate).
    pub fn empty() -> Self {
        Self {
            b: Box::new([0xFFu8; 65536]),
            end: Box::new([0xFFu8; 65536]),
        }
    }

    /// Create a prefilter from raw byte-arrays (useful for deserialisation).
    pub fn from_raw(b: [u8; 65536], end: [u8; 65536]) -> Self {
        Self {
            b: Box::new(b),
            end: Box::new(end),
        }
    }

    /// Access the raw bigram-position mask.
    pub fn raw_b(&self) -> &[u8; 65536] {
        &self.b
    }

    /// Access the raw terminal-bigram mask.
    pub fn raw_end(&self) -> &[u8; 65536] {
        &self.end
    }

    /// Run the Shift-OR filter over `data`.
    ///
    /// Returns `Some(start_offset)` when a candidate region is found, where
    /// `start_offset` is a conservative estimate of the earliest position at
    /// which a match could start.  Returns `None` when the entire buffer can
    /// be skipped.
    pub fn search(&self, data: &[u8]) -> Option<usize> {
        if data.len() < 2 {
            return None;
        }
        let mut state: u8 = 0xFF;
        for j in 0..data.len() - 1 {
            let q = u16::from_le_bytes([data[j], data[j + 1]]) as usize;
            state = (state << 1) | self.b[q];
            if (state | self.end[q]) != 0xFF {
                let start = if j + 2 >= 16 { j + 2 - 16 } else { 0 };
                return Some(start);
            }
        }
        None
    }

    /// Returns `true` if no patterns were registered (always signals skip).
    pub fn is_empty(&self) -> bool {
        self.b.iter().all(|&x| x == 0xFF)
    }
}

/// A length-bucketed multi-level prefilter.
///
/// When many patterns are registered, a single [`QgramPrefilter`] saturates
/// (every bigram appears somewhere, so it always signals a candidate).
/// Bucketing patterns by length keeps each per-bucket filter sparse enough to
/// be effective.
///
/// Six buckets are used:
///
/// | Bucket | Pattern length |
/// |--------|----------------|
/// | 0      | 3–4            |
/// | 1      | 5–6            |
/// | 2      | 7–9            |
/// | 3      | 10–15          |
/// | 4      | 16–25          |
/// | 5      | 26+            |
///
/// Reference: Baeza-Yates & Gonnet (1992) multi-pattern extension.
#[derive(Clone)]
pub struct MultiQgramPrefilter {
    filters: Box<[QgramPrefilter; 6]>,
}

impl MultiQgramPrefilter {
    /// Build from a list of exact-case byte patterns.
    ///
    /// Patterns are automatically routed to the appropriate length bucket.
    /// Patterns shorter than 3 bytes are ignored.
    pub fn from_patterns(patterns: &[Vec<u8>]) -> Self {
        let mut buckets: [Vec<Vec<u8>>; 6] = Default::default();
        for pat in patterns {
            let idx = match pat.len() {
                3..=4 => 0,
                5..=6 => 1,
                7..=9 => 2,
                10..=15 => 3,
                16..=25 => 4,
                _ => 5,
            };
            buckets[idx].push(pat.clone());
        }
        Self {
            filters: Box::new([
                QgramPrefilter::from_patterns(&buckets[0]),
                QgramPrefilter::from_patterns(&buckets[1]),
                QgramPrefilter::from_patterns(&buckets[2]),
                QgramPrefilter::from_patterns(&buckets[3]),
                QgramPrefilter::from_patterns(&buckets[4]),
                QgramPrefilter::from_patterns(&buckets[5]),
            ]),
        }
    }

    /// Create from a pre-built array of per-bucket filters.
    pub fn from_filters(filters: [QgramPrefilter; 6]) -> Self {
        Self {
            filters: Box::new(filters),
        }
    }

    /// Access the per-bucket filters.
    pub fn filters(&self) -> &[QgramPrefilter; 6] {
        &self.filters
    }

    /// Run all per-bucket filters and return the earliest candidate position.
    pub fn search(&self, data: &[u8]) -> Option<usize> {
        let mut earliest: Option<usize> = None;
        for f in self.filters.iter() {
            if f.is_empty() {
                continue;
            }
            if let Some(start) = f.search(data) {
                match earliest {
                    None => earliest = Some(start),
                    Some(e) if start < e => earliest = Some(start),
                    _ => {}
                }
            }
        }
        earliest
    }

    /// Returns `true` if all buckets are empty (always skip).
    pub fn is_empty(&self) -> bool {
        self.filters.iter().all(|f| f.is_empty())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_prefilter_signals_nothing() {
        let pf = QgramPrefilter::empty();
        assert!(pf.is_empty());
        assert_eq!(pf.search(b"hello"), None);
    }

    #[test]
    fn single_pattern_is_found() {
        let patterns = vec![b"abc".to_vec()];
        let pf = QgramPrefilter::from_patterns(&patterns);
        assert!(!pf.is_empty());
        assert!(pf.search(b"xyz___abc___xyz").is_some());
    }

    #[test]
    fn unrelated_buffer_is_rejected() {
        let patterns = vec![b"xyz".to_vec()];
        let pf = QgramPrefilter::from_patterns(&patterns);
        assert_eq!(pf.search(b"aaaaaa"), None);
    }

    #[test]
    fn pattern_shorter_than_3_is_ignored() {
        let patterns = vec![b"ab".to_vec()];
        let pf = QgramPrefilter::from_patterns(&patterns);
        assert!(pf.is_empty());
    }

    #[test]
    fn multilevel_finds_earliest_candidate() {
        let patterns = vec![b"short".to_vec(), b"a much longer pattern".to_vec()];
        let pf = MultiQgramPrefilter::from_patterns(&patterns);
        let buf = b"skip___a much longer pattern___short";
        let pos = pf.search(buf);
        assert!(pos.is_some());
        assert!(pos.unwrap() <= 7); // should find the longer pattern's region
    }

    #[test]
    fn multilevel_empty_when_no_patterns() {
        let pf = MultiQgramPrefilter::from_patterns(&[]);
        assert!(pf.is_empty());
    }
}
