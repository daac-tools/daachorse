//! Bit-parallel (Shift-OR / Shift-Add) prefilters based on:
//!
//! > Ricardo Baeza-Yates and Gaston H. Gonnet.
//! > "A new approach to text searching."
//! > *Communications of the ACM*, 35(10): 74–82, 1992.
//! > <https://doi.org/10.1145/135239.135243>
//!
//! The key idea (Sections 1–2): represent the state of the search as a
//! bit-vector where each bit tracks whether a prefix of some pattern matches
//! the tail of the text at that offset.  Each input byte advances the state
//! with a single shift + bitwise-OR (or addition for the mismatch-tolerant
//! variant).  When the state indicates no pattern can possibly match, the
//! caller can skip ahead — providing a fast prefilter before running the
//! full automaton.
//!
//! Two variants are provided:
//!
//! * [`QgramPrefilter`] — uses 2-byte q-grams (bigrams) instead of raw
//!   characters so that the per-position bit budget scales to thousands of
//!   patterns without saturating a machine word.  A practical extension of
//!   the paper's bit-parallel philosophy for large pattern sets.
//!
//! * [`MultiQgramPrefilter`] — length-bucketed version that keeps each
//!   per-bucket filter sparse when pattern lengths vary widely.

use alloc::boxed::Box;
use alloc::vec::Vec;

// ---------------------------------------------------------------------------
// QgramPrefilter — bigram-based Shift-OR (practical extension for large sets)
// ---------------------------------------------------------------------------

/// Single-level bigram prefilter following the bit-parallel philosophy of
/// Baeza-Yates & Gonnet §3 (Shift-OR).
///
/// Instead of tracking one bit per *character* position (which would require
/// `sum(|pattern|)` bits ≤ word size), this prefilter tracks one bit per
/// *bigram* position.  A bigram `(byte[j], byte[j+1])` at offset `j` in a
/// pattern clears bit `j` in `b[bigram]`.  At search time the Shift-OR update
///
/// ```text
/// state = (state << 1) | b[input_bigram]
/// ```
///
/// keeps a sliding window of which bigram sequences *might* match.  When
/// `(state | end[bigram]) != 0xFF` a candidate region is signalled.
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
    /// Build a prefilter from exact-case byte patterns.
    ///
    /// Patterns shorter than 3 bytes are ignored.  Only the first 9 bytes
    /// of each pattern contribute (matching the 8-bit state width).
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

    /// Empty prefilter — never signals a candidate.
    pub fn empty() -> Self {
        Self {
            b: Box::new([0xFFu8; 65536]),
            end: Box::new([0xFFu8; 65536]),
        }
    }

    /// Build from raw byte arrays (useful for serialisation).
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
    /// Returns `Some(start_offset)` when a candidate region is found.
    /// Returns `None` when the entire buffer can be skipped.
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

    /// `true` when no patterns are registered (always skips).
    pub fn is_empty(&self) -> bool {
        self.b.iter().all(|&x| x == 0xFF)
    }
}

// ---------------------------------------------------------------------------
// MultiQgramPrefilter — length-bucketed variant for large pattern sets
// ---------------------------------------------------------------------------

/// A length-bucketed multi-level prefilter.
///
/// When thousands of patterns share the same bigram-position table, the
/// table saturates (every bigram bit is cleared).  Separating patterns by
/// length into independent buckets keeps each per-bucket filter sparse.
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
#[derive(Clone)]
pub struct MultiQgramPrefilter {
    filters: Box<[QgramPrefilter; 6]>,
}

impl MultiQgramPrefilter {
    /// Build from exact-case byte patterns, routing each to its length bucket.
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

    /// Build from a pre-built array of per-bucket filters.
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

    /// `true` when all buckets are empty.
    pub fn is_empty(&self) -> bool {
        self.filters.iter().all(|f| f.is_empty())
    }
}

// ---------------------------------------------------------------------------
// Exact character-level Shift-OR (Baeza-Yates & Gonnet §3, Figure 4)
// ---------------------------------------------------------------------------

/// Exact single-pattern Shift-OR matcher (Baeza-Yates & Gonnet §3, Figure 4).
///
/// A bit-vector `state` tracks which prefixes of the pattern match the
/// current suffix of the text.  The per-character table `T[x]` has bit *i*
/// cleared when `pattern[i] == x`.  The main loop is:
///
/// ```text
/// state = (state << 1) | T[text_byte];
/// if (state & end_mask) != end_mask { /* pattern ends here */ }
/// ```
///
/// Equivalent to `state < limit` in the paper's Figure 4 (page 226).
///
/// # Multi-pattern
///
/// For multiple patterns use [`QgramPrefilter`] or [`MultiQgramPrefilter`].
/// Packing multiple patterns into a single bit vector (coalesced approach,
/// page 77) causes false negatives due to shift‑based bit interference
/// between adjacent patterns.
#[derive(Clone, Debug)]
pub struct ShiftOrMask {
    t: [u64; 256],
    end_mask: u64,
    full_mask: u64,
}

impl ShiftOrMask {
    /// Build from a single exact-case pattern (Figure 4).
    ///
    /// Returns `None` if the pattern is empty or longer than 64 bytes.
    pub fn from_pattern(pat: &[u8]) -> Option<Self> {
        if pat.is_empty() || pat.len() > 64 {
            return None;
        }
        let m = pat.len();
        let full_mask = if m == 64 { !0u64 } else { (1u64 << m) - 1 };
        let end_mask = 1u64 << (m - 1);

        let mut t = [full_mask; 256];
        let mut bit = 1u64;
        for &ch in pat {
            t[ch as usize] &= !bit;
            bit <<= 1;
        }
        Some(Self { t, end_mask, full_mask })
    }

    /// Run Shift-OR over `data`, returning the number of matches.
    pub fn search(&self, data: &[u8]) -> usize {
        let mut state = self.full_mask;
        let mut matches = 0usize;
        for &ch in data {
            state = ((state << 1) | self.t[ch as usize]) & self.full_mask;
            if (state & self.end_mask) != self.end_mask {
                matches += 1;
            }
        }
        matches
    }

    /// Return the earliest offset where a match could start (prefilter hint).
    pub fn search_hint(&self, data: &[u8]) -> Option<usize> {
        let mut state = self.full_mask;
        for (i, &ch) in data.iter().enumerate() {
            state = ((state << 1) | self.t[ch as usize]) & self.full_mask;
            if (state & self.end_mask) != self.end_mask {
                let start = if i >= 63 { i - 63 } else { 0 };
                return Some(start);
            }
        }
        None
    }

    /// End mask — bit = 1 at the last character position of each pattern.
    pub fn end_mask(&self) -> u64 {
        self.end_mask
    }

    /// Full mask — bits covering all pattern positions + separators.
    pub fn full_mask(&self) -> u64 {
        self.full_mask
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- QgramPrefilter tests --

    #[test]
    fn qgram_empty_signals_nothing() {
        let pf = QgramPrefilter::empty();
        assert!(pf.is_empty());
        assert_eq!(pf.search(b"hello"), None);
    }

    #[test]
    fn qgram_single_pattern_is_found() {
        let patterns = vec![b"abc".to_vec()];
        let pf = QgramPrefilter::from_patterns(&patterns);
        assert!(!pf.is_empty());
        assert!(pf.search(b"xyz___abc___xyz").is_some());
    }

    #[test]
    fn qgram_unrelated_buffer_is_rejected() {
        let patterns = vec![b"xyz".to_vec()];
        let pf = QgramPrefilter::from_patterns(&patterns);
        assert_eq!(pf.search(b"aaaaaa"), None);
    }

    #[test]
    fn qgram_pattern_shorter_than_3_is_ignored() {
        let patterns = vec![b"ab".to_vec()];
        let pf = QgramPrefilter::from_patterns(&patterns);
        assert!(pf.is_empty());
    }

    // -- MultiQgramPrefilter tests --

    #[test]
    fn multilevel_finds_earliest_candidate() {
        let patterns = vec![b"short".to_vec(), b"a much longer pattern".to_vec()];
        let pf = MultiQgramPrefilter::from_patterns(&patterns);
        let buf = b"skip___a much longer pattern___short";
        let pos = pf.search(buf);
        assert!(pos.is_some());
        assert!(pos.unwrap() <= 7);
    }

    #[test]
    fn multilevel_empty_when_no_patterns() {
        let pf = MultiQgramPrefilter::from_patterns(&[]);
        assert!(pf.is_empty());
    }

    // -- ShiftOrMask tests (exact Figure 4 algorithm) --

    #[test]
    fn shift_or_single_pattern_exact_match() {
        // Example 1 from the paper: pattern "ababc" in text "abdabababc"
        let sor = ShiftOrMask::from_pattern(b"ababc").unwrap();
        let n = sor.search(b"abdabababc");
        assert_eq!(n, 1); // one occurrence
    }

    #[test]
    fn shift_or_single_pattern_no_match() {
        let sor = ShiftOrMask::from_pattern(b"xyz").unwrap();
        let n = sor.search(b"abcdefghij");
        assert_eq!(n, 0);
    }

    #[test]
    fn shift_or_single_pattern_multiple_matches() {
        let sor = ShiftOrMask::from_pattern(b"aa").unwrap();
        let n = sor.search(b"aaaab");
        // "aa" at offsets 0, 1, 2 → 3 overlapping matches (no match at offset 3: "ab")
        assert_eq!(n, 3);
    }

    #[test]
    fn shift_or_search_hint_rejects_empty_buffer() {
        let sor = ShiftOrMask::from_pattern(b"abc").unwrap();
        assert_eq!(sor.search_hint(b""), None);
    }

    #[test]
    fn shift_or_search_hint_finds_candidate() {
        let sor = ShiftOrMask::from_pattern(b"abc").unwrap();
        let hint = sor.search_hint(b"xyz_abc_xyz");
        assert!(hint.is_some());
    }

    #[test]
    fn shift_or_search_hint_rejects_unrelated() {
        let sor = ShiftOrMask::from_pattern(b"xyz").unwrap();
        assert_eq!(sor.search_hint(b"aaaaaaaaaa"), None);
    }

    #[test]
    fn shift_or_pattern_too_long_returns_none() {
        let long = vec![b'a'; 65];
        assert!(ShiftOrMask::from_pattern(&long).is_none());
    }

    #[test]
    fn shift_or_empty_pattern_returns_none() {
        assert!(ShiftOrMask::from_pattern(b"").is_none());
    }
}
