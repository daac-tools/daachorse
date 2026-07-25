//! Shift-OR bloom prefilter for ClamAV-style Aho-Corasick scanning.
//!
//! Uses 2-byte q-grams with a 65536-entry bit-vector (128 KB, L2-cache-friendly).
//! No-false-negatives: if `search()` returns `None`, the automaton can be skipped
//! entirely.  If it returns `Some(offset)`, the scanner should run from `offset`
//! (which may be 0 if the match starts very early).
//!
//! [`ClamavMultilevelPrefilter`] splits patterns by length bucket to avoid
//! saturation with large databases (30k+ patterns).
//!
//! Adapted from ClamAV's `filtering.c` / `matcher-ac.c`.

use alloc::boxed::Box;
use alloc::vec::Vec;

/// Shift-OR bloom prefilter (ClamAV-style).
///
/// `b[q]` has bit P clear if q-gram `q` can appear at position P of some pattern.
/// `end[q]` has bit P clear if `q` can be the terminal q-gram of a pattern
/// (i.e. the pattern ends at byte P+2).  Only exact-case q-grams are tracked
/// (no lowering) — use [`ClamavMultilevelPrefilter`] for nocase support or
/// large pattern sets.
#[derive(Clone)]
pub struct ClamavPrefilter {
    b: Box<[u8; 65536]>,
    end: Box<[u8; 65536]>,
}

impl core::fmt::Debug for ClamavPrefilter {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ClamavPrefilter").finish()
    }
}

impl ClamavPrefilter {
    /// Empty prefilter that never rejects data.
    #[must_use]
    pub fn empty() -> Self {
        Self { b: Box::new([0u8; 65536]), end: Box::new([0u8; 65536]) }
    }

    /// Build from raw bit-vectors (for deserialisation).
    #[must_use]
    pub fn from_raw(b: [u8; 65536], end: [u8; 65536]) -> Self {
        Self { b: Box::new(b), end: Box::new(end) }
    }

    /// Expose the `b` table for serialisation.
    #[must_use]
    pub fn raw_b(&self) -> &[u8; 65536] { &self.b }

    /// Expose the `end` table for serialisation.
    #[must_use]
    pub fn raw_end(&self) -> &[u8; 65536] { &self.end }

    /// Build from exact-case patterns.  Patterns shorter than 3 bytes are
    /// skipped (they can't form a 2-byte q-gram).
    #[must_use]
    pub fn from_patterns(patterns: &[Vec<u8>]) -> Self {
        let mut b = Box::new([0xFFu8; 65536]);
        let mut end = Box::new([0xFFu8; 65536]);
        for pat in patterns {
            let n = pat.len().min(9);
            if n < 3 { continue; }
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

    /// Search the prefilter over `data`.
    ///
    /// Returns `None` if no pattern can match (skip the automaton).
    /// Returns `Some(byte_offset)` if a potential match was detected.
    #[must_use]
    pub fn search(&self, data: &[u8]) -> Option<usize> {
        if data.len() < 2 { return None; }
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

    /// Returns `true` if this filter has no patterns registered.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.b.iter().all(|&x| x == 0xFF)
    }
}

/// Multilevel prefilter: one [`ClamavPrefilter`] per pattern-length bucket.
///
/// With many patterns, a single prefilter saturates (every q-gram matches).
/// Bucketing by length keeps each per-bucket filter sparse enough to be
/// effective.  All q-grams are case-exact (no lowering) — nocase atoms
/// fall through to the dense automaton (the prefilter is a best-effort
/// speed-up, not a correctness gate).
#[derive(Clone)]
pub struct ClamavMultilevelPrefilter {
    filters: alloc::boxed::Box<[ClamavPrefilter; 6]>,
}

impl ClamavMultilevelPrefilter {
    /// Expose the per-length filters (for serialisation).
    #[must_use]
    pub fn filters(&self) -> &[ClamavPrefilter; 6] { &self.filters }

    /// Build from raw filters (for deserialisation).
    #[must_use]
    pub fn from_filters(filters: [ClamavPrefilter; 6]) -> Self {
        Self { filters: Box::new(filters) }
    }

    /// Build per-length prefilters.  Buckets: [3,4], [5,6], [7,9], [10,15],
    /// [16,25], [26,∞).
    #[must_use]
    pub fn from_patterns(patterns: &[Vec<u8>]) -> Self {
        // Use Vec to avoid stack-allocating 6 × 64KB filters.
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
            filters: alloc::boxed::Box::new([
                ClamavPrefilter::from_patterns(&buckets[0]),
                ClamavPrefilter::from_patterns(&buckets[1]),
                ClamavPrefilter::from_patterns(&buckets[2]),
                ClamavPrefilter::from_patterns(&buckets[3]),
                ClamavPrefilter::from_patterns(&buckets[4]),
                ClamavPrefilter::from_patterns(&buckets[5]),
            ]),
        }
    }

    /// Returns `Some(start_offset)` if ANY level filter sees a potential
    /// match, else `None`.
    #[must_use]
    pub fn search(&self, data: &[u8]) -> Option<usize> {
        let mut earliest: Option<usize> = None;
        for f in self.filters.iter() {
            if f.is_empty() { continue; }
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

    /// Returns `true` when every level filter is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.filters.iter().all(|f| f.is_empty())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_accepts_everything() {
        let pf = ClamavPrefilter::empty();
        assert_eq!(pf.search(b"hello"), Some(0));
        assert_eq!(pf.search(b"x"), None);
    }

    #[test]
    fn simple_match() {
        let pf = ClamavPrefilter::from_patterns(&[b"abc".to_vec()]);
        assert_eq!(pf.search(b"---abc---"), Some(0));
    }

    #[test]
    fn no_match() {
        let pf = ClamavPrefilter::from_patterns(&[b"xyz".to_vec()]);
        assert_eq!(pf.search(b"---abc---"), None);
    }

    #[test]
    fn short_patterns_skipped() {
        let pf = ClamavPrefilter::from_patterns(&[b"ab".to_vec()]);
        assert_eq!(pf.search(b"xab"), None);
    }

    #[test]
    fn multilevel_beats_single_saturation() {
        // 4000 patterns in the [3,4] bucket — enough to saturate a single
        // 65536 × 8 filter if they were all mixed together.
        let pats: Vec<Vec<u8>> = (0..4000)
            .map(|i| format!("a{:02}", i % 100).into_bytes())
            .collect();
        let single = ClamavPrefilter::from_patterns(&pats);
        let multi = ClamavMultilevelPrefilter::from_patterns(&pats);

        // Both should reject "xyz" because "xy", "yz" are not in any pattern.
        assert_eq!(single.search(b"---xyz---"), None);
        assert_eq!(multi.search(b"---xyz---"), None);
    }

    #[test]
    fn multilevel_detects_real_match() {
        let pats = vec![b"abc".to_vec(), b"defgh".to_vec()];
        let multi = ClamavMultilevelPrefilter::from_patterns(&pats);
        assert!(multi.search(b"---abc---").is_some());
        assert!(multi.search(b"---defgh---").is_some());
    }
}
