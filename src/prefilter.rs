//! A match-candidate prefilter based on the SOG (Shift-Or with q-Grams) algorithm.
//!
//! The filter scans the haystack with a bit-parallel shift-or automaton over overlapping 2-grams
//! and reports positions where an occurrence of some pattern can start. Sections between
//! candidates are guaranteed to contain no occurrence, so the Aho-Corasick automaton can skip
//! them entirely while it stays in the root state. Candidates may be false positives; they are
//! simply verified by running the Aho-Corasick automaton as usual, so the filter never changes
//! match results.
//!
//! The algorithm is described in the following paper:
//!
//! > Leena Salmela, Jorma Tarhio, and Jari Kytöjoki.
//! > [Multipattern string matching with q-grams](https://doi.org/10.1145/1187436.1187438).
//! > *ACM Journal of Experimental Algorithmics*, 11, 2006.

use alloc::boxed::Box;
use alloc::vec::Vec;

use crate::errors::{DaachorseError, Result};
use crate::serializer::{Serializable, SerializableVec};

/// A SOG (Shift-Or with 2-Grams) prefilter.
#[derive(Clone, Eq, Hash, PartialEq)]
pub struct Prefilter {
    /// Maps a 2-gram to a bit vector whose `i`-th bit is 0 iff the 2-gram occurs at position `i`
    /// in the length-`window_len` prefix of some pattern.
    table: Box<[u8; Self::TABLE_LEN]>,
    /// The window length `m`: the length of the shortest pattern, capped at
    /// [`Prefilter::MAX_WINDOW_LEN`].
    window_len: u8,
    /// The bit at which a candidate is detected: `1 << (window_len - 2)`.
    hit_bit: u8,
}

impl Prefilter {
    /// The maximum window length: an 8-bit state supports up to `8 + 2 - 1` bytes because a window of
    /// `m` bytes yields `m - 1` overlapping 2-grams.
    pub const MAX_WINDOW_LEN: usize = 9;

    /// The minimum window length: a window must contain at least one 2-gram.
    pub const MIN_WINDOW_LEN: usize = 2;

    /// The number of 2-gram entries in the filter table.
    const TABLE_LEN: usize = 65536;

    /// The maximum estimated probability that a uniformly random position becomes a candidate.
    /// A table saturated with the 2-grams of too many patterns reports candidates almost
    /// everywhere and can hardly skip anything, so such a filter is not built. The estimate
    /// assumes random text and is thus optimistic on natural-language text; filters passing
    /// this check but not paying off in practice are disabled by [`PrefilterGate`] at run
    /// time.
    const MAX_EXPECTED_CANDIDATE_RATE: f64 = 1. / 16.;

    /// Returns the smallest position `>= start` where an occurrence of some pattern can start, or
    /// `haystack.len()` if there is none. The result may be a false positive, but there is never
    /// an occurrence starting in `start..result`.
    #[inline(always)]
    pub fn next_position(&self, haystack: &[u8], start: usize) -> usize {
        let Some(&(mut prev)) = haystack.get(start) else {
            return haystack.len();
        };
        let mut e = u8::MAX;
        for (i, &c) in haystack.iter().enumerate().skip(start + 1) {
            e = (e << 1) | self.table[usize::from(prev) << 8 | usize::from(c)];
            if e & self.hit_bit == 0 {
                return i + 1 - usize::from(self.window_len);
            }
            prev = c;
        }
        haystack.len()
    }

    /// Same as [`Prefilter::next_position`], but never returns a position in the middle of a
    /// UTF-8 character. Candidates starting with a continuation byte cannot be occurrences of
    /// character-wise patterns, so they are simply skipped.
    #[inline(always)]
    pub fn next_position_at_char_boundary(&self, haystack: &[u8], start: usize) -> usize {
        let mut pos = start;
        loop {
            let candidate_pos = self.next_position(haystack, pos);
            let Some(&first) = haystack.get(candidate_pos) else {
                return haystack.len();
            };
            if first & 0xc0 != 0x80 {
                return candidate_pos;
            }
            pos = candidate_pos + 1;
        }
    }

    /// Returns the heap size of the filter table in bytes.
    pub const fn heap_bytes(&self) -> usize {
        Self::TABLE_LEN
    }

    /// Estimates the probability that a uniformly random position in a random text becomes a
    /// candidate, as the product over all 2-gram positions of the fraction of 2-grams accepted
    /// there.
    fn expected_candidate_rate(&self) -> f64 {
        let mut zeros = [0u32; 8];
        for &bits in self.table.iter() {
            for (i, n) in zeros.iter_mut().enumerate() {
                *n += u32::from(bits >> i & 1 == 0);
            }
        }
        let mut rate = 1.;
        for &n in &zeros[..usize::from(self.window_len - 1)] {
            rate *= f64::from(n) / Self::TABLE_LEN as f64;
        }
        rate
    }
}

/// An incremental builder of [`Prefilter`]. The automaton builders feed it while the patterns
/// stream through them, so that no copy of the pattern set is kept for the filter.
pub struct PrefilterBuilder {
    /// The table under construction; see [`Prefilter::table`] for the semantics.
    table: Vec<u8>,
    /// The length of the shortest pattern added so far, or `usize::MAX` if none has been added.
    min_len: usize,
}

impl PrefilterBuilder {
    pub fn new() -> Self {
        Self {
            table: vec![u8::MAX; Prefilter::TABLE_LEN],
            min_len: usize::MAX,
        }
    }

    /// Registers the 2-grams of the pattern's window, which is the pattern itself capped at
    /// [`Prefilter::MAX_WINDOW_LEN`] bytes.
    pub fn add(&mut self, pattern: &[u8]) {
        self.min_len = self.min_len.min(pattern.len());
        let window = &pattern[..pattern.len().min(Prefilter::MAX_WINDOW_LEN)];
        for (i, gram) in window.windows(2).enumerate() {
            self.table[usize::from(gram[0]) << 8 | usize::from(gram[1])] &= !(1 << i);
        }
    }

    /// Builds the prefilter, or returns `None` when prefiltering cannot pay off: no pattern was
    /// added, some pattern is shorter than [`Prefilter::MIN_WINDOW_LEN`], or the table is too
    /// dense to filter out enough positions.
    pub fn build(self) -> Option<Prefilter> {
        // usize::MAX means that no pattern has been added.
        if self.min_len < Prefilter::MIN_WINDOW_LEN || self.min_len == usize::MAX {
            return None;
        }
        let window_len = self.min_len.min(Prefilter::MAX_WINDOW_LEN);
        let prefilter = Prefilter {
            table: self.table.into_boxed_slice().try_into().unwrap(),
            window_len: window_len.try_into().unwrap(),
            hit_bit: 1 << (window_len - 2),
        };
        (prefilter.expected_candidate_rate() <= Prefilter::MAX_EXPECTED_CANDIDATE_RATE)
            .then_some(prefilter)
    }
}

impl Serializable for Prefilter {
    fn serialize_to_vec(&self, dst: &mut Vec<u8>) {
        self.window_len.serialize_to_vec(dst);
        self.table.serialize_to_vec(dst);
    }

    fn deserialize_from_slice(src: &[u8]) -> Result<(Self, &[u8])> {
        let (window_len, src) = u8::deserialize_from_slice(src)?;
        if !(Self::MIN_WINDOW_LEN..=Self::MAX_WINDOW_LEN).contains(&usize::from(window_len)) {
            return Err(DaachorseError::invalid_automaton());
        }
        let (table, rest) = Box::<[u8; Self::TABLE_LEN]>::deserialize_from_slice(src)?;
        Ok((
            Self {
                table,
                window_len,
                hit_bit: 1 << (window_len - 2),
            },
            rest,
        ))
    }

    fn serialized_bytes() -> usize {
        u8::serialized_bytes() + Self::TABLE_LEN
    }
}

/// A runtime gate that disables prefiltering when it does not pay off on the current haystack.
///
/// Each iterator owns a gate. Every filter run records how many bytes it allowed the automaton to
/// skip, and once the average gain within a measurement window falls below a threshold, the gate
/// closes and the iterator falls back to plain automaton scanning.
#[derive(Clone)]
pub struct PrefilterGate {
    calls_in_window: u32,
    gain_in_window: usize,
    enabled: bool,
}

impl PrefilterGate {
    /// The number of filter runs in one measurement window of [`PrefilterGate`].
    const GATE_WINDOW_CALLS: u32 = 64;

    /// The minimum number of bytes that filter runs in one measurement window must have skipped in
    /// total. Below this, filtering is likely slower than plain automaton scanning.
    const GATE_MIN_WINDOW_GAIN: usize = 8 * Self::GATE_WINDOW_CALLS as usize;

    pub(crate) const fn new() -> Self {
        Self {
            calls_in_window: 0,
            gain_in_window: 0,
            enabled: true,
        }
    }

    #[inline(always)]
    pub(crate) const fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Records that a filter run let the automaton skip `gain` bytes.
    #[inline(always)]
    pub(crate) fn record(&mut self, gain: usize) {
        self.calls_in_window += 1;
        self.gain_in_window += gain;
        if self.calls_in_window == Self::GATE_WINDOW_CALLS {
            if self.gain_in_window < Self::GATE_MIN_WINDOW_GAIN {
                self.enabled = false;
            }
            self.calls_in_window = 0;
            self.gain_in_window = 0;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build(patterns: &[&[u8]]) -> Option<Prefilter> {
        let mut builder = PrefilterBuilder::new();
        for pattern in patterns {
            builder.add(pattern);
        }
        builder.build()
    }

    #[test]
    fn test_build_none_for_short_min_pattern() {
        assert!(build(&[b"aqua", b"a"]).is_none());
        assert!(build(&[b"aqua", b""]).is_none());
    }

    #[test]
    fn test_build_none_for_empty_pattern_set() {
        assert!(build(&[]).is_none());
    }

    #[test]
    fn test_build_none_when_table_saturated() {
        // All 2-byte patterns clear every table entry at position 0, making the expected
        // candidate rate 1.
        let mut builder = PrefilterBuilder::new();
        for a in 0..=255u8 {
            for b in 0..=255u8 {
                builder.add(&[a, b]);
            }
        }
        assert!(builder.build().is_none());
    }

    #[test]
    fn test_long_pattern_windows_are_capped() {
        // Patterns longer than MAX_WINDOW_LEN must not overflow the 8-bit table entries.
        let long = b"undine".repeat(20);
        let pf = build(&[&long, b"neovenezia"]).unwrap();
        let mut haystack = vec![b'x'; 50];
        haystack.extend_from_slice(&long);
        assert_eq!(pf.next_position(&haystack, 0), 50);
    }

    #[test]
    fn test_next_position_never_skips_occurrences() {
        let patterns: &[&[u8]] = &[b"aria", b"rari", b"iaria", b"ariaariaaria"];
        let pf = build(patterns).unwrap();
        // A real occurrence must never lie before the returned position.
        assert!(pf.next_position(b"iiiiariaii", 0) <= 4);
        // Exhaustively check all haystacks over {a, r, i} up to length 8: walking a haystack
        // candidate by candidate, no occurrence may start in a skipped section. Real
        // occurrences are thus never passed over, since a candidate section is skipped only
        // after being checked here.
        for len in 0..=8u32 {
            for haystack_code in 0..3usize.pow(len) {
                let mut code = haystack_code;
                let haystack: Vec<u8> = (0..len)
                    .map(|_| {
                        let c = b"ari"[code % 3];
                        code /= 3;
                        c
                    })
                    .collect();
                let mut pos = 0;
                while pos < haystack.len() {
                    let candidate = pf.next_position(&haystack, pos);
                    for start in pos..candidate {
                        for pattern in patterns {
                            assert_ne!(haystack.get(start..start + pattern.len()), Some(*pattern));
                        }
                    }
                    pos = candidate + 1;
                }
                assert_eq!(pf.next_position(&haystack, haystack.len()), haystack.len());
            }
        }
    }

    #[test]
    fn test_char_boundary_candidates() {
        let patterns: &[&[u8]] = &["火星猫".as_bytes(), b"undine"];
        let pf = build(patterns).unwrap();
        let haystack = "アリア社長は火星猫で、灯里はundineの見習いです".as_bytes();
        let mut pos = 0;
        while pos < haystack.len() {
            let candidate = pf.next_position_at_char_boundary(haystack, pos);
            if candidate == haystack.len() {
                break;
            }
            // Candidates are always on a character boundary.
            assert_ne!(haystack[candidate] & 0xc0, 0x80);
            for start in pos..candidate {
                for pattern in patterns {
                    assert_ne!(haystack.get(start..start + pattern.len()), Some(*pattern));
                }
            }
            pos = candidate + 1;
        }
    }

    #[test]
    fn test_serialize_roundtrip() {
        let pf = build(&[b"aqua", b"aria"]).unwrap();
        let mut data = vec![];
        pf.serialize_to_vec(&mut data);
        assert_eq!(data.len(), Prefilter::serialized_bytes());
        data.push(42);
        let (other, rest) = Prefilter::deserialize_from_slice(&data).unwrap();
        assert_eq!(&[42], rest);
        assert!(pf == other);
    }

    #[test]
    fn test_deserialize_rejects_invalid_data() {
        let pf = build(&[b"gondola"]).unwrap();
        let mut data = vec![];
        pf.serialize_to_vec(&mut data);
        // The window length must stay within its valid range.
        for bad_window_len in [0, 1, 10, u8::MAX] {
            let mut data = data.clone();
            data[0] = bad_window_len;
            assert!(Prefilter::deserialize_from_slice(&data).is_err());
        }
        // A truncated table must also be rejected.
        assert!(Prefilter::deserialize_from_slice(&data[..data.len() - 1]).is_err());
    }
}
