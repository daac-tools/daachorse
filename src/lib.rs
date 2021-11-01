//! # 🐎 Daac Horse: Double-Array Aho-Corasick
//!
//! A fast implementation of the Aho-Corasick algorithm using Double-Array Trie.
//!
//! ## Examples
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
//! assert_eq!((0, 1, 2), (m.start(), m.end(), m.pattern()));
//!
//! let m = it.next().unwrap();
//! assert_eq!((0, 2, 1), (m.start(), m.end(), m.pattern()));
//!
//! let m = it.next().unwrap();
//! assert_eq!((1, 4, 0), (m.start(), m.end(), m.pattern()));
//!
//! assert_eq!(None, it.next());
//! ```

mod builder;
pub mod errors;

use std::io;

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

pub use builder::DoubleArrayAhoCorasickBuilder;
use errors::DaachorseError;

// The maximum ID of a pattern used as an invalid value.
pub(crate) const PATTERN_ID_INVALID: u32 = std::u32::MAX;
// The maximum length of a pattern used as an invalid value.
pub(crate) const PATTERN_LEN_INVALID: u32 = std::u32::MAX >> 1;
// The maximum BASE value used as an invalid value.
pub(crate) const BASE_INVALID: u32 = std::u32::MAX;
// The maximum FAIL value used as an invalid value.
pub(crate) const FAIL_INVALID: u32 = std::u32::MAX >> 8;
// The maximum output position value used as an invalid value.
pub(crate) const OUTPOS_INVALID: u32 = std::u32::MAX;
// The maximum state index used as an invalid value.
pub(crate) const STATE_IDX_INVALID: u32 = std::u32::MAX;
// The length of each double-array block.
pub(crate) const BLOCK_LEN: usize = 256;
// The number of last blocks to be searched in `DoubleArrayAhoCorasickBuilder::find_base`.
pub(crate) const FREE_BLOCKS: usize = 16;
// The number of last states (or elements) to be searched in `DoubleArrayAhoCorasickBuilder::find_base`.
pub(crate) const FREE_STATES: usize = BLOCK_LEN * FREE_BLOCKS;

#[derive(Clone, Copy)]
struct State {
    base: u32,
    fach: u32,
    output_pos: u32,
}

impl Default for State {
    fn default() -> Self {
        Self {
            base: BASE_INVALID,
            fach: FAIL_INVALID << 8,
            output_pos: OUTPOS_INVALID,
        }
    }
}

impl State {
    #[inline(always)]
    pub const fn base(&self) -> u32 {
        self.base
    }

    #[inline(always)]
    pub const fn check(&self) -> u8 {
        (self.fach & 0xFF) as u8
    }

    #[inline(always)]
    pub const fn fail(&self) -> u32 {
        self.fach >> 8
    }

    #[inline(always)]
    pub const fn output_pos(&self) -> u32 {
        self.output_pos
    }

    #[inline(always)]
    pub fn set_base(&mut self, x: u32) {
        self.base = x;
    }

    #[inline(always)]
    pub fn set_check(&mut self, x: u8) {
        self.fach = (self.base() << 8) | x as u32;
    }

    #[inline(always)]
    pub fn set_fail(&mut self, x: u32) {
        self.fach = (x << 8) | self.check() as u32;
    }

    #[inline(always)]
    pub fn set_output_pos(&mut self, x: u32) {
        self.output_pos = x;
    }

    /// Serializes the state.
    pub fn serialize<W>(&self, mut writer: W) -> io::Result<()>
    where
        W: io::Write,
    {
        writer.write_u32::<LittleEndian>(self.base)?;
        writer.write_u32::<LittleEndian>(self.fach)?;
        writer.write_u32::<LittleEndian>(self.output_pos)?;
        Ok(())
    }

    /// Deserializes the state.
    pub fn deserialize<R>(mut reader: R) -> io::Result<Self>
    where
        R: io::Read,
    {
        let base = reader.read_u32::<LittleEndian>()?;
        let fach = reader.read_u32::<LittleEndian>()?;
        let output_pos = reader.read_u32::<LittleEndian>()?;
        Ok(Self {
            base,
            fach,
            output_pos,
        })
    }
}

#[derive(Copy, Clone)]
struct Output(u64);

impl Output {
    #[inline(always)]
    pub const fn new(pattern_id: u32, pattern_len: u32, is_begin: bool) -> Self {
        Self((pattern_id as u64) << 32 | (pattern_len as u64) << 1 | is_begin as u64)
    }

    #[inline(always)]
    pub const fn pattern_id(&self) -> u32 {
        (self.0 >> 32) as u32
    }

    #[inline(always)]
    pub const fn pattern_len(&self) -> u32 {
        ((self.0 >> 1) as u32) & PATTERN_LEN_INVALID
    }

    #[inline(always)]
    pub const fn is_begin(&self) -> bool {
        self.0 & 1 == 1
    }

    #[inline]
    pub const fn from_u64(x: u64) -> Self {
        Self(x)
    }

    #[inline]
    pub const fn as_u64(&self) -> u64 {
        self.0
    }
}

/// Match result.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Match {
    length: usize,
    end: usize,
    pattern: usize,
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

    /// Pattern ID.
    #[inline(always)]
    pub const fn pattern(&self) -> usize {
        self.pattern
    }
}

/// Iterator created by [`DoubleArrayAhoCorasick::find_iter()`].
pub struct FindIterator<'a, P>
where
    P: AsRef<[u8]>,
{
    pma: &'a DoubleArrayAhoCorasick,
    haystack: P,
    pos: usize,
}

impl<'a, P> Iterator for FindIterator<'a, P>
where
    P: AsRef<[u8]>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let mut state_id = 0;
        let haystack = self.haystack.as_ref();
        for (pos, &c) in haystack.iter().enumerate().skip(self.pos) {
            state_id = self.pma.get_next_state_id(state_id, c);
            let out_pos = unsafe { self.pma.states.get_unchecked(state_id).output_pos() } as usize;
            if let Some(out) = self.pma.outputs.get(out_pos) {
                self.pos = pos + 1;
                return Some(Match {
                    length: out.pattern_len() as usize,
                    end: self.pos,
                    pattern: out.pattern_id() as usize,
                });
            }
        }
        self.pos = haystack.len();
        None
    }
}

/// Iterator created by [`DoubleArrayAhoCorasick::find_overlapping_iter()`].
pub struct FindOverlappingIterator<'a, P>
where
    P: AsRef<[u8]>,
{
    pma: &'a DoubleArrayAhoCorasick,
    haystack: P,
    state_id: usize,
    pos: usize,
    out_pos: usize,
}

impl<'a, P> Iterator for FindOverlappingIterator<'a, P>
where
    P: AsRef<[u8]>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let out = unsafe { self.pma.outputs.get_unchecked(self.out_pos) };
        if !out.is_begin() {
            self.out_pos += 1;
            return Some(Match {
                length: out.pattern_len() as usize,
                end: self.pos,
                pattern: out.pattern_id() as usize,
            });
        }
        let haystack = self.haystack.as_ref();
        for (pos, &c) in haystack.iter().enumerate().skip(self.pos) {
            self.state_id = self.pma.get_next_state_id(self.state_id, c);
            let out_pos = unsafe { self.pma.states.get_unchecked(self.state_id).output_pos() };
            if out_pos != OUTPOS_INVALID {
                self.pos = pos + 1;
                self.out_pos = out_pos as usize + 1;
                let out = unsafe { self.pma.outputs.get_unchecked(out_pos as usize) };
                return Some(Match {
                    length: out.pattern_len() as usize,
                    end: self.pos,
                    pattern: out.pattern_id() as usize,
                });
            }
        }
        self.pos = haystack.len();
        None
    }
}

/// Iterator created by [`DoubleArrayAhoCorasick::find_overlapping_no_suffix_iter()`].
pub struct FindOverlappingNoSuffixIterator<'a, P>
where
    P: AsRef<[u8]>,
{
    pma: &'a DoubleArrayAhoCorasick,
    haystack: P,
    state_id: usize,
    pos: usize,
}

impl<'a, P> Iterator for FindOverlappingNoSuffixIterator<'a, P>
where
    P: AsRef<[u8]>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let haystack = self.haystack.as_ref();
        for (pos, &c) in haystack.iter().enumerate().skip(self.pos) {
            self.state_id = self.pma.get_next_state_id(self.state_id, c);
            let out_pos = unsafe { self.pma.states.get_unchecked(self.state_id).output_pos() };
            if out_pos != OUTPOS_INVALID {
                self.pos = pos + 1;
                let out = unsafe { self.pma.outputs.get_unchecked(out_pos as usize) };
                return Some(Match {
                    length: out.pattern_len() as usize,
                    end: self.pos,
                    pattern: out.pattern_id() as usize,
                });
            }
        }
        self.pos = haystack.len();
        None
    }
}

/// Pattern match automaton implemented with the Aho-Corasick algorithm and Double-Array.
pub struct DoubleArrayAhoCorasick {
    states: Vec<State>,
    outputs: Vec<Output>,
}

impl DoubleArrayAhoCorasick {
    /// Creates a new [`DoubleArrayAhoCorasick`].
    ///
    /// # Arguments
    ///
    /// * `patterns` - List of patterns.
    ///
    /// # Errors
    ///
    /// [`errors::DuplicatePatternError`] is returned when `patterns` contains duplicate entries.
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
    /// assert_eq!((0, 1, 2), (m.start(), m.end(), m.pattern()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.pattern()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn new<I, P>(patterns: I) -> Result<Self, DaachorseError>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<[u8]>,
    {
        DoubleArrayAhoCorasickBuilder::new(65536)?.build(patterns)
    }

    /// Returns an iterator of non-overlapping matches in the given haystack.
    ///
    /// # Arguments
    ///
    /// * `haystack` - String to search for.
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
    /// assert_eq!((0, 1, 2), (m.start(), m.end(), m.pattern()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.pattern()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn find_iter<P>(&self, haystack: P) -> FindIterator<P>
    where
        P: AsRef<[u8]>,
    {
        FindIterator {
            pma: self,
            haystack,
            pos: 0,
        }
    }

    /// Returns an iterator of overlapping matches in the given haystack.
    ///
    /// # Arguments
    ///
    /// * `haystack` - String to search for.
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
    /// assert_eq!((0, 1, 2), (m.start(), m.end(), m.pattern()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 2, 1), (m.start(), m.end(), m.pattern()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.pattern()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn find_overlapping_iter<P>(&self, haystack: P) -> FindOverlappingIterator<P>
    where
        P: AsRef<[u8]>,
    {
        FindOverlappingIterator {
            pma: self,
            haystack,
            state_id: 0,
            pos: 0,
            out_pos: 0,
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
    /// assert_eq!((0, 3, 2), (m.start(), m.end(), m.pattern()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.pattern()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn find_overlapping_no_suffix_iter<P>(
        &self,
        haystack: P,
    ) -> FindOverlappingNoSuffixIterator<P>
    where
        P: AsRef<[u8]>,
    {
        FindOverlappingNoSuffixIterator {
            pma: self,
            haystack,
            state_id: 0,
            pos: 0,
        }
    }

    /// Serializes the automaton into the output stream.
    ///
    /// # Arguments
    ///
    /// * `writer` - Output stream.
    ///
    /// # Errors
    ///
    /// `std::io::Error` is returned if it fails to write the data.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut buffer = vec![];
    /// pma.serialize(&mut buffer).unwrap();
    /// ```
    #[doc(hidden)]
    pub fn serialize<W>(&self, mut writer: W) -> io::Result<()>
    where
        W: io::Write,
    {
        writer.write_u64::<LittleEndian>(self.states.len() as u64)?;
        for &s in &self.states {
            s.serialize(&mut writer)?;
        }
        writer.write_u64::<LittleEndian>(self.outputs.len() as u64)?;
        for &x in &self.outputs {
            writer.write_u64::<LittleEndian>(x.as_u64())?;
        }
        Ok(())
    }

    /// Deserializes the automaton from the input stream.
    ///
    /// # Arguments
    ///
    /// * `reader` - Input stream.
    ///
    /// # Errors
    ///
    /// `std::io::Error` is returned if it fails to read the data.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// let mut buffer = vec![];
    /// pma.serialize(&mut buffer).unwrap();
    ///
    /// let other = DoubleArrayAhoCorasick::deserialize(&buffer[..]).unwrap();
    /// ```
    #[doc(hidden)]
    pub fn deserialize<R>(mut reader: R) -> io::Result<Self>
    where
        R: io::Read,
    {
        let states = {
            let len = reader.read_u64::<LittleEndian>()? as usize;
            let mut states = Vec::with_capacity(len);
            for _ in 0..len {
                states.push(State::deserialize(&mut reader)?);
            }
            states
        };
        let outputs = {
            let len = reader.read_u64::<LittleEndian>()? as usize;
            let mut outputs = Vec::with_capacity(len);
            for _ in 0..len {
                outputs.push(Output::from_u64(reader.read_u64::<LittleEndian>()?));
            }
            outputs
        };
        Ok(Self { states, outputs })
    }

    #[inline(always)]
    fn get_child_index(&self, state_id: usize, c: u8) -> Option<usize> {
        let base = unsafe { self.states.get_unchecked(state_id).base() };
        if base == BASE_INVALID {
            return None;
        }
        let child_idx = (base ^ c as u32) as usize;
        if unsafe { self.states.get_unchecked(child_idx).check() } == c {
            Some(child_idx)
        } else {
            None
        }
    }

    #[inline(always)]
    fn get_next_state_id(&self, mut state_id: usize, c: u8) -> usize {
        loop {
            if let Some(state_id) = self.get_child_index(state_id, c) {
                return state_id;
            }
            if state_id == 0 {
                return 0;
            }
            state_id = unsafe { self.states.get_unchecked(state_id).fail() } as usize;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::collections::HashSet;

    use rand::Rng;

    fn generate_random_string(size: usize) -> String {
        const CHARSET: &[u8] = b"random";
        let mut rng = rand::thread_rng();

        (0..size)
            .map(|_| {
                let idx = rng.gen_range(0..CHARSET.len());
                CHARSET[idx] as char
            })
            .collect()
    }

    fn generate_random_binary_string(size: usize) -> Vec<u8> {
        let mut rng = rand::thread_rng();
        (0..size).map(|_| rng.gen_range(0..=255)).collect()
    }

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
        let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();

        let base_expected = vec![
            3,
            BASE_INVALID,
            7,
            4,
            BASE_INVALID,
            BASE_INVALID,
            BASE_INVALID,
        ];
        let check_expected = vec![0, 2, 1, 0, 0, 2, 2];
        //                        ^  ^  ^  ^  ^  ^  ^
        //              node_id=  0  3  2  1  4  6  5
        let fail_expected = vec![0, 0, 0, 0, 3, 1, 1];

        let pma_base: Vec<_> = pma.states[0..7].iter().map(|state| state.base()).collect();
        let pma_check: Vec<_> = pma.states[0..7].iter().map(|state| state.check()).collect();
        let pma_fail: Vec<_> = pma.states[0..7].iter().map(|state| state.fail()).collect();

        assert_eq!(base_expected, pma_base);
        assert_eq!(check_expected, pma_check);
        assert_eq!(fail_expected, pma_fail);
    }

    #[test]
    fn test_find_iter_random() {
        for _ in 0..100 {
            let mut patterns = HashSet::new();
            for _ in 0..100 {
                patterns.insert(generate_random_string(4));
            }
            let haystack = generate_random_string(100);

            // naive pattern match
            let mut expected = HashSet::new();
            let mut pos = 0;
            while pos <= haystack.len() - 4 {
                if patterns.contains(&haystack[pos..pos + 4]) {
                    expected.insert((pos, pos + 4, haystack[pos..pos + 4].to_string()));
                    pos += 3;
                }
                pos += 1;
            }

            // daachorse
            let mut actual = HashSet::new();
            let patterns_vec: Vec<_> = patterns.into_iter().collect();
            let pma = DoubleArrayAhoCorasick::new(&patterns_vec).unwrap();
            for m in pma.find_iter(&haystack) {
                actual.insert((m.start(), m.end(), patterns_vec[m.pattern()].clone()));
            }
            eprintln!("{}", haystack);
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_find_iter_binary_random() {
        for _ in 0..100 {
            let mut patterns = HashSet::new();
            for _ in 0..100 {
                patterns.insert(generate_random_binary_string(4));
            }
            let haystack = generate_random_binary_string(100);

            // naive pattern match
            let mut expected = HashSet::new();
            let mut pos = 0;
            while pos <= haystack.len() - 4 {
                if patterns.contains(&haystack[pos..pos + 4]) {
                    expected.insert((pos, pos + 4, haystack[pos..pos + 4].to_vec()));
                    pos += 3;
                }
                pos += 1;
            }

            // daachorse
            let mut actual = HashSet::new();
            let patterns_vec: Vec<_> = patterns.into_iter().collect();
            let pma = DoubleArrayAhoCorasick::new(&patterns_vec).unwrap();
            for m in pma.find_iter(&haystack) {
                actual.insert((m.start(), m.end(), patterns_vec[m.pattern()].clone()));
            }
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_find_overlapping_iter_random() {
        for _ in 0..100 {
            let mut patterns = HashSet::new();
            for _ in 0..6 {
                patterns.insert(generate_random_string(1));
            }
            for _ in 0..20 {
                patterns.insert(generate_random_string(2));
            }
            for _ in 0..50 {
                patterns.insert(generate_random_string(3));
            }
            for _ in 0..100 {
                patterns.insert(generate_random_string(4));
            }
            let haystack = generate_random_string(100);

            // naive pattern match
            let mut expected = HashSet::new();
            for i in 0..4 {
                for pos in 0..haystack.len() - i {
                    if patterns.contains(&haystack[pos..pos + i + 1]) {
                        expected.insert((pos, pos + i + 1, haystack[pos..pos + i + 1].to_string()));
                    }
                }
            }

            // daachorse
            let mut actual = HashSet::new();
            let patterns_vec: Vec<_> = patterns.into_iter().collect();
            let pma = DoubleArrayAhoCorasick::new(&patterns_vec).unwrap();
            for m in pma.find_overlapping_iter(&haystack) {
                actual.insert((m.start(), m.end(), patterns_vec[m.pattern()].clone()));
            }
            eprintln!("{}", haystack);
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_find_overlapping_iter_binary_random() {
        for _ in 0..100 {
            let mut patterns = HashSet::new();
            for _ in 0..6 {
                patterns.insert(generate_random_binary_string(1));
            }
            for _ in 0..20 {
                patterns.insert(generate_random_binary_string(2));
            }
            for _ in 0..50 {
                patterns.insert(generate_random_binary_string(3));
            }
            for _ in 0..100 {
                patterns.insert(generate_random_binary_string(4));
            }
            let haystack = generate_random_binary_string(100);

            // naive pattern match
            let mut expected = HashSet::new();
            for i in 0..4 {
                for pos in 0..haystack.len() - i {
                    if patterns.contains(&haystack[pos..pos + i + 1]) {
                        expected.insert((pos, pos + i + 1, haystack[pos..pos + i + 1].to_vec()));
                    }
                }
            }

            // daachorse
            let mut actual = HashSet::new();
            let patterns_vec: Vec<_> = patterns.into_iter().collect();
            let pma = DoubleArrayAhoCorasick::new(&patterns_vec).unwrap();
            for m in pma.find_overlapping_iter(&haystack) {
                actual.insert((m.start(), m.end(), patterns_vec[m.pattern()].clone()));
            }
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_dump_root_state() {
        let patterns: Vec<Vec<u8>> = (1..=255).map(|c| vec![c]).collect();
        let pma = DoubleArrayAhoCorasick::new(&patterns).unwrap();
        assert!(pma.get_child_index(0, 0).is_none());
        for c in 1..=255 {
            assert_eq!(pma.get_child_index(0, c).unwrap(), c as usize);
        }
    }

    #[test]
    fn test_dump_states_random() {
        for _ in 0..100 {
            let mut patterns = HashSet::new();
            for _ in 0..100 {
                patterns.insert(generate_random_string(8));
            }
            let patterns_vec: Vec<_> = patterns.into_iter().collect();
            let pma = DoubleArrayAhoCorasick::new(&patterns_vec).unwrap();

            let mut visitor = vec![0 as usize];
            let mut visited = vec![false; pma.states.len()];

            while let Some(idx) = visitor.pop() {
                assert!(!visited[idx]);
                assert!(
                    pma.states[idx].base() != BASE_INVALID
                        || pma.states[idx].output_pos() != OUTPOS_INVALID
                );
                visited[idx] = true;
                for c in 0..=255 {
                    if let Some(child_idx) = pma.get_child_index(idx, c) {
                        visitor.push(child_idx);
                    }
                }
            }
        }
    }

    #[test]
    fn test_serialization() {
        let patterns: Vec<String> = {
            let mut patterns = HashSet::new();
            for _ in 0..100 {
                patterns.insert(generate_random_string(4));
            }
            patterns.into_iter().collect()
        };
        let pma = DoubleArrayAhoCorasick::new(&patterns).unwrap();

        // Serialize
        let mut buffer = vec![];
        pma.serialize(&mut buffer).unwrap();

        // Deserialize
        let other = DoubleArrayAhoCorasick::deserialize(&buffer[..]).unwrap();

        assert_eq!(pma.states.len(), other.states.len());
        for (a, b) in pma.states.iter().zip(other.states.iter()) {
            assert_eq!(a.base, b.base);
            assert_eq!(a.fach, b.fach);
            assert_eq!(a.output_pos, b.output_pos);
        }
        assert_eq!(pma.outputs.len(), other.outputs.len());
        for (a, b) in pma.outputs.iter().zip(other.outputs.iter()) {
            assert_eq!(a.as_u64(), b.as_u64());
        }
    }
}
