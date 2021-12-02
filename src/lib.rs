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

mod builder;
pub mod errors;

pub use builder::DoubleArrayAhoCorasickBuilder;
use errors::DaachorseError;

// The maximum BASE value used as an invalid value.
pub(crate) const BASE_INVALID: u32 = std::u32::MAX;
// The maximum output position value used as an invalid value.
pub(crate) const OUTPUT_POS_INVALID: u32 = std::u32::MAX;
// The maximum FAIL value.
pub(crate) const FAIL_MAX: u32 = 0xFFFFFF;
// The mask value of FAIL for `State::fach`.
const FAIL_MASK: u32 = FAIL_MAX << 8;
// The mask value of CEHCK for `State::fach`.
const CHECK_MASK: u32 = 0xFF;

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
        self.fach |= x as u32;
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
}

#[derive(Copy, Clone)]
struct Output {
    value: u32,
    length: u32, // 1 bit is borrowed by a beginning flag
}

impl Output {
    #[inline(always)]
    pub const fn new(value: u32, length: u32, is_begin: bool) -> Self {
        Self {
            value,
            length: (length << 1) | is_begin as u32,
        }
    }

    #[inline(always)]
    pub const fn value(&self) -> u32 {
        self.value
    }

    #[inline(always)]
    pub const fn length(&self) -> u32 {
        self.length >> 1
    }

    #[inline(always)]
    pub const fn is_begin(&self) -> bool {
        self.length & 1 == 1
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
            // state_id is always smaller than self.pma.states.len() because
            // self.pma.get_next_state_id_unchecked() ensures to return such a value.
            state_id = unsafe { self.pma.get_next_state_id_unchecked(state_id, c) };
            if let Some(output_pos) =
                unsafe { self.pma.states.get_unchecked(state_id).output_pos() }
            {
                // output_pos is always smaller than self.pma.outputs.len() because
                // State::output_pos() ensures to return such a value when it is Some.
                let out = unsafe { self.pma.outputs.get_unchecked(output_pos as usize) };
                self.pos = pos + 1;
                return Some(Match {
                    length: out.length() as usize,
                    end: self.pos,
                    value: out.value() as usize,
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
    output_pos: usize,
}

impl<'a, P> Iterator for FindOverlappingIterator<'a, P>
where
    P: AsRef<[u8]>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        // self.output_pos is always smaller than self.pma.outputs.len() because
        // State::output_pos() ensures to return such a value when it is Some.
        let out = unsafe { self.pma.outputs.get_unchecked(self.output_pos) };
        if !out.is_begin() {
            self.output_pos += 1;
            return Some(Match {
                length: out.length() as usize,
                end: self.pos,
                value: out.value() as usize,
            });
        }
        let haystack = self.haystack.as_ref();
        for (pos, &c) in haystack.iter().enumerate().skip(self.pos) {
            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.get_next_state_id_unchecked() ensures to return such a value.
            self.state_id = unsafe { self.pma.get_next_state_id_unchecked(self.state_id, c) };
            if let Some(output_pos) =
                unsafe { self.pma.states.get_unchecked(self.state_id).output_pos() }
            {
                self.pos = pos + 1;
                self.output_pos = output_pos as usize + 1;
                let out = unsafe { self.pma.outputs.get_unchecked(output_pos as usize) };
                return Some(Match {
                    length: out.length() as usize,
                    end: self.pos,
                    value: out.value() as usize,
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
            // self.state_id is always smaller than self.pma.states.len() because
            // self.pma.get_next_state_id_unchecked() ensures to return such a value.
            self.state_id = unsafe { self.pma.get_next_state_id_unchecked(self.state_id, c) };
            if let Some(output_pos) =
                unsafe { self.pma.states.get_unchecked(self.state_id).output_pos() }
            {
                // output_pos is always smaller than self.pma.outputs.len() because
                // State::output_pos() ensures to return such a value when it is Some.
                let out = unsafe { self.pma.outputs.get_unchecked(output_pos as usize) };
                self.pos = pos + 1;
                return Some(Match {
                    length: out.length() as usize,
                    end: self.pos,
                    value: out.value() as usize,
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
    /// Creates a new [`DoubleArrayAhoCorasick`] from input patterns.
    /// The value `i` is automatically associated with `patterns[i]`.
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
    /// assert_eq!((0, 1, 2), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn new<I, P>(patterns: I) -> Result<Self, DaachorseError>
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
    /// * `patvals` - List of pattern-value pairs, where the value is of type `u32` and less than `u32::MAX`.
    ///
    /// # Errors
    ///
    /// [`errors::DuplicatePatternError`] is returned when `patvals` contains duplicate patterns or invalid values.
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
    pub fn with_values<I, P>(patvals: I) -> Result<Self, DaachorseError>
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
    pub fn find_overlapping_iter<P>(&self, haystack: P) -> FindOverlappingIterator<P>
    where
        P: AsRef<[u8]>,
    {
        FindOverlappingIterator {
            pma: self,
            haystack,
            state_id: 0,
            pos: 0,
            output_pos: 0,
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
        self.states.len() * std::mem::size_of::<State>()
            + self.outputs.len() * std::mem::size_of::<Output>()
    }

    /// # Safety
    ///
    /// `state_id` must be smaller than the length of states.
    #[inline(always)]
    unsafe fn get_child_index_unchecked(&self, state_id: usize, c: u8) -> Option<usize> {
        // child_idx is always smaller than states.len() because
        //  - states.len() is 256 * k for some integer k, and
        //  - base() returns smaller than states.len() when it is Some.
        self.states.get_unchecked(state_id).base().and_then(|base| {
            let child_idx = (base ^ c as u32) as usize;
            Some(child_idx).filter(|&x| self.states.get_unchecked(x).check() == c)
        })
    }

    /// # Safety
    ///
    /// `state_id` must be smaller than the length of states.
    #[inline(always)]
    unsafe fn get_next_state_id_unchecked(&self, mut state_id: usize, c: u8) -> usize {
        // In the loop, state_id is always set to values smaller than states.len(),
        // because get_child_index_unchecked() and fail() return such values.
        loop {
            if let Some(state_id) = self.get_child_index_unchecked(state_id, c) {
                return state_id;
            }
            if state_id == 0 {
                return 0;
            }
            state_id = self.states.get_unchecked(state_id).fail() as usize;
        }
    }

    #[cfg(test)]
    #[inline(always)]
    fn get_child_index(&self, state_id: usize, c: u8) -> Option<usize> {
        self.states[state_id].base().and_then(|base| {
            let child_idx = (base ^ c as u32) as usize;
            Some(child_idx).filter(|&x| self.states[x].check() == c)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::collections::{HashMap, HashSet};

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
        //             state_id=  0  3  2  1  4  6  5
        let fail_expected = vec![0, 0, 0, 0, 3, 1, 1];

        let pma_base: Vec<_> = pma.states[0..7]
            .iter()
            .map(|state| state.base().unwrap_or(BASE_INVALID))
            .collect();
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
                actual.insert((m.start(), m.end(), patterns_vec[m.value()].clone()));
            }
            eprintln!("{}", haystack);
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_find_iter_random_with_values() {
        let mut value_gen = rand::thread_rng();

        for _ in 0..100 {
            let mut patvals = HashMap::new();
            for _ in 0..100 {
                patvals.insert(generate_random_string(4), value_gen.gen_range(0..100));
            }
            let haystack = generate_random_string(100);

            // naive pattern match
            let mut expected = HashMap::new();
            let mut pos = 0;
            while pos <= haystack.len() - 4 {
                if let Some(&v) = patvals.get(&haystack[pos..pos + 4]) {
                    expected.insert((pos, pos + 4), v as usize);
                    pos += 3;
                }
                pos += 1;
            }

            // daachorse
            let mut actual = HashMap::new();
            let patvals_vec: Vec<_> = patvals.into_iter().collect();
            let pma = DoubleArrayAhoCorasick::with_values(patvals_vec).unwrap();
            for m in pma.find_iter(&haystack) {
                actual.insert((m.start(), m.end()), m.value());
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
                actual.insert((m.start(), m.end(), patterns_vec[m.value()].clone()));
            }
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_find_iter_binary_random_with_values() {
        let mut value_gen = rand::thread_rng();

        for _ in 0..100 {
            let mut patvals = HashMap::new();
            for _ in 0..100 {
                patvals.insert(
                    generate_random_binary_string(4),
                    value_gen.gen_range(0..100),
                );
            }
            let haystack = generate_random_binary_string(100);

            // naive pattern match
            let mut expected = HashMap::new();
            let mut pos = 0;
            while pos <= haystack.len() - 4 {
                if let Some(&v) = patvals.get(&haystack[pos..pos + 4]) {
                    expected.insert((pos, pos + 4), v as usize);
                    pos += 3;
                }
                pos += 1;
            }

            // daachorse
            let mut actual = HashMap::new();
            let patvals_vec: Vec<_> = patvals.into_iter().collect();
            let pma = DoubleArrayAhoCorasick::with_values(patvals_vec).unwrap();
            for m in pma.find_iter(&haystack) {
                actual.insert((m.start(), m.end()), m.value());
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
                actual.insert((m.start(), m.end(), patterns_vec[m.value()].clone()));
            }
            eprintln!("{}", haystack);
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_find_overlapping_iter_random_with_values() {
        let mut value_gen = rand::thread_rng();

        for _ in 0..100 {
            let mut patvals = HashMap::new();
            for _ in 0..6 {
                patvals.insert(generate_random_string(1), value_gen.gen_range(0..100));
            }
            for _ in 0..20 {
                patvals.insert(generate_random_string(2), value_gen.gen_range(0..100));
            }
            for _ in 0..50 {
                patvals.insert(generate_random_string(3), value_gen.gen_range(0..100));
            }
            for _ in 0..100 {
                patvals.insert(generate_random_string(4), value_gen.gen_range(0..100));
            }
            let haystack = generate_random_string(100);

            // naive pattern match
            let mut expected = HashMap::new();
            for i in 0..4 {
                for pos in 0..haystack.len() - i {
                    if let Some(&v) = patvals.get(&haystack[pos..pos + i + 1]) {
                        expected.insert((pos, pos + i + 1), v as usize);
                    }
                }
            }

            // daachorse
            let mut actual = HashMap::new();
            let patvals_vec: Vec<_> = patvals.into_iter().collect();
            let pma = DoubleArrayAhoCorasick::with_values(patvals_vec).unwrap();
            for m in pma.find_overlapping_iter(&haystack) {
                actual.insert((m.start(), m.end()), m.value());
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
                actual.insert((m.start(), m.end(), patterns_vec[m.value()].clone()));
            }
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_find_overlapping_iter_binary_random_with_values() {
        let mut value_gen = rand::thread_rng();

        for _ in 0..100 {
            let mut patvals = HashMap::new();
            for _ in 0..6 {
                patvals.insert(
                    generate_random_binary_string(1),
                    value_gen.gen_range(0..100),
                );
            }
            for _ in 0..20 {
                patvals.insert(
                    generate_random_binary_string(2),
                    value_gen.gen_range(0..100),
                );
            }
            for _ in 0..50 {
                patvals.insert(
                    generate_random_binary_string(3),
                    value_gen.gen_range(0..100),
                );
            }
            for _ in 0..100 {
                patvals.insert(
                    generate_random_binary_string(4),
                    value_gen.gen_range(0..100),
                );
            }
            let haystack = generate_random_binary_string(100);

            // naive pattern match
            let mut expected = HashMap::new();
            for i in 0..4 {
                for pos in 0..haystack.len() - i {
                    if let Some(&v) = patvals.get(&haystack[pos..pos + i + 1]) {
                        expected.insert((pos, pos + i + 1), v as usize);
                    }
                }
            }

            // daachorse
            let mut actual = HashMap::new();
            let patvals_vec: Vec<_> = patvals.into_iter().collect();
            let pma = DoubleArrayAhoCorasick::with_values(patvals_vec).unwrap();
            for m in pma.find_overlapping_iter(&haystack) {
                actual.insert((m.start(), m.end()), m.value());
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
                assert!(pma.states[idx].base().is_some() || pma.states[idx].output_pos().is_some());
                visited[idx] = true;
                for c in 0..=255 {
                    if let Some(child_idx) = pma.get_child_index(idx, c) {
                        visitor.push(child_idx);
                    }
                }
            }
        }
    }
}
