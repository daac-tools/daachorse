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

use std::collections::VecDeque;
use std::error::Error;
use std::fmt;

/// Error used when the argument is invalid.
#[derive(Debug)]
pub struct InvalidArgumentError {
    /// Name of the argument.
    pub arg: &'static str,

    /// Error message.
    pub msg: String,
}

impl fmt::Display for InvalidArgumentError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "InvalidArgumentError: {}: {}", self.arg, self.msg)
    }
}

impl Error for InvalidArgumentError {}

/// Error used when some patterns are duplicated.
#[derive(Debug)]
pub struct DuplicatePatternError {
    /// A duplicate pattern.
    pub pattern: Vec<u8>,
}

impl fmt::Display for DuplicatePatternError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DuplicatedPatternError: {:?}", self.pattern)
    }
}

impl Error for DuplicatePatternError {}

struct SparseTrie {
    nodes: Vec<Vec<(u8, usize)>>,
    pattern_id: Vec<usize>,
    len: usize,
}

impl SparseTrie {
    fn new() -> Self {
        Self {
            nodes: vec![vec![]],
            pattern_id: vec![std::usize::MAX],
            len: 0,
        }
    }

    #[inline(always)]
    fn add(&mut self, pattern: &[u8]) -> Result<(), DuplicatePatternError> {
        let mut node_id = 0;
        for &c in pattern {
            node_id = self.get(node_id, c).unwrap_or_else(|| {
                let next_node_id = self.nodes.len();
                self.nodes.push(vec![]);
                self.nodes[node_id].push((c, next_node_id));
                self.pattern_id.push(std::usize::MAX);
                next_node_id
            });
        }
        let pattern_id = self.pattern_id.get_mut(node_id).unwrap();
        if *pattern_id != std::usize::MAX {
            return Err(DuplicatePatternError {
                pattern: pattern.to_vec(),
            });
        }
        *pattern_id = self.len;
        self.len += 1;
        Ok(())
    }

    #[inline(always)]
    fn get(&self, node_id: usize, c: u8) -> Option<usize> {
        for trans in &self.nodes[node_id] {
            if c == trans.0 {
                return Some(trans.1);
            }
        }
        None
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
            let pattern = self.pma.pattern_ids[state_id];
            if pattern != std::usize::MAX {
                self.pos = pos + 1;
                return Some(Match {
                    length: self.pma.pattern_len[pattern],
                    end: self.pos,
                    pattern,
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
    cs_pattern_ids: std::slice::Iter<'a, usize>,
}

impl<'a, P> Iterator for FindOverlappingIterator<'a, P>
where
    P: AsRef<[u8]>,
{
    type Item = Match;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(&pattern) = self.cs_pattern_ids.next() {
            return Some(Match {
                length: self.pma.pattern_len[pattern],
                end: self.pos,
                pattern,
            });
        }
        let haystack = self.haystack.as_ref();
        for (pos, &c) in haystack.iter().enumerate().skip(self.pos) {
            self.state_id = self.pma.get_next_state_id(self.state_id, c);
            let pattern = self.pma.pattern_ids[self.state_id];
            if pattern != std::usize::MAX {
                self.pos = pos + 1;
                self.cs_pattern_ids = self.pma.cs_pattern_ids[pattern].iter();
                return Some(Match {
                    length: self.pma.pattern_len[pattern],
                    end: self.pos,
                    pattern,
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
            let pattern = self.pma.pattern_ids[self.state_id];
            if pattern != std::usize::MAX {
                self.pos = pos + 1;
                return Some(Match {
                    length: self.pma.pattern_len[pattern],
                    end: self.pos,
                    pattern,
                });
            }
        }
        self.pos = haystack.len();
        None
    }
}

/// Pattern match automaton implemented with the Aho-Corasick algorithm and Double-Array.
pub struct DoubleArrayAhoCorasick {
    base: Vec<isize>,
    check: Vec<usize>,
    fail: Vec<usize>,
    pattern_ids: Vec<usize>,
    pattern_len: Vec<usize>,
    cs_pattern_ids: Vec<Vec<usize>>,
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
    /// [`DuplicatePatternError`] is returned when `patterns` contains duplicate entries.
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
    pub fn new<I, P>(patterns: I) -> Result<Self, DuplicatePatternError>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<[u8]>,
    {
        DoubleArrayAhoCorasickBuilder::new(65536, 65536)
            .unwrap()
            .build(patterns)
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
            cs_pattern_ids: [].iter(),
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

    /// Returns a pattern ID of the given pattern if it exists. Otherwise, None.
    ///
    /// # Arguments
    ///
    /// * `pattern` - Pattern to search for.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasick;
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    ///
    /// assert_eq!(Some(0), pma.find_pattern_id("bcd"));
    /// assert_eq!(Some(1), pma.find_pattern_id("ab"));
    /// assert_eq!(Some(2), pma.find_pattern_id("a"));
    /// assert_eq!(None, pma.find_pattern_id("abc"));
    /// ```
    #[inline(always)]
    pub fn find_pattern_id<P>(&self, pattern: P) -> Option<usize>
    where
        P: AsRef<[u8]>,
    {
        let mut state_id = 0;
        for &c in pattern.as_ref() {
            state_id = self.get_child_index(state_id, c)?;
        }
        let pattern_id = self.pattern_ids[state_id];
        if pattern_id == std::usize::MAX {
            None
        } else {
            Some(pattern_id)
        }
    }

    #[inline(always)]
    fn get_child_index(&self, state_id: usize, c: u8) -> Option<usize> {
        let child_idx = (self.base[state_id] + c as isize) as usize;
        // When base + c < 0, the following .get() may return None since `child_idx` is too large
        // number.
        if let Some(&check) = self.check.get(child_idx) {
            if check == state_id {
                return Some(child_idx);
            }
        }
        None
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
            state_id = self.fail[state_id];
        }
    }
}

/// Builder of [`DoubleArrayAhoCorasick`].
pub struct DoubleArrayAhoCorasickBuilder {
    base: Vec<isize>,
    check: Vec<usize>,
    fail: Vec<usize>,
    pattern_ids: Vec<usize>,
    pattern_len: Vec<usize>,
    cs_pattern_ids: Vec<Vec<usize>>,
    step_size: usize,
}

impl DoubleArrayAhoCorasickBuilder {
    /// Creates a new [`DoubleArrayAhoCorasickBuilder`].
    ///
    /// # Arguments
    ///
    /// * `init_size` - Initial size of the Double-Array.
    /// * `step_size` - The amount by which the capacity of the Double-Array is increased when
    /// the capacity is insufficient.
    ///
    /// Both `init_size` and `step_size` must be positive integers.
    ///
    /// # Errors
    ///
    /// [`InvalidArgumentError`] is returned when invalid arguements are given.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasickBuilder;
    ///
    /// let builder = DoubleArrayAhoCorasickBuilder::new(16, 16).unwrap();
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = builder.build(patterns).unwrap();
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
    pub fn new(init_size: usize, step_size: usize) -> Result<Self, InvalidArgumentError> {
        if init_size == 0 {
            return Err(InvalidArgumentError {
                arg: "init_size",
                msg: "must be >= 1".to_string(),
            });
        }
        if step_size == 0 {
            return Err(InvalidArgumentError {
                arg: "step_size",
                msg: "must be >= 1".to_string(),
            });
        }
        Ok(Self {
            base: vec![std::isize::MIN; init_size],
            check: vec![std::usize::MAX; init_size],
            pattern_ids: vec![std::usize::MAX; init_size],
            cs_pattern_ids: vec![],
            pattern_len: vec![],
            fail: vec![std::usize::MAX; init_size],
            step_size,
        })
    }

    /// Builds and returns a new [`DoubleArrayAhoCorasick`].
    ///
    /// # Arguments
    ///
    /// * `patterns` - List of patterns.
    ///
    /// # Errors
    ///
    /// [`DuplicatePatternError`] is returned when the `patterns` contains duplicate entries.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasickBuilder;
    ///
    /// let builder = DoubleArrayAhoCorasickBuilder::new(16, 16).unwrap();
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = builder.build(patterns).unwrap();
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
    pub fn build<I, P>(
        mut self,
        patterns: I,
    ) -> Result<DoubleArrayAhoCorasick, DuplicatePatternError>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<[u8]>,
    {
        let sparse_trie = self.build_sparse_trie(patterns)?;
        self.build_double_array(&sparse_trie);
        self.add_fails(&sparse_trie);

        let DoubleArrayAhoCorasickBuilder {
            base,
            check,
            fail,
            pattern_ids,
            pattern_len,
            cs_pattern_ids,
            ..
        } = self;
        Ok(DoubleArrayAhoCorasick {
            base,
            check,
            fail,
            pattern_ids,
            pattern_len,
            cs_pattern_ids,
        })
    }

    fn build_sparse_trie<I, P>(&mut self, patterns: I) -> Result<SparseTrie, DuplicatePatternError>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<[u8]>,
    {
        let mut trie = SparseTrie::new();
        for pattern in patterns {
            let pattern = pattern.as_ref();
            trie.add(pattern)?;
            self.cs_pattern_ids.push(vec![]);
            self.pattern_len.push(pattern.len());
        }
        Ok(trie)
    }

    fn build_double_array(&mut self, sparse_trie: &SparseTrie) {
        let mut node_id_map = vec![std::usize::MAX; sparse_trie.nodes.len()];
        let mut min_idx = 1;
        let mut act_size = 1;
        node_id_map[0] = 0;
        self.check[0] = 0;
        for (i, node) in sparse_trie.nodes.iter().enumerate() {
            if node.is_empty() {
                continue;
            }
            let mut min_c = std::u8::MAX;
            for &(c, _) in node {
                if c < min_c {
                    min_c = c;
                }
            }
            let mut base = min_idx - min_c as isize;
            'outer: loop {
                for &(c, _) in node {
                    let idx = (base + c as isize) as usize;
                    if idx + 1 > act_size {
                        act_size = idx + 1;
                    }
                    self.extend_arrays(idx + 1);
                    if self.check[idx] != std::usize::MAX {
                        if c == min_c {
                            min_idx += 1;
                        }
                        base += 1;
                        continue 'outer;
                    }
                }
                break;
            }
            for &(c, child_id) in node {
                let idx = (base + c as isize) as usize;
                self.check[idx] = node_id_map[i];
                self.pattern_ids[idx] = sparse_trie.pattern_id[child_id];
                node_id_map[child_id] = idx;
            }
            self.base[node_id_map[i]] = base;
        }
        self.truncate_arrays(act_size);
    }

    fn add_fails(&mut self, sparse_trie: &SparseTrie) {
        let mut queue = VecDeque::new();
        self.fail[0] = 0;
        for &(c, orig_child_idx) in &sparse_trie.nodes[0] {
            let child_idx = self.get_child_index(0, c).unwrap();
            self.fail[child_idx] = 0;
            queue.push_back((child_idx, orig_child_idx));
        }
        while let Some((node_idx, orig_node_idx)) = queue.pop_front() {
            for &(c, orig_child_idx) in &sparse_trie.nodes[orig_node_idx] {
                let child_idx = self.get_child_index(node_idx, c).unwrap();
                let mut fail_idx = self.fail[node_idx];
                loop {
                    if let Some(child_fail_idx) = self.get_child_index(fail_idx, c) {
                        self.fail[child_idx] = child_fail_idx;
                        if self.pattern_ids[child_fail_idx] != std::usize::MAX {
                            if self.pattern_ids[child_idx] == std::usize::MAX {
                                self.pattern_ids[child_idx] = self.pattern_ids[child_fail_idx];
                            } else {
                                let child_pattern_id = self.pattern_ids[child_idx];
                                let fail_pattern_id = self.pattern_ids[child_fail_idx];
                                let mut fail_ids = self.cs_pattern_ids[fail_pattern_id].clone();
                                self.cs_pattern_ids[child_pattern_id].push(fail_pattern_id);
                                self.cs_pattern_ids[child_pattern_id].append(&mut fail_ids);
                            }
                        }
                        break;
                    }
                    let next_fail_idx = self.fail[fail_idx];
                    if fail_idx == 0 && next_fail_idx == 0 {
                        self.fail[child_idx] = 0;
                        break;
                    }
                    fail_idx = next_fail_idx;
                }
                queue.push_back((child_idx, orig_child_idx));
            }
        }
    }

    #[inline(always)]
    fn extend_arrays(&mut self, min_size: usize) {
        if min_size > self.base.len() {
            let new_len = ((min_size - self.base.len() - 1) / self.step_size + 1) * self.step_size
                + self.base.len();
            self.base.resize(new_len, std::isize::MIN);
            self.check.resize(new_len, std::usize::MAX);
            self.pattern_ids.resize(new_len, std::usize::MAX);
            self.fail.resize(new_len, std::usize::MAX);
        }
    }

    fn truncate_arrays(&mut self, size: usize) {
        self.base.truncate(size);
        self.check.truncate(size);
        self.pattern_ids.truncate(size);
        self.fail.truncate(size);
    }

    #[inline(always)]
    fn get_child_index(&self, idx: usize, c: u8) -> Option<usize> {
        let child_idx = (self.base[idx] + c as isize) as usize;
        // When base + c < 0, the following .get() may return None, since `child_idx` is too large
        // number.
        if let Some(&check) = self.check.get(child_idx) {
            if check == idx {
                return Some(child_idx);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::collections::HashSet;
    use std::isize::MIN;

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

        let base_expected = vec![1, 4, 3, MIN, MIN, MIN, MIN];
        let check_expected = vec![0, 0, 0, 0, 1, 2, 1];
        //                        ^  ^  ^  ^  ^  ^  ^
        //              node_id=  0  1  2  3  4  6  5
        let fail_expected = vec![0, 0, 0, 0, 1, 3, 3];

        assert_eq!(base_expected, pma.base);
        assert_eq!(check_expected, pma.check);
        assert_eq!(fail_expected, pma.fail);
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
            let patterns_vec: Vec<_> = patterns.iter().cloned().collect();
            let pma = DoubleArrayAhoCorasick::new(&patterns_vec).unwrap();
            for m in pma.find_iter(&haystack) {
                actual.insert((m.start(), m.end(), patterns_vec[m.pattern()].clone()));
            }
            eprintln!("{}", haystack);
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_find_overlapping_iter_random() {
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
                }
                pos += 1;
            }

            // daachorse
            let mut actual = HashSet::new();
            let patterns_vec: Vec<_> = patterns.iter().cloned().collect();
            let pma = DoubleArrayAhoCorasick::new(&patterns_vec).unwrap();
            for m in pma.find_overlapping_iter(&haystack) {
                actual.insert((m.start(), m.end(), patterns_vec[m.pattern()].clone()));
            }
            eprintln!("{}", haystack);
            assert_eq!(expected, actual);
        }
    }
}
