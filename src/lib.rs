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

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

use std::collections::VecDeque;
use std::error::Error;
use std::fmt;
use std::io;

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
        write!(f, "DuplicatePatternError: {:?}", self.pattern)
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

#[derive(Clone, Copy)]
struct State {
    base: isize,
    check: usize,
    fail: usize,
    pattern_id: usize,
}

impl Default for State {
    fn default() -> Self {
        Self {
            base: std::isize::MIN,
            check: std::usize::MAX,
            fail: std::usize::MAX,
            pattern_id: std::usize::MAX,
        }
    }
}

impl State {
    /// Serializes the state.
    pub fn serialize<W>(&self, mut writer: W) -> io::Result<()>
    where
        W: io::Write,
    {
        writer.write_i64::<LittleEndian>(self.base as i64)?;
        writer.write_u64::<LittleEndian>(self.check as u64)?;
        writer.write_u64::<LittleEndian>(self.fail as u64)?;
        writer.write_u64::<LittleEndian>(self.pattern_id as u64)?;
        Ok(())
    }

    /// Deserializes the state.
    pub fn deserialize<R>(mut reader: R) -> io::Result<Self>
    where
        R: io::Read,
    {
        let base = reader.read_i64::<LittleEndian>()? as isize;
        let check = reader.read_u64::<LittleEndian>()? as usize;
        let fail = reader.read_u64::<LittleEndian>()? as usize;
        let pattern_id = reader.read_u64::<LittleEndian>()? as usize;
        Ok(Self {
            base,
            check,
            fail,
            pattern_id,
        })
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
            let pattern = unsafe { self.pma.states.get_unchecked(state_id).pattern_id };
            if let Some(&length) = self.pma.pattern_len.get(pattern) {
                self.pos = pos + 1;
                return Some(Match {
                    length,
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
                length: unsafe { *self.pma.pattern_len.get_unchecked(pattern) },
                end: self.pos,
                pattern,
            });
        }
        let haystack = self.haystack.as_ref();
        for (pos, &c) in haystack.iter().enumerate().skip(self.pos) {
            self.state_id = self.pma.get_next_state_id(self.state_id, c);
            let pattern = unsafe { self.pma.states.get_unchecked(self.state_id).pattern_id };
            if let Some(&length) = self.pma.pattern_len.get(pattern) {
                self.pos = pos + 1;
                self.cs_pattern_ids =
                    unsafe { self.pma.cs_pattern_ids.get_unchecked(pattern) }.iter();
                return Some(Match {
                    length,
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
            let pattern = unsafe { self.pma.states.get_unchecked(self.state_id).pattern_id };
            if let Some(&length) = self.pma.pattern_len.get(pattern) {
                self.pos = pos + 1;
                return Some(Match {
                    length,
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
    states: Vec<State>,
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
        writer.write_u64::<LittleEndian>(self.pattern_len.len() as u64)?;
        for &x in &self.pattern_len {
            writer.write_u64::<LittleEndian>(x as u64)?;
        }
        writer.write_u64::<LittleEndian>(self.cs_pattern_ids.len() as u64)?;
        for ids in &self.cs_pattern_ids {
            writer.write_u64::<LittleEndian>(ids.len() as u64)?;
            for &id in ids {
                writer.write_u64::<LittleEndian>(id as u64)?;
            }
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
        let pattern_len = {
            let len = reader.read_u64::<LittleEndian>()? as usize;
            let mut pattern_len = Vec::with_capacity(len);
            for _ in 0..len {
                pattern_len.push(reader.read_u64::<LittleEndian>()? as usize);
            }
            pattern_len
        };
        let cs_pattern_ids = {
            let len = reader.read_u64::<LittleEndian>()? as usize;
            let mut cs_pattern_ids = Vec::with_capacity(len);
            for _ in 0..len {
                let num_ids = reader.read_u64::<LittleEndian>()? as usize;
                let mut ids = Vec::with_capacity(num_ids);
                for _ in 0..num_ids {
                    ids.push(reader.read_u64::<LittleEndian>()? as usize);
                }
                cs_pattern_ids.push(ids);
            }
            cs_pattern_ids
        };
        Ok(Self {
            states,
            pattern_len,
            cs_pattern_ids,
        })
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
        writer.write_u64::<LittleEndian>(self.pattern_len.len() as u64)?;
        for &x in &self.pattern_len {
            writer.write_u64::<LittleEndian>(x as u64)?;
        }
        writer.write_u64::<LittleEndian>(self.cs_pattern_ids.len() as u64)?;
        for ids in &self.cs_pattern_ids {
            writer.write_u64::<LittleEndian>(ids.len() as u64)?;
            for &id in ids {
                writer.write_u64::<LittleEndian>(id as u64)?;
            }
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
    /// assert_eq!(Some(0), other.find_pattern_id("bcd"));
    /// assert_eq!(Some(1), other.find_pattern_id("ab"));
    /// assert_eq!(Some(2), other.find_pattern_id("a"));
    /// assert_eq!(None, other.find_pattern_id("abc"));
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
        let pattern_len = {
            let len = reader.read_u64::<LittleEndian>()? as usize;
            let mut pattern_len = Vec::with_capacity(len);
            for _ in 0..len {
                pattern_len.push(reader.read_u64::<LittleEndian>()? as usize);
            }
            pattern_len
        };
        let cs_pattern_ids = {
            let len = reader.read_u64::<LittleEndian>()? as usize;
            let mut cs_pattern_ids = Vec::with_capacity(len);
            for _ in 0..len {
                let num_ids = reader.read_u64::<LittleEndian>()? as usize;
                let mut ids = Vec::with_capacity(num_ids);
                for _ in 0..num_ids {
                    ids.push(reader.read_u64::<LittleEndian>()? as usize);
                }
                cs_pattern_ids.push(ids);
            }
            cs_pattern_ids
        };
        Ok(Self {
            states,
            pattern_len,
            cs_pattern_ids,
        })
    }

    #[inline(always)]
    fn get_child_index(&self, state_id: usize, c: u8) -> Option<usize> {
        let child_idx = (unsafe { self.states.get_unchecked(state_id).base } + c as isize) as usize;
        // When base + c < 0, the following .get() returns None since `child_idx` is too large
        // number.
        if let Some(state) = self.states.get(child_idx) {
            if state.check == state_id {
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
            state_id = unsafe { self.states.get_unchecked(state_id).fail };
        }
    }
}

/// Builder of [`DoubleArrayAhoCorasick`].
pub struct DoubleArrayAhoCorasickBuilder {
    states: Vec<State>,
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
            states: vec![State::default(); init_size],
            cs_pattern_ids: vec![],
            pattern_len: vec![],
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
            states,
            pattern_len,
            cs_pattern_ids,
            ..
        } = self;
        Ok(DoubleArrayAhoCorasick {
            states,
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
        self.states[0].check = 0;
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
                    if self.states[idx].check != std::usize::MAX {
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
                self.states[idx].check = node_id_map[i];
                self.states[idx].pattern_id = sparse_trie.pattern_id[child_id];
                node_id_map[child_id] = idx;
            }
            self.states[node_id_map[i]].base = base;
        }
        self.truncate_arrays(act_size);
    }

    fn add_fails(&mut self, sparse_trie: &SparseTrie) {
        let mut queue = VecDeque::new();
        self.states[0].fail = 0;
        for &(c, orig_child_idx) in &sparse_trie.nodes[0] {
            let child_idx = self.get_child_index(0, c).unwrap();
            self.states[child_idx].fail = 0;
            queue.push_back((child_idx, orig_child_idx));
        }
        while let Some((node_idx, orig_node_idx)) = queue.pop_front() {
            for &(c, orig_child_idx) in &sparse_trie.nodes[orig_node_idx] {
                let child_idx = self.get_child_index(node_idx, c).unwrap();
                let mut fail_idx = self.states[node_idx].fail;
                self.states[child_idx].fail = loop {
                    if let Some(child_fail_idx) = self.get_child_index(fail_idx, c) {
                        if self.states[child_fail_idx].pattern_id != std::usize::MAX {
                            let fail_pattern_id = self.states[child_fail_idx].pattern_id;
                            let child_pattern_id = self.states[child_idx].pattern_id;
                            if child_pattern_id == std::usize::MAX {
                                self.states[child_idx].pattern_id = fail_pattern_id;
                            } else {
                                let mut fail_ids = self.cs_pattern_ids[fail_pattern_id].clone();
                                self.cs_pattern_ids[child_pattern_id].push(fail_pattern_id);
                                self.cs_pattern_ids[child_pattern_id].append(&mut fail_ids);
                            }
                        }
                        break child_fail_idx;
                    }
                    let next_fail_idx = self.states[fail_idx].fail;
                    if fail_idx == 0 && next_fail_idx == 0 {
                        break 0;
                    }
                    fail_idx = next_fail_idx;
                };
                queue.push_back((child_idx, orig_child_idx));
            }
        }
    }

    #[inline(always)]
    fn extend_arrays(&mut self, min_size: usize) {
        if min_size > self.states.len() {
            let new_len = ((min_size - self.states.len() - 1) / self.step_size + 1)
                * self.step_size
                + self.states.len();
            self.states.resize(new_len, State::default());
        }
    }

    fn truncate_arrays(&mut self, size: usize) {
        self.states.truncate(size);
    }

    #[inline(always)]
    fn get_child_index(&self, idx: usize, c: u8) -> Option<usize> {
        let child_idx = (unsafe { self.states.get_unchecked(idx).base } + c as isize) as usize;
        // When base + c < 0, the following .get() returns None, since `child_idx` is too large
        // number.
        if let Some(state) = self.states.get(child_idx) {
            if state.check == idx {
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

        let pma_base: Vec<_> = pma.states.iter().map(|state| state.base).collect();
        let pma_check: Vec<_> = pma.states.iter().map(|state| state.check).collect();
        let pma_fail: Vec<_> = pma.states.iter().map(|state| state.fail).collect();

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
            assert_eq!(a.check, b.check);
            assert_eq!(a.fail, b.fail);
            assert_eq!(a.pattern_id, b.pattern_id);
        }
        assert_eq!(pma.pattern_len, other.pattern_len);
        assert_eq!(pma.cs_pattern_ids.len(), other.cs_pattern_ids.len());
        for (a, b) in pma.cs_pattern_ids.iter().zip(other.cs_pattern_ids.iter()) {
            assert_eq!(a, b);
        }
    }
}
