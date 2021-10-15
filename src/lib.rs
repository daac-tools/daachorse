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

use std::error::Error;
use std::fmt;
use std::io;

/// The maximum ID of a pattern used as an invalid value.
const PATTERN_ID_INVALID: u32 = std::u32::MAX;
/// The maximum length of a pattern used as an invalid value.
const PATTERN_LEN_INVALID: u32 = std::u32::MAX >> 1;
/// The maximum BASE value used as an invalid value.
const BASE_INVALID: u32 = std::u32::MAX;
/// The maximum FAIL value used as an invalid value.
const FAIL_INVALID: u32 = std::u32::MAX >> 8;
/// The maximum output position value used as an invalid value.
const OUTPOS_INVALID: u32 = std::u32::MAX;
/// The maximum state index used as an invalid value.
const STATE_IDX_INVALID: u32 = std::u32::MAX;
/// The length of each double-array block.
const BLOCK_LEN: usize = 256;
/// The number of last blocks to be searched in `DoubleArrayAhoCorasickBuilder::find_base`.
const FREE_BLOCKS: usize = 16;
/// The number of last states (or elements) to be searched in `DoubleArrayAhoCorasickBuilder::find_base`.
const FREE_STATES: usize = BLOCK_LEN * FREE_BLOCKS;

/// Errors in daachorse.
#[derive(Debug)]
pub enum DaachorseError {
    InvalidArgument(InvalidArgumentError),
    DuplicatePattern(DuplicatePatternError),
    PatternScale(PatternScaleError),
    AutomatonScale(AutomatonScaleError),
}

/// Error used when the argument is invalid.
#[derive(Debug)]
pub struct InvalidArgumentError {
    /// Name of the argument.
    arg: &'static str,

    /// Error message.
    msg: String,
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
    pattern: Vec<u8>,
}

impl fmt::Display for DuplicatePatternError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DuplicatePatternError: {:?}", self.pattern)
    }
}

impl Error for DuplicatePatternError {}

/// Error used when the scale of input patterns exceeds the expected one.
#[derive(Debug)]
pub struct PatternScaleError {
    msg: String,
}

impl fmt::Display for PatternScaleError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PatternScaleError: {}", self.msg)
    }
}

impl Error for PatternScaleError {}

/// Error used when the scale of the automaton exceeds the expected one.
#[derive(Debug)]
pub struct AutomatonScaleError {
    msg: String,
}

impl fmt::Display for AutomatonScaleError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "AutomatonScaleError: {}", self.msg)
    }
}

impl Error for AutomatonScaleError {}

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
    fn add(&mut self, pattern: &[u8]) -> Result<(), DaachorseError> {
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
            let e = DuplicatePatternError {
                pattern: pattern.to_vec(),
            };
            return Err(DaachorseError::DuplicatePattern(e));
        }
        if self.len > PATTERN_ID_INVALID as usize {
            let e = PatternScaleError {
                msg: format!("Number of patterns must be <= {}", PATTERN_ID_INVALID),
            };
            return Err(DaachorseError::PatternScale(e));
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
    pub fn new(pattern_id: u32, pattern_len: u32, is_begin: bool) -> Self {
        debug_assert!(pattern_len <= PATTERN_LEN_INVALID);
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

// TODO: Optimize in memory
#[derive(Clone, Copy)]
struct Extra {
    // For double-array construction
    used_base: bool,
    used_index: bool,
    next: usize,
    prev: usize,
    // For output construction
    pattern_id: u32,
    processed: bool,
}

impl Default for Extra {
    fn default() -> Self {
        Self {
            used_base: false,
            used_index: false,
            next: std::usize::MAX,
            prev: std::usize::MAX,
            pattern_id: PATTERN_ID_INVALID,
            processed: false,
        }
    }
}

#[derive(Clone, Copy)]
struct StatePair {
    da_idx: usize,
    st_idx: usize,
}

/// Builder of [`DoubleArrayAhoCorasick`].
pub struct DoubleArrayAhoCorasickBuilder {
    states: Vec<State>,
    outputs: Vec<Output>,
    pattern_lens: Vec<usize>,
    extras: Vec<Extra>,
    visits: Vec<StatePair>,
    head_idx: usize,
}

impl DoubleArrayAhoCorasickBuilder {
    /// Creates a new [`DoubleArrayAhoCorasickBuilder`].
    ///
    /// # Arguments
    ///
    /// * `init_size` - Initial size of the Double-Array (<= 2^{32}).
    ///
    /// # Errors
    ///
    /// [`DaachorseError`] is returned when invalid arguements are given.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasickBuilder;
    ///
    /// let builder = DoubleArrayAhoCorasickBuilder::new(16).unwrap();
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
    pub fn new(init_size: usize) -> Result<Self, DaachorseError> {
        if init_size > STATE_IDX_INVALID as usize {
            let e = InvalidArgumentError {
                arg: "init_size",
                msg: format!("must be <= {}", STATE_IDX_INVALID),
            };
            return Err(DaachorseError::InvalidArgument(e));
        }

        let init_capa = std::cmp::min(BLOCK_LEN, init_size / BLOCK_LEN * BLOCK_LEN);
        Ok(Self {
            states: Vec::with_capacity(init_capa),
            outputs: vec![],
            pattern_lens: vec![],
            extras: Vec::with_capacity(init_capa),
            visits: vec![],
            head_idx: std::usize::MAX,
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
    /// [`DaachorseError`] is returned when
    ///   - the `patterns` contains duplicate entries,
    ///   - the scale of `patterns` exceeds the expected one, or
    ///   - the scale of the resulting automaton exceeds the expected one.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasickBuilder;
    ///
    /// let builder = DoubleArrayAhoCorasickBuilder::new(16).unwrap();
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
    pub fn build<I, P>(mut self, patterns: I) -> Result<DoubleArrayAhoCorasick, DaachorseError>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<[u8]>,
    {
        let sparse_trie = self.build_sparse_trie(patterns)?;
        self.build_double_array(&sparse_trie)?;
        self.add_fails(&sparse_trie)?;
        self.build_outputs()?;
        self.set_dummy_outputs();

        let DoubleArrayAhoCorasickBuilder {
            mut states,
            mut outputs,
            ..
        } = self;

        states.shrink_to_fit();
        outputs.shrink_to_fit();

        Ok(DoubleArrayAhoCorasick { states, outputs })
    }

    fn build_sparse_trie<I, P>(&mut self, patterns: I) -> Result<SparseTrie, DaachorseError>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<[u8]>,
    {
        let mut trie = SparseTrie::new();
        for pattern in patterns {
            let pattern = pattern.as_ref();
            if pattern.len() >= PATTERN_LEN_INVALID as usize {
                let e = PatternScaleError {
                    msg: format!("pattern.len() must be < {}", PATTERN_LEN_INVALID),
                };
                return Err(DaachorseError::PatternScale(e));
            }
            trie.add(pattern)?;
            self.pattern_lens.push(pattern.len());
        }
        Ok(trie)
    }

    fn build_double_array(&mut self, sparse_trie: &SparseTrie) -> Result<(), DaachorseError> {
        let mut node_id_map = vec![std::usize::MAX; sparse_trie.nodes.len()];
        node_id_map[0] = 0;

        self.init_array();

        for (i, node) in sparse_trie.nodes.iter().enumerate() {
            let idx = node_id_map[i];
            {
                let pattern_id = sparse_trie.pattern_id[i];
                if pattern_id != std::usize::MAX {
                    self.extras[idx].pattern_id = pattern_id as u32;
                }
            }

            if node.is_empty() {
                continue;
            }

            let base = self.find_base(node);
            if base >= self.states.len() {
                self.extend_array()?;
            }

            for &(c, child_id) in node {
                let child_idx = base ^ c as usize;
                self.fix_state(child_idx);
                self.states[child_idx].set_check(c);
                node_id_map[child_id] = child_idx;
            }
            self.states[idx].set_base(base as u32);
            self.extras[base].used_base = true;
        }

        while self.head_idx != std::usize::MAX {
            let block_idx = self.head_idx / BLOCK_LEN;
            self.close_block(block_idx);
        }
        Ok(())
    }

    fn init_array(&mut self) {
        self.states.resize(BLOCK_LEN, Default::default());
        self.extras.resize(BLOCK_LEN, Default::default());
        self.head_idx = 0;

        for i in 0..BLOCK_LEN {
            if i == 0 {
                self.extras[i].prev = BLOCK_LEN - 1;
            } else {
                self.extras[i].prev = i - 1;
            }
            if i == BLOCK_LEN - 1 {
                self.extras[i].next = 0;
            } else {
                self.extras[i].next = i + 1;
            }
        }

        self.states[0].set_check(0);
        self.fix_state(0);
    }

    fn fix_state(&mut self, i: usize) {
        debug_assert!(!self.extras[i].used_index);
        self.extras[i].used_index = true;

        let next = self.extras[i].next;
        let prev = self.extras[i].prev;
        self.extras[prev].next = next;
        self.extras[next].prev = prev;

        if self.head_idx == i {
            if next == i {
                self.head_idx = std::usize::MAX;
            } else {
                self.head_idx = next;
            }
        }
    }

    #[inline(always)]
    fn find_base(&self, node: &[(u8, usize)]) -> usize {
        if self.head_idx == std::usize::MAX {
            return self.states.len();
        }
        let mut idx = self.head_idx;
        loop {
            debug_assert!(!self.extras[idx].used_index);
            let base = idx ^ node[0].0 as usize;
            if self.check_valid_base(base, node) {
                return base;
            }
            idx = self.extras[idx].next;
            if idx == self.head_idx {
                break;
            }
        }
        self.states.len()
    }

    fn check_valid_base(&self, base: usize, node: &[(u8, usize)]) -> bool {
        if self.extras[base].used_base {
            return false;
        }
        for &(c, _) in node {
            let idx = base ^ c as usize;
            if self.extras[idx].used_index {
                return false;
            }
        }
        true
    }

    fn extend_array(&mut self) -> Result<(), DaachorseError> {
        let old_len = self.states.len();
        let new_len = old_len + BLOCK_LEN;

        if new_len > STATE_IDX_INVALID as usize {
            let e = AutomatonScaleError {
                msg: format!("states.len() must be <= {}", STATE_IDX_INVALID),
            };
            return Err(DaachorseError::AutomatonScale(e));
        }

        for i in old_len..new_len {
            self.states.push(Default::default());
            self.extras.push(Default::default());
            self.extras[i].next = i + 1;
            self.extras[i].prev = i - 1;
        }

        if self.head_idx == std::usize::MAX {
            self.extras[old_len].prev = new_len - 1;
            self.extras[new_len - 1].next = old_len;
            self.head_idx = old_len;
        } else {
            let tail_idx = self.extras[self.head_idx].prev;
            self.extras[old_len].prev = tail_idx;
            self.extras[tail_idx].next = old_len;
            self.extras[new_len - 1].next = self.head_idx;
            self.extras[self.head_idx].prev = new_len - 1;
        }

        if FREE_STATES <= old_len {
            self.close_block((old_len - FREE_STATES) / BLOCK_LEN);
        }

        Ok(())
    }

    /// Note: Assumes all the previous blocks are closed.
    fn close_block(&mut self, block_idx: usize) {
        let beg_idx = block_idx * BLOCK_LEN;
        let end_idx = beg_idx + BLOCK_LEN;

        // Already closed?
        if self.head_idx >= end_idx {
            return;
        }

        let unused_base = {
            let mut i = beg_idx;
            while i < end_idx {
                if !self.extras[i].used_base {
                    break;
                }
                i += 1;
            }
            i
        };
        debug_assert_ne!(unused_base, end_idx);

        for c in 0..BLOCK_LEN {
            let idx = unused_base ^ c;
            if idx == 0 || !self.extras[idx].used_index {
                self.states[idx].set_check(c as u8);
            }
        }

        while self.head_idx < end_idx && self.head_idx != std::usize::MAX {
            self.fix_state(self.head_idx);
        }
    }

    fn add_fails(&mut self, sparse_trie: &SparseTrie) -> Result<(), DaachorseError> {
        self.states[0].set_fail(0);
        self.visits.reserve(sparse_trie.nodes.len());

        for &(c, st_child_idx) in &sparse_trie.nodes[0] {
            let da_child_idx = self.get_child_index(0, c).unwrap();
            self.states[da_child_idx].set_fail(0);
            self.visits.push(StatePair {
                da_idx: da_child_idx,
                st_idx: st_child_idx,
            });
        }

        let mut vi = 0;
        while vi < self.visits.len() {
            let StatePair {
                da_idx: da_node_idx,
                st_idx: st_node_idx,
            } = self.visits[vi];
            vi += 1;

            for &(c, st_child_idx) in &sparse_trie.nodes[st_node_idx] {
                let da_child_idx = self.get_child_index(da_node_idx, c).unwrap();
                let mut fail_idx = self.states[da_node_idx].fail() as usize;
                let new_fail_idx = loop {
                    if let Some(child_fail_idx) = self.get_child_index(fail_idx, c) {
                        break child_fail_idx;
                    }
                    let next_fail_idx = self.states[fail_idx].fail() as usize;
                    if fail_idx == 0 && next_fail_idx == 0 {
                        break 0;
                    }
                    fail_idx = next_fail_idx;
                };
                if new_fail_idx >= FAIL_INVALID as usize {
                    let e = AutomatonScaleError {
                        msg: format!("fail_idx must be < {}", FAIL_INVALID),
                    };
                    return Err(DaachorseError::AutomatonScale(e));
                }

                self.states[da_child_idx].set_fail(new_fail_idx as u32);
                self.visits.push(StatePair {
                    da_idx: da_child_idx,
                    st_idx: st_child_idx,
                });
            }
        }

        Ok(())
    }

    fn build_outputs(&mut self) -> Result<(), DaachorseError> {
        let error_checker = |outputs: &Vec<Output>| {
            if outputs.len() > OUTPOS_INVALID as usize {
                let e = AutomatonScaleError {
                    msg: format!("outputs.len() must be <= {}", OUTPOS_INVALID),
                };
                Err(DaachorseError::AutomatonScale(e))
            } else {
                Ok(())
            }
        };

        for sp in self.visits.iter().rev() {
            let mut da_node_idx = sp.da_idx;

            let Extra {
                pattern_id,
                processed,
                ..
            } = self.extras[da_node_idx];

            if pattern_id == PATTERN_ID_INVALID {
                continue;
            }
            if processed {
                debug_assert_ne!(self.states[da_node_idx].output_pos(), PATTERN_ID_INVALID);
                continue;
            }

            self.extras[da_node_idx].processed = true;
            self.states[da_node_idx].set_output_pos(self.outputs.len() as u32);
            self.outputs.push(Output::new(
                pattern_id,
                self.pattern_lens[pattern_id as usize] as u32,
                true,
            ));

            error_checker(&self.outputs)?;

            loop {
                da_node_idx = self.states[da_node_idx].fail() as usize;
                if da_node_idx == 0 {
                    break;
                }

                let Extra {
                    pattern_id,
                    processed,
                    ..
                } = self.extras[da_node_idx];

                if pattern_id == PATTERN_ID_INVALID {
                    continue;
                }

                if processed {
                    let mut clone_pos = self.states[da_node_idx].output_pos() as usize;
                    debug_assert!(!self.outputs[clone_pos].is_begin());
                    while !self.outputs[clone_pos].is_begin() {
                        self.outputs.push(self.outputs[clone_pos]);
                        clone_pos += 1;
                    }
                    error_checker(&self.outputs)?;
                    break;
                }

                self.extras[da_node_idx].processed = true;
                self.states[da_node_idx].set_output_pos(self.outputs.len() as u32);
                self.outputs.push(Output::new(
                    pattern_id,
                    self.pattern_lens[pattern_id as usize] as u32,
                    false,
                ));
            }
        }

        // sentinel
        self.outputs
            .push(Output::new(PATTERN_ID_INVALID, PATTERN_LEN_INVALID, true));
        error_checker(&self.outputs)?;

        Ok(())
    }

    fn set_dummy_outputs(&mut self) {
        for sp in self.visits.iter() {
            let da_node_idx = sp.da_idx;

            let Extra {
                pattern_id,
                processed,
                ..
            } = self.extras[da_node_idx];

            if processed {
                debug_assert_ne!(self.states[da_node_idx].output_pos(), PATTERN_ID_INVALID);
                continue;
            }
            debug_assert_eq!(pattern_id, PATTERN_ID_INVALID);

            let fail_idx = self.states[da_node_idx].fail() as usize;
            let output_pos = self.states[fail_idx].output_pos();
            self.states[da_node_idx].set_output_pos(output_pos);
        }
    }

    #[inline(always)]
    fn get_child_index(&self, idx: usize, c: u8) -> Option<usize> {
        if self.states[idx].base() == BASE_INVALID {
            return None;
        }
        let child_idx = (self.states[idx].base() ^ c as u32) as usize;
        if self.states[child_idx].check() == c {
            Some(child_idx)
        } else {
            None
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
            assert_eq!(a.fach, b.fach);
            assert_eq!(a.output_pos, b.output_pos);
        }
        assert_eq!(pma.outputs.len(), other.outputs.len());
        for (a, b) in pma.outputs.iter().zip(other.outputs.iter()) {
            assert_eq!(a.as_u64(), b.as_u64());
        }
    }
}
