use crate::errors::{
    AutomatonScaleError, DaachorseError, DuplicatePatternError, PatternScaleError,
};
use crate::{DoubleArrayAhoCorasick, Output, State, OUTPOS_INVALID};

// The length of each double-array block.
const BLOCK_LEN: usize = 256;
// The number of last blocks to be searched in `DoubleArrayAhoCorasickBuilder::find_base`.
const FREE_BLOCKS: usize = 16;
// The number of last states (or elements) to be searched in `DoubleArrayAhoCorasickBuilder::find_base`.
const FREE_STATES: usize = BLOCK_LEN * FREE_BLOCKS;
// The maximum state index used as an invalid value.
const STATE_IDX_INVALID: u32 = std::u32::MAX;
// The maximum value of a pattern used as an invalid value.
const VALUE_INVALID: u32 = std::u32::MAX;
// The maximum length of a pattern used as an invalid value.
const LENGTH_INVALID: u32 = std::u32::MAX >> 1;
// The maximum FAIL value.
const FAIL_MAX: usize = 0x00ffffff;
// The initial capacity to build a double array.
const INIT_CAPACITY: usize = 1 << 16;

struct SparseNFA {
    states: Vec<SparseState>,
    outputs: Vec<Output>, // in which common parts are merged.
    len: usize,
}

impl SparseNFA {
    fn new() -> Self {
        Self {
            states: vec![SparseState::default()],
            outputs: vec![],
            len: 0,
        }
    }

    #[inline(always)]
    fn add(&mut self, pattern: &[u8], value: u32) -> Result<(), DaachorseError> {
        if value == VALUE_INVALID {
            let e = PatternScaleError {
                msg: format!("Input value must be < {}", VALUE_INVALID),
            };
            return Err(DaachorseError::PatternScale(e));
        }
        if pattern.len() >= LENGTH_INVALID as usize {
            let e = PatternScaleError {
                msg: format!("Pattern length must be < {}", LENGTH_INVALID),
            };
            return Err(DaachorseError::PatternScale(e));
        }

        let mut state_id = 0;
        for &c in pattern {
            if let Some(next_state_id) = self.get(state_id, c) {
                state_id = next_state_id;
            } else {
                let next_state_id = self.states.len();
                if next_state_id == STATE_IDX_INVALID as usize {
                    let e = AutomatonScaleError {
                        msg: format!("Number of states must be <= {}", STATE_IDX_INVALID),
                    };
                    return Err(DaachorseError::AutomatonScale(e));
                }
                self.states[state_id].edges.push((c, next_state_id as u32));
                self.states.push(Default::default());
                state_id = next_state_id;
            }
        }

        let output = &mut self.states[state_id].output;
        if output.0 != VALUE_INVALID {
            let e = DuplicatePatternError {
                pattern: pattern.to_vec(),
            };
            return Err(DaachorseError::DuplicatePattern(e));
        }
        *output = (value, pattern.len() as u32);
        self.len += 1;
        Ok(())
    }

    fn build_fails(&mut self) -> Vec<u32> {
        let mut q = Vec::with_capacity(self.states.len());
        for &(_, child_id) in &self.states[0].edges {
            q.push(child_id);
        }

        let mut qi = 0;
        while qi < q.len() {
            let state_id = q[qi] as usize;
            qi += 1;
            for i in 0..self.states[state_id].edges.len() {
                let (c, child_id) = self.states[state_id].edges[i];
                let mut fail_id = self.states[state_id].fail as usize;
                let new_fail_id = loop {
                    if let Some(child_fail_id) = self.get(fail_id, c) {
                        break child_fail_id;
                    }
                    let next_fail_id = self.states[fail_id].fail as usize;
                    if fail_id == 0 && next_fail_id == 0 {
                        break 0;
                    }
                    fail_id = next_fail_id;
                };
                self.states[child_id as usize].fail = new_fail_id as u32;
                q.push(child_id);
            }
        }
        q
    }

    fn build_outputs(&mut self, q: &[u32]) -> Result<(), DaachorseError> {
        let mut processed = vec![false; self.states.len()];

        // Builds an output sequence in which common parts are merged.
        for &state_id in q.iter().rev() {
            let state_id = state_id as usize;
            let s = &mut self.states[state_id];
            if s.output.0 == VALUE_INVALID {
                continue;
            }

            if processed[state_id] {
                debug_assert_ne!(s.output_pos, OUTPOS_INVALID);
                continue;
            }
            debug_assert_eq!(s.output_pos, OUTPOS_INVALID);
            processed[state_id] = true;

            s.output_pos = self.outputs.len() as u32;
            self.outputs.push(Output::new(s.output.0, s.output.1, true));
            Self::check_outputs_error(&self.outputs)?;

            let mut fail_id = state_id;
            loop {
                fail_id = self.states[fail_id].fail as usize;
                if fail_id == 0 {
                    break;
                }

                let s = &mut self.states[fail_id];
                if s.output.0 == VALUE_INVALID {
                    continue;
                }

                if processed[fail_id] {
                    debug_assert_ne!(s.output_pos, OUTPOS_INVALID);
                    let mut clone_pos = s.output_pos as usize;
                    debug_assert!(!self.outputs[clone_pos].is_begin());
                    while !self.outputs[clone_pos].is_begin() {
                        self.outputs.push(self.outputs[clone_pos]);
                        clone_pos += 1;
                    }
                    Self::check_outputs_error(&self.outputs)?;
                    break;
                }
                processed[fail_id] = true;

                s.output_pos = self.outputs.len() as u32;
                self.outputs
                    .push(Output::new(s.output.0, s.output.1, false));
                Self::check_outputs_error(&self.outputs)?;
            }
        }

        // Puts a sentinel
        self.outputs
            .push(Output::new(VALUE_INVALID, LENGTH_INVALID, true));
        self.outputs.shrink_to_fit();
        Self::check_outputs_error(&self.outputs)?;

        // Sets dummy outputs
        for &state_id in q {
            let state_id = state_id as usize;
            let s = &mut self.states[state_id];
            if processed[state_id] {
                debug_assert_ne!(s.output_pos, OUTPOS_INVALID);
                continue;
            }
            debug_assert_eq!(s.output_pos, OUTPOS_INVALID);
            debug_assert_eq!(s.output.0, VALUE_INVALID);

            let fail_id = self.states[state_id].fail as usize;
            self.states[state_id].output_pos = self.states[fail_id].output_pos;
        }

        Ok(())
    }

    #[inline(always)]
    fn check_outputs_error(outputs: &[Output]) -> Result<(), DaachorseError> {
        if outputs.len() > OUTPOS_INVALID as usize {
            let e = AutomatonScaleError {
                msg: format!("outputs.len() must be <= {}", OUTPOS_INVALID),
            };
            Err(DaachorseError::AutomatonScale(e))
        } else {
            Ok(())
        }
    }

    #[inline(always)]
    fn get(&self, state_id: usize, c: u8) -> Option<usize> {
        for &(cc, child_id) in &self.states[state_id].edges {
            if c == cc {
                return Some(child_id as usize);
            }
        }
        None
    }
}

#[derive(Clone)]
struct SparseState {
    edges: Vec<(u8, u32)>,
    fail: u32,
    output: (u32, u32),
    output_pos: u32,
}

impl Default for SparseState {
    fn default() -> Self {
        Self {
            edges: vec![],
            fail: 0,
            output: (VALUE_INVALID, LENGTH_INVALID),
            output_pos: OUTPOS_INVALID,
        }
    }
}

#[derive(Clone, Copy)]
struct Extra {
    used_base: bool,
    used_index: bool,
    next: u32,
    prev: u32,
}

impl Default for Extra {
    fn default() -> Self {
        Self {
            used_base: false,
            used_index: false,
            next: STATE_IDX_INVALID,
            prev: STATE_IDX_INVALID,
        }
    }
}

impl Extra {
    #[inline(always)]
    const fn get_next(&self) -> usize {
        self.next as usize
    }

    #[inline(always)]
    const fn get_prev(&self) -> usize {
        self.prev as usize
    }

    #[inline(always)]
    fn set_next(&mut self, x: usize) {
        self.next = x as u32
    }

    #[inline(always)]
    fn set_prev(&mut self, x: usize) {
        self.prev = x as u32
    }

    #[inline(always)]
    const fn is_used_base(&self) -> bool {
        self.used_base
    }

    #[inline(always)]
    const fn is_used_index(&self) -> bool {
        self.used_index
    }

    #[inline(always)]
    fn use_base(&mut self) {
        self.used_base = true;
    }

    #[inline(always)]
    fn use_index(&mut self) {
        self.used_index = true;
    }
}

/// Builder of [`DoubleArrayAhoCorasick`].
pub struct DoubleArrayAhoCorasickBuilder {
    states: Vec<State>,
    extras: Vec<Extra>,
    head_idx: usize,
}

impl Default for DoubleArrayAhoCorasickBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl DoubleArrayAhoCorasickBuilder {
    /// Creates a new [`DoubleArrayAhoCorasickBuilder`].
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasickBuilder;
    ///
    /// let builder = DoubleArrayAhoCorasickBuilder::new();
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = builder.build(patterns).unwrap();
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
    pub fn new() -> Self {
        let init_capa = std::cmp::min(BLOCK_LEN, INIT_CAPACITY / BLOCK_LEN * BLOCK_LEN);
        Self {
            states: Vec::with_capacity(init_capa),
            extras: Vec::with_capacity(init_capa),
            head_idx: std::usize::MAX,
        }
    }

    /// Builds and returns a new [`DoubleArrayAhoCorasick`] from input patterns.
    /// The value `i` is automatically associated with `patterns[i]`.
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
    /// let builder = DoubleArrayAhoCorasickBuilder::new();
    ///
    /// let patterns = vec!["bcd", "ab", "a"];
    /// let pma = builder.build(patterns).unwrap();
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
    pub fn build<I, P>(mut self, patterns: I) -> Result<DoubleArrayAhoCorasick, DaachorseError>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<[u8]>,
    {
        let patvals = patterns.into_iter().enumerate().map(|(i, p)| (p, i as u32));
        let nfa = self.build_sparse_nfa(patvals)?;
        self.build_double_array(&nfa)?;

        Ok(DoubleArrayAhoCorasick {
            states: self.states,
            outputs: nfa.outputs,
        })
    }

    /// Builds and returns a new [`DoubleArrayAhoCorasick`] from input pattern-value pairs.
    ///
    /// # Arguments
    ///
    /// * `patvals` - List of pattern-value pairs, where the value is of type `u32` and less than `u32::MAX`.
    ///
    /// # Errors
    ///
    /// [`DaachorseError`] is returned when
    ///   - the `patvals` contains duplicate patterns,
    ///   - the `patvals` contains invalid values,
    ///   - the scale of `patvals` exceeds the expected one, or
    ///   - the scale of the resulting automaton exceeds the expected one.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::DoubleArrayAhoCorasickBuilder;
    ///
    /// let builder = DoubleArrayAhoCorasickBuilder::new();
    ///
    /// let patvals = vec![("bcd", 0), ("ab", 1), ("a", 2), ("e", 1)];
    /// let pma = builder.build_with_values(patvals).unwrap();
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
    pub fn build_with_values<I, P>(
        mut self,
        patvals: I,
    ) -> Result<DoubleArrayAhoCorasick, DaachorseError>
    where
        I: IntoIterator<Item = (P, u32)>,
        P: AsRef<[u8]>,
    {
        let nfa = self.build_sparse_nfa(patvals)?;
        self.build_double_array(&nfa)?;

        Ok(DoubleArrayAhoCorasick {
            states: self.states,
            outputs: nfa.outputs,
        })
    }

    fn build_sparse_nfa<I, P>(&mut self, patvals: I) -> Result<SparseNFA, DaachorseError>
    where
        I: IntoIterator<Item = (P, u32)>,
        P: AsRef<[u8]>,
    {
        let mut nfa = SparseNFA::new();
        for (pattern, value) in patvals {
            nfa.add(pattern.as_ref(), value)?;
        }
        let q = nfa.build_fails();
        nfa.build_outputs(&q)?;
        Ok(nfa)
    }

    fn build_double_array(&mut self, nfa: &SparseNFA) -> Result<(), DaachorseError> {
        let mut state_id_map = vec![STATE_IDX_INVALID; nfa.states.len()];
        state_id_map[0] = 0;

        self.init_array();

        // Arranges base & check values
        for (i, state) in nfa.states.iter().enumerate() {
            let idx = state_id_map[i] as usize;
            if state.edges.is_empty() {
                continue;
            }

            let base = self.find_base(&state.edges);
            if base >= self.states.len() {
                self.extend_array()?;
            }

            for &(c, child_id) in &state.edges {
                let child_idx = base ^ c as usize;
                self.fix_state(child_idx);
                self.states[child_idx].set_check(c);
                state_id_map[child_id as usize] = child_idx as u32;
            }
            self.states[idx].set_base(base as u32);
            self.extras[base].use_base();
        }

        // Sets fail & output_pos values
        for (i, state) in nfa.states.iter().enumerate() {
            let idx = state_id_map[i] as usize;
            self.states[idx].set_output_pos(state.output_pos);

            let fail_idx = state_id_map[state.fail as usize] as usize;
            if fail_idx > FAIL_MAX {
                let e = AutomatonScaleError {
                    msg: format!("fail_idx must be <= {}", FAIL_MAX),
                };
                return Err(DaachorseError::AutomatonScale(e));
            }
            self.states[idx].set_fail(fail_idx as u32);
        }

        // If the root block has not been closed, it has to be closed for setting CHECK[0] to a valid value.
        if self.states.len() <= FREE_STATES {
            self.close_block(0);
        }

        while self.head_idx != std::usize::MAX {
            let block_idx = self.head_idx / BLOCK_LEN;
            self.close_block(block_idx);
        }

        self.states.shrink_to_fit();

        Ok(())
    }

    fn init_array(&mut self) {
        self.states.resize(BLOCK_LEN, Default::default());
        self.extras.resize(BLOCK_LEN, Default::default());
        self.head_idx = 0;

        for i in 0..BLOCK_LEN {
            if i == 0 {
                self.extras[i].set_prev(BLOCK_LEN - 1);
            } else {
                self.extras[i].set_prev(i - 1);
            }
            if i == BLOCK_LEN - 1 {
                self.extras[i].set_next(0);
            } else {
                self.extras[i].set_next(i + 1);
            }
        }

        self.states[0].set_check(0);
        self.fix_state(0);
    }

    #[inline(always)]
    fn fix_state(&mut self, i: usize) {
        debug_assert!(!self.extras[i].is_used_index());
        self.extras[i].use_index();

        let next = self.extras[i].get_next();
        let prev = self.extras[i].get_prev();
        self.extras[prev].set_next(next);
        self.extras[next].set_prev(prev);

        if self.head_idx == i {
            if next == i {
                self.head_idx = std::usize::MAX;
            } else {
                self.head_idx = next;
            }
        }
    }

    #[inline(always)]
    fn find_base(&self, edges: &[(u8, u32)]) -> usize {
        if self.head_idx == std::usize::MAX {
            return self.states.len();
        }
        let mut idx = self.head_idx;
        loop {
            debug_assert!(!self.extras[idx].is_used_index());
            let base = idx ^ edges[0].0 as usize;
            if self.check_valid_base(base, edges) {
                return base;
            }
            idx = self.extras[idx].get_next();
            if idx == self.head_idx {
                break;
            }
        }
        self.states.len()
    }

    #[inline(always)]
    fn check_valid_base(&self, base: usize, edges: &[(u8, u32)]) -> bool {
        if self.extras[base].is_used_base() {
            return false;
        }
        for &(c, _) in edges {
            let idx = base ^ c as usize;
            if self.extras[idx].is_used_index() {
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
            self.extras[i].set_next(i + 1);
            self.extras[i].set_prev(i - 1);
        }

        if self.head_idx == std::usize::MAX {
            self.extras[old_len].set_prev(new_len - 1);
            self.extras[new_len - 1].set_next(old_len);
            self.head_idx = old_len;
        } else {
            let tail_idx = self.extras[self.head_idx].get_prev();
            self.extras[old_len].set_prev(tail_idx);
            self.extras[tail_idx].set_next(old_len);
            self.extras[new_len - 1].set_next(self.head_idx);
            self.extras[self.head_idx].set_prev(new_len - 1);
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

        if block_idx == 0 || self.head_idx < end_idx {
            self.remove_invalid_checks(block_idx);
        }
        while self.head_idx < end_idx && self.head_idx != std::usize::MAX {
            self.fix_state(self.head_idx);
        }
    }

    fn remove_invalid_checks(&mut self, block_idx: usize) {
        let beg_idx = block_idx * BLOCK_LEN;
        let end_idx = beg_idx + BLOCK_LEN;

        let unused_base = {
            let mut i = beg_idx;
            while i < end_idx {
                if !self.extras[i].is_used_base() {
                    break;
                }
                i += 1;
            }
            i
        };
        debug_assert_ne!(unused_base, end_idx);

        for c in 0..BLOCK_LEN {
            let idx = unused_base ^ c;
            if idx == 0 || !self.extras[idx].is_used_index() {
                self.states[idx].set_check(c as u8);
            }
        }
    }
}
