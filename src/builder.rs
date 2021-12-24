use crate::errors::{
    AutomatonScaleError, DaachorseError, DuplicatePatternError, PatternScaleError,
};
use crate::{
    DoubleArrayAhoCorasick, MatchKind, Output, State, DEAD_STATE_IDX, FAIL_MAX, OUTPUT_POS_INVALID,
    ROOT_STATE_IDX,
};

// The maximum value of each double-array block.
const BLOCK_MAX: u8 = std::u8::MAX;
// The length of each double-array block.
const BLOCK_LEN: u32 = BLOCK_MAX as u32 + 1;
// The number of last blocks to be searched in `DoubleArrayAhoCorasickBuilder::find_base`.
const FREE_BLOCKS: u32 = 16;
// The number of last states (or elements) to be searched in `DoubleArrayAhoCorasickBuilder::find_base`.
const FREE_STATES: u32 = BLOCK_LEN * FREE_BLOCKS;
// The maximum value of a pattern used as an invalid value.
const VALUE_INVALID: u32 = std::u32::MAX;
// The maximum length of a pattern used as an invalid value.
const LENGTH_INVALID: u32 = std::u32::MAX >> 1;
// The initial capacity to build a double array.
const INIT_CAPACITY: u32 = 1 << 16;
// The root state id of SparseNFA.
const ROOT_STATE_ID: u32 = ROOT_STATE_IDX;
// The dead state id of SparseNFA.
const DEAD_STATE_ID: u32 = DEAD_STATE_IDX;

struct SparseNFA {
    states: Vec<SparseState>,
    outputs: Vec<Output>, // in which common parts are merged.
    len: usize,
    match_kind: MatchKind,
}

impl SparseNFA {
    fn new(match_kind: MatchKind) -> Self {
        Self {
            states: vec![SparseState::default(), SparseState::default()], // (root, dead)
            outputs: vec![],
            len: 0,
            match_kind,
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
        if pattern.is_empty() {
            let e = PatternScaleError {
                msg: "Pattern must not be empty".to_string(),
            };
            return Err(DaachorseError::PatternScale(e));
        }

        let mut state_id = ROOT_STATE_ID;
        for &c in pattern {
            if self.match_kind.is_leftmost_first() {
                // If state_id has an output, the descendants will never searched.
                let output = &mut self.states[state_id as usize].output;
                if output.0 != VALUE_INVALID {
                    return Ok(());
                }
            }

            if let Some(next_state_id) = self.get_child_id(state_id, c) {
                state_id = next_state_id;
            } else if let Ok(next_state_id) = self.states.len().try_into() {
                self.states[state_id as usize]
                    .edges
                    .push((c, next_state_id));
                self.states.push(SparseState::default());
                state_id = next_state_id;
            } else {
                let e = AutomatonScaleError {
                    msg: "A state id must be represented with u32".to_string(),
                };
                return Err(DaachorseError::AutomatonScale(e));
            }
        }

        let output = &mut self.states[state_id as usize].output;
        if output.0 != VALUE_INVALID {
            let e = DuplicatePatternError {
                pattern: pattern.to_vec(),
            };
            return Err(DaachorseError::DuplicatePattern(e));
        }
        *output = (value, pattern.len().try_into().unwrap());
        self.len += 1;
        Ok(())
    }

    fn build_fails(&mut self) -> Vec<u32> {
        let mut q = Vec::with_capacity(self.states.len());
        for &(_, child_id) in &self.states[ROOT_STATE_ID as usize].edges {
            q.push(child_id);
        }

        let mut qi = 0;
        while qi < q.len() {
            let state_id = q[qi] as usize;
            qi += 1;
            for i in 0..self.states[state_id].edges.len() {
                let (c, child_id) = self.states[state_id].edges[i];
                let mut fail_id = self.states[state_id].fail;
                let new_fail_id = loop {
                    if let Some(child_fail_id) = self.get_child_id(fail_id, c) {
                        break child_fail_id;
                    }
                    let next_fail_id = self.states[fail_id as usize].fail;
                    if fail_id == ROOT_STATE_ID && next_fail_id == ROOT_STATE_ID {
                        break ROOT_STATE_ID;
                    }
                    fail_id = next_fail_id;
                };
                self.states[child_id as usize].fail = new_fail_id;
                q.push(child_id);
            }
        }
        q
    }

    fn build_fails_leftmost(&mut self) -> Vec<u32> {
        let mut q = Vec::with_capacity(self.states.len());
        for &(_, child_id) in &self.states[ROOT_STATE_ID as usize].edges {
            q.push(child_id);
        }

        let mut qi = 0;
        while qi < q.len() {
            let state_id = q[qi] as usize;
            qi += 1;

            // Sets the output state to the dead fail.
            if self.states[state_id].output.0 != VALUE_INVALID {
                self.states[state_id].fail = DEAD_STATE_ID;
            }

            for i in 0..self.states[state_id].edges.len() {
                let (c, child_id) = self.states[state_id].edges[i];
                let mut fail_id = self.states[state_id].fail;

                // If the parent has the dead fail, the child also has the dead fail.
                let new_fail_id = if fail_id == DEAD_STATE_ID {
                    DEAD_STATE_ID
                } else {
                    loop {
                        if let Some(child_fail_id) = self.get_child_id(fail_id, c) {
                            break child_fail_id;
                        }
                        let next_fail_id = self.states[fail_id as usize].fail;
                        if next_fail_id == DEAD_STATE_ID {
                            break DEAD_STATE_ID;
                        }
                        if fail_id == ROOT_STATE_ID && next_fail_id == ROOT_STATE_ID {
                            break ROOT_STATE_ID;
                        }
                        fail_id = next_fail_id;
                    }
                };

                self.states[child_id as usize].fail = new_fail_id;
                q.push(child_id);
            }
        }
        q
    }

    fn build_outputs(&mut self, q: &[u32]) -> Result<(), DaachorseError> {
        // The queue (built in build_fails or _leftmost) will not have the root state id,
        // so in the following processing the output of the root state will not be handled.
        // But, there is no problem since Daachorse does not allow an empty pattern.
        debug_assert_ne!(q[0], ROOT_STATE_ID);

        let mut processed = vec![false; self.states.len()];

        // Builds an output sequence in which common parts are merged.
        for &state_id in q.iter().rev() {
            let s = &mut self.states[state_id as usize];
            if s.output.0 == VALUE_INVALID {
                continue;
            }

            if processed[state_id as usize] {
                debug_assert_ne!(s.output_pos, OUTPUT_POS_INVALID);
                continue;
            }
            debug_assert_eq!(s.output_pos, OUTPUT_POS_INVALID);
            processed[state_id as usize] = true;

            s.output_pos = self.outputs.len().try_into().unwrap();
            self.outputs.push(Output::new(s.output.0, s.output.1, true));
            Self::check_outputs_error(&self.outputs)?;

            let mut fail_id = state_id;
            loop {
                fail_id = self.states[fail_id as usize].fail;
                if fail_id == ROOT_STATE_ID || fail_id == DEAD_STATE_ID {
                    break;
                }

                let s = &mut self.states[fail_id as usize];
                if s.output.0 == VALUE_INVALID {
                    continue;
                }

                if processed[fail_id as usize] {
                    debug_assert_ne!(s.output_pos, OUTPUT_POS_INVALID);
                    let mut clone_pos = s.output_pos as usize;
                    debug_assert!(!self.outputs[clone_pos].is_begin());
                    while !self.outputs[clone_pos].is_begin() {
                        self.outputs.push(self.outputs[clone_pos]);
                        clone_pos += 1;
                    }
                    Self::check_outputs_error(&self.outputs)?;
                    break;
                }
                processed[fail_id as usize] = true;

                s.output_pos = self.outputs.len().try_into().unwrap();
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

        self.set_dummy_outputs(q, &processed);

        Ok(())
    }

    fn set_dummy_outputs(&mut self, q: &[u32], processed: &[bool]) {
        for &state_id in q {
            let state_id = state_id as usize;
            let s = &mut self.states[state_id];
            if processed[state_id] {
                debug_assert_ne!(s.output_pos, OUTPUT_POS_INVALID);
                continue;
            }
            debug_assert_eq!(s.output_pos, OUTPUT_POS_INVALID);
            debug_assert_eq!(s.output.0, VALUE_INVALID);

            let fail_id = self.states[state_id].fail;
            if fail_id != DEAD_STATE_ID {
                self.states[state_id].output_pos = self.states[fail_id as usize].output_pos;
            }
        }
    }

    #[inline(always)]
    fn check_outputs_error(outputs: &[Output]) -> Result<(), DaachorseError> {
        if outputs.len() > OUTPUT_POS_INVALID as usize {
            let e = AutomatonScaleError {
                msg: format!("outputs.len() must be <= {}", OUTPUT_POS_INVALID),
            };
            Err(DaachorseError::AutomatonScale(e))
        } else {
            Ok(())
        }
    }

    #[inline(always)]
    fn get_child_id(&self, state_id: u32, c: u8) -> Option<u32> {
        for &(cc, child_id) in &self.states[state_id as usize].edges {
            if c == cc {
                return Some(child_id);
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
            fail: ROOT_STATE_ID,
            output: (VALUE_INVALID, LENGTH_INVALID),
            output_pos: OUTPUT_POS_INVALID,
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
            next: DEAD_STATE_IDX,
            prev: DEAD_STATE_IDX,
        }
    }
}

impl Extra {
    #[inline(always)]
    const fn get_next(&self) -> u32 {
        self.next
    }

    #[inline(always)]
    const fn get_prev(&self) -> u32 {
        self.prev
    }

    #[inline(always)]
    fn set_next(&mut self, x: u32) {
        self.next = x;
    }

    #[inline(always)]
    fn set_prev(&mut self, x: u32) {
        self.prev = x;
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
    extras: [Extra; FREE_STATES as usize],
    head_idx: u32,
    match_kind: MatchKind,
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
        let init_capa = BLOCK_LEN.min(INIT_CAPACITY / BLOCK_LEN * BLOCK_LEN);
        Self {
            states: Vec::with_capacity(init_capa as usize),
            extras: [Extra::default(); FREE_STATES as usize],
            head_idx: DEAD_STATE_IDX,
            match_kind: MatchKind::default(),
        }
    }

    /// Specifies [`MatchKind`] to build.
    ///
    /// # Arguments
    ///
    /// * `kind` - Match kind.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::{DoubleArrayAhoCorasickBuilder, MatchKind};
    ///
    /// let patterns = vec!["ab", "abcd"];
    /// let pma = DoubleArrayAhoCorasickBuilder::new()
    ///           .match_kind(MatchKind::LeftmostLongest)
    ///           .build(&patterns)
    ///           .unwrap();
    ///
    /// let mut it = pma.leftmost_find_iter("abcd");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 4, 1), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    #[must_use]
    pub const fn match_kind(mut self, kind: MatchKind) -> Self {
        self.match_kind = kind;
        self
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
    ///   - `patterns` is empty,
    ///   - `patterns` contains entries of length zero,
    ///   - `patterns` contains duplicate entries,
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
    pub fn build<I, P>(self, patterns: I) -> Result<DoubleArrayAhoCorasick, DaachorseError>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<[u8]>,
    {
        let patvals = patterns
            .into_iter()
            .enumerate()
            .map(|(i, p)| (p, i.try_into().unwrap_or(VALUE_INVALID)));
        self.build_with_values(patvals)
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
    ///   - `patvals` is empty,
    ///   - `patvals` contains patterns of length zero,
    ///   - `patvals` contains duplicate patterns,
    ///   - `patvals` contains invalid values,
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
            match_kind: self.match_kind,
            num_states: nfa.states.len() - 1,
        })
    }

    fn build_sparse_nfa<I, P>(&mut self, patvals: I) -> Result<SparseNFA, DaachorseError>
    where
        I: IntoIterator<Item = (P, u32)>,
        P: AsRef<[u8]>,
    {
        let mut nfa = SparseNFA::new(self.match_kind);
        for (pattern, value) in patvals {
            nfa.add(pattern.as_ref(), value)?;
        }
        if nfa.len == 0 {
            let e = AutomatonScaleError {
                msg: "Pattern set must not be empty.".to_string(),
            };
            return Err(DaachorseError::AutomatonScale(e));
        }
        let q = match self.match_kind {
            MatchKind::Standard => nfa.build_fails(),
            MatchKind::LeftmostLongest | MatchKind::LeftmostFirst => nfa.build_fails_leftmost(),
        };
        nfa.build_outputs(&q)?;
        Ok(nfa)
    }

    fn build_double_array(&mut self, nfa: &SparseNFA) -> Result<(), DaachorseError> {
        self.init_array();

        let mut state_id_map = vec![DEAD_STATE_IDX; nfa.states.len()];
        state_id_map[ROOT_STATE_ID as usize] = ROOT_STATE_IDX;

        // Arranges base & check values
        for (i, state) in nfa.states.iter().enumerate() {
            if i == DEAD_STATE_ID as usize {
                continue;
            }

            let idx = state_id_map[i] as usize;
            debug_assert_ne!(idx, DEAD_STATE_IDX as usize);

            if state.edges.is_empty() {
                continue;
            }

            let base = self.find_base(&state.edges);
            if base as usize >= self.states.len() {
                self.extend_array()?;
            }

            for &(c, child_id) in &state.edges {
                let child_idx = base ^ u32::from(c);
                self.fix_state(child_idx);
                self.states[child_idx as usize].set_check(c);
                state_id_map[child_id as usize] = child_idx;
            }
            self.states[idx].set_base(base);
            self.extra_mut_ref(base).use_base();
        }

        // Sets fail & output_pos values
        for (i, state) in nfa.states.iter().enumerate() {
            if i == DEAD_STATE_ID as usize {
                continue;
            }

            let idx = state_id_map[i] as usize;
            debug_assert_ne!(idx, DEAD_STATE_IDX as usize);

            self.states[idx].set_output_pos(state.output_pos);

            let fail_id = state.fail;
            if fail_id == DEAD_STATE_ID {
                self.states[idx].set_fail(DEAD_STATE_IDX);
            } else {
                let fail_idx = state_id_map[fail_id as usize];
                debug_assert_ne!(fail_idx, DEAD_STATE_IDX);
                if fail_idx > FAIL_MAX {
                    let e = AutomatonScaleError {
                        msg: format!("fail_idx must be <= {}", FAIL_MAX),
                    };
                    return Err(DaachorseError::AutomatonScale(e));
                }
                self.states[idx].set_fail(fail_idx);
            }
        }

        // If the root block has not been closed, it has to be closed for setting CHECK[0] to a valid value.
        if self.states.len() <= FREE_STATES as usize {
            self.close_block(0);
        }

        while self.head_idx != DEAD_STATE_IDX {
            let block_idx = self.head_idx / BLOCK_LEN;
            self.close_block(block_idx);
        }

        self.states.shrink_to_fit();

        Ok(())
    }

    fn init_array(&mut self) {
        self.states.resize(BLOCK_LEN as usize, State::default());
        self.head_idx = ROOT_STATE_IDX;

        for i in 0..BLOCK_LEN {
            self.init_extra(i);
            if i == 0 {
                self.extra_mut_ref(i).set_prev(BLOCK_LEN - 1);
            } else {
                self.extra_mut_ref(i).set_prev(i - 1);
            }
            if i == BLOCK_LEN - 1 {
                self.extra_mut_ref(i).set_next(0);
            } else {
                self.extra_mut_ref(i).set_next(i + 1);
            }
        }

        self.fix_state(ROOT_STATE_IDX);
        self.fix_state(DEAD_STATE_IDX);
    }

    #[inline(always)]
    fn fix_state(&mut self, i: u32) {
        debug_assert!(!self.extra_ref(i).is_used_index());
        self.extra_mut_ref(i).use_index();

        let next = self.extra_ref(i).get_next();
        let prev = self.extra_ref(i).get_prev();
        self.extra_mut_ref(prev).set_next(next);
        self.extra_mut_ref(next).set_prev(prev);

        if self.head_idx == i {
            if next == i {
                self.head_idx = DEAD_STATE_IDX;
            } else {
                self.head_idx = next;
            }
        }
    }

    #[inline(always)]
    fn find_base(&self, edges: &[(u8, u32)]) -> u32 {
        if self.head_idx == DEAD_STATE_IDX {
            return self.states.len().try_into().unwrap();
        }
        let mut idx = self.head_idx;
        loop {
            debug_assert!(!self.extra_ref(idx).is_used_index());
            let base = idx ^ u32::from(edges[0].0);
            if self.check_valid_base(base, edges) {
                return base;
            }
            idx = self.extra_ref(idx).get_next();
            if idx == self.head_idx {
                break;
            }
        }
        self.states.len().try_into().unwrap()
    }

    #[inline(always)]
    fn check_valid_base(&self, base: u32, edges: &[(u8, u32)]) -> bool {
        if self.extra_ref(base).is_used_base() {
            return false;
        }
        for &(c, _) in edges {
            let idx = base ^ u32::from(c);
            if self.extra_ref(idx).is_used_index() {
                return false;
            }
        }
        true
    }

    fn extend_array(&mut self) -> Result<(), DaachorseError> {
        let old_len = self.states.len().try_into().unwrap();
        // The following condition is same as `new_len > STATE_INDEX_IVALID`.
        // We use the following condition to avoid overflow.
        if old_len > std::u32::MAX - BLOCK_LEN {
            let e = AutomatonScaleError {
                msg: "An index of states must be represented with u32".to_string(),
            };
            return Err(DaachorseError::AutomatonScale(e));
        }
        let new_len = old_len + BLOCK_LEN;

        // It is necessary to close the head block before appending a new block
        // so that the builder works in extras[..FREE_STATES].
        if FREE_STATES <= old_len {
            self.close_block((old_len - FREE_STATES) / BLOCK_LEN);
        }

        for i in old_len..new_len {
            self.states.push(State::default());
            self.init_extra(i);
            self.extra_mut_ref(i).set_next(i + 1);
            self.extra_mut_ref(i).set_prev(i - 1);
        }

        if self.head_idx == DEAD_STATE_IDX {
            self.extra_mut_ref(old_len).set_prev(new_len - 1);
            self.extra_mut_ref(new_len - 1).set_next(old_len);
            self.head_idx = old_len;
        } else {
            let head_idx = self.head_idx;
            let tail_idx = self.extra_ref(head_idx).get_prev();
            self.extra_mut_ref(old_len).set_prev(tail_idx);
            self.extra_mut_ref(tail_idx).set_next(old_len);
            self.extra_mut_ref(new_len - 1).set_next(head_idx);
            self.extra_mut_ref(head_idx).set_prev(new_len - 1);
        }

        Ok(())
    }

    /// Note: Assumes all the previous blocks are closed.
    fn close_block(&mut self, block_idx: u32) {
        let beg_idx = block_idx * BLOCK_LEN;
        let end_idx = beg_idx + BLOCK_LEN;

        if block_idx == 0 || self.head_idx < end_idx {
            self.remove_invalid_checks(block_idx);
        }
        while self.head_idx < end_idx && self.head_idx != DEAD_STATE_IDX {
            self.fix_state(self.head_idx);
        }
    }

    fn remove_invalid_checks(&mut self, block_idx: u32) {
        let beg_idx = block_idx * BLOCK_LEN;
        let end_idx = beg_idx + BLOCK_LEN;

        let unused_base = {
            let mut i = beg_idx;
            while i < end_idx {
                if !self.extra_ref(i).is_used_base() {
                    break;
                }
                i += 1;
            }
            i
        };
        debug_assert_ne!(unused_base, end_idx);

        for c in 0..=BLOCK_MAX {
            let idx = unused_base ^ u32::from(c);
            if idx == ROOT_STATE_IDX
                || idx == DEAD_STATE_IDX
                || !self.extra_ref(idx).is_used_index()
            {
                self.states[idx as usize].set_check(c);
            }
        }
    }

    #[inline(always)]
    fn init_extra(&mut self, i: u32) {
        debug_assert!(self.states.len() <= (i + FREE_STATES) as usize);
        self.extras[(i % FREE_STATES) as usize] = Extra::default();
    }

    #[inline(always)]
    fn extra_ref(&self, i: u32) -> &Extra {
        debug_assert!(self.states.len() <= (i + FREE_STATES) as usize);
        &self.extras[(i % FREE_STATES) as usize]
    }

    #[inline(always)]
    fn extra_mut_ref(&mut self, i: u32) -> &mut Extra {
        debug_assert!(self.states.len() <= (i + FREE_STATES) as usize);
        &mut self.extras[(i % FREE_STATES) as usize]
    }
}
