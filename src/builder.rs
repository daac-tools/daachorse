use crate::errors::{
    AutomatonScaleError, DaachorseError, DuplicatePatternError, InvalidArgumentError,
    PatternScaleError,
};
use crate::{
    DoubleArrayAhoCorasick, Output, State, BLOCK_LEN, FAIL_INVALID, FREE_STATES, OUTPOS_INVALID,
    PATTERN_ID_INVALID, PATTERN_LEN_INVALID, STATE_IDX_INVALID,
};

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

        // If the root block has not been closed, it has to be closed for setting CHECK[0] to a valid value.
        if self.states.len() <= FREE_STATES {
            self.close_block(0);
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
                debug_assert!(self.states[da_node_idx].output_pos().is_some());
                continue;
            }
            debug_assert!(self.states[da_node_idx].output_pos().is_none());

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
                    let mut clone_pos = self.states[da_node_idx].output_pos().unwrap() as usize;
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
                debug_assert!(self.states[da_node_idx].output_pos().is_some());
                continue;
            }
            debug_assert!(self.states[da_node_idx].output_pos().is_none());
            debug_assert_eq!(pattern_id, PATTERN_ID_INVALID);

            let fail_idx = self.states[da_node_idx].fail() as usize;
            if let Some(output_pos) = self.states[fail_idx].output_pos() {
                self.states[da_node_idx].set_output_pos(output_pos);
            }
        }
    }

    #[inline(always)]
    fn get_child_index(&self, idx: usize, c: u8) -> Option<usize> {
        self.states[idx].base().and_then(|base| {
            let child_idx = (base ^ c as u32) as usize;
            if self.states[child_idx].check() == c {
                Some(child_idx)
            } else {
                None
            }
        })
    }
}
