use alloc::vec::Vec;

use crate::errors::{DaachorseError, Result};
use crate::nfa_builder::{NfaBuilder, DEAD_STATE_ID, ROOT_STATE_ID};
use crate::{
    BuildHelper, DoubleArrayAhoCorasick, MatchKind, State, DEAD_STATE_IDX, OUTPUT_POS_MAX,
    ROOT_STATE_IDX,
};

// The maximum value of each double-array block.
const BLOCK_MAX: u8 = u8::MAX;
// The length of each double-array block.
const BLOCK_LEN: u32 = BLOCK_MAX as u32 + 1;

// Specialized [`NfaBuilder`] handling labels of `u8`.
type BytewiseNfaBuilder = NfaBuilder<u8>;

/// Builder of [`DoubleArrayAhoCorasick`].
pub struct DoubleArrayAhoCorasickBuilder {
    states: Vec<State>,
    match_kind: MatchKind,
    num_free_blocks: u32,
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
    #[must_use]
    pub const fn new() -> Self {
        Self {
            states: vec![],
            match_kind: MatchKind::Standard,
            num_free_blocks: 16,
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

    /// Specifies the number of last blocks to search bases.
    ///
    /// The smaller the number is, the faster the construction time will be;
    /// however, the memory efficiency can be degraded.
    ///
    /// A fixed length of memory is allocated in proportion to this value in construction.
    /// If an allocation error occurs during building the automaton even though the pattern set is
    /// small, try setting a smaller value.
    ///
    /// # Arguments
    ///
    /// * `n` - The number of last blocks.
    ///
    /// # Panics
    ///
    /// `n` must be greater than or equal to 1.
    #[must_use]
    pub fn num_free_blocks(mut self, n: u32) -> Self {
        assert!(n >= 1);
        self.num_free_blocks = n;
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
    pub fn build<I, P>(self, patterns: I) -> Result<DoubleArrayAhoCorasick>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<[u8]>,
    {
        // The following code implicitly replaces large indices with 0,
        // but build_with_values() returns an error variant for such iterators.
        let patvals = patterns
            .into_iter()
            .enumerate()
            .map(|(i, p)| (p, i.try_into().unwrap_or(0)));
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
    pub fn build_with_values<I, P>(mut self, patvals: I) -> Result<DoubleArrayAhoCorasick>
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

    fn build_sparse_nfa<I, P>(&mut self, patvals: I) -> Result<BytewiseNfaBuilder>
    where
        I: IntoIterator<Item = (P, u32)>,
        P: AsRef<[u8]>,
    {
        let mut nfa = BytewiseNfaBuilder::new(self.match_kind);
        for (pattern, value) in patvals {
            nfa.add(pattern.as_ref(), value)?;
        }
        if nfa.len == 0 {
            return Err(DaachorseError::invalid_argument("patvals.len()", ">=", 1));
        }
        if nfa.len > OUTPUT_POS_MAX as usize {
            return Err(DaachorseError::automaton_scale(
                "patvals.len()",
                OUTPUT_POS_MAX,
            ));
        }
        let q = match self.match_kind {
            MatchKind::Standard => nfa.build_fails(),
            MatchKind::LeftmostLongest | MatchKind::LeftmostFirst => nfa.build_fails_leftmost(),
        };
        nfa.build_outputs(&q);
        Ok(nfa)
    }

    fn build_double_array(&mut self, nfa: &BytewiseNfaBuilder) -> Result<()> {
        let mut helper = self.init_array();

        let mut state_id_map = vec![DEAD_STATE_IDX; nfa.states.len()];
        state_id_map[ROOT_STATE_ID as usize] = ROOT_STATE_IDX;

        // Arranges base & check values
        let mut stack = vec![ROOT_STATE_ID];
        let mut labels = vec![];

        while let Some(state_id) = stack.pop() {
            debug_assert_ne!(state_id, DEAD_STATE_ID);
            let state = &nfa.states[state_id as usize];

            let state_idx = state_id_map[state_id as usize] as usize;
            debug_assert_ne!(state_idx, DEAD_STATE_IDX as usize);

            let s = &state.borrow();
            if s.edges.is_empty() {
                continue;
            }

            labels.clear();
            s.edges.keys().for_each(|&k| labels.push(k));

            let base = self.find_base(&labels, &helper);
            if base as usize >= self.states.len() {
                self.extend_array(&mut helper)?;
            }

            for (&c, &child_id) in &s.edges {
                let child_idx = base ^ u32::from(c);
                helper.use_index(child_idx);
                self.states[child_idx as usize].set_check(c);
                state_id_map[child_id as usize] = child_idx;
                stack.push(child_id);
            }
            self.states[state_idx].set_base(base);
            helper.use_base(base);
        }

        // Sets fail & output_pos values
        for (i, state) in nfa.states.iter().enumerate() {
            if i == DEAD_STATE_ID as usize {
                continue;
            }

            let idx = state_id_map[i] as usize;
            debug_assert_ne!(idx, DEAD_STATE_IDX as usize);

            let s = &state.borrow();
            self.states[idx].set_output_pos(s.output_pos)?;

            let fail_id = s.fail;
            if fail_id == DEAD_STATE_ID {
                self.states[idx].set_fail(DEAD_STATE_IDX);
            } else {
                let fail_idx = state_id_map[fail_id as usize];
                debug_assert_ne!(fail_idx, DEAD_STATE_IDX);
                self.states[idx].set_fail(fail_idx);
            }
        }

        for closed_block_idx in helper.active_block_range() {
            self.remove_invalid_checks(closed_block_idx, &helper);
        }
        self.states.shrink_to_fit();

        Ok(())
    }

    fn init_array(&mut self) -> BuildHelper {
        self.states
            .resize(usize::try_from(BLOCK_LEN).unwrap(), State::default());
        let mut helper = BuildHelper::new(BLOCK_LEN, self.num_free_blocks);
        helper.push_block().unwrap();
        helper.use_index(ROOT_STATE_IDX);
        helper.use_index(DEAD_STATE_IDX);
        helper
    }

    #[inline(always)]
    fn find_base(&self, labels: &[u8], helper: &BuildHelper) -> u32 {
        for idx in helper.vacant_iter() {
            let base = idx ^ u32::from(labels[0]);
            if self.check_valid_base(base, labels, helper) {
                return base;
            }
        }
        self.states.len().try_into().unwrap()
    }

    #[inline(always)]
    fn check_valid_base(&self, base: u32, labels: &[u8], helper: &BuildHelper) -> bool {
        if helper.is_used_base(base) {
            return false;
        }
        for &c in labels {
            let idx = base ^ u32::from(c);
            if helper.is_used_index(idx) {
                return false;
            }
        }
        true
    }

    fn extend_array(&mut self, helper: &mut BuildHelper) -> Result<()> {
        if self.states.len() > usize::try_from(u32::MAX - BLOCK_LEN).unwrap() {
            return Err(DaachorseError::automaton_scale("states.len()", u32::MAX));
        }

        if let Some(closed_block_idx) = helper.dropped_block() {
            self.remove_invalid_checks(closed_block_idx, helper);
        }

        helper.push_block()?;
        (0..BLOCK_LEN).for_each(|_| self.states.push(State::default()));

        Ok(())
    }

    /// Embeds valid CHECK values for all vacant elements in the block
    /// to avoid invalid transitions.
    fn remove_invalid_checks(&mut self, block_idx: u32, helper: &BuildHelper) {
        if let Some(unused_base) = helper.unused_base_in_block(block_idx) {
            for c in 0..=BLOCK_MAX {
                let idx = unused_base ^ u32::from(c);
                if idx == ROOT_STATE_IDX || idx == DEAD_STATE_IDX || !helper.is_used_index(idx) {
                    self.states[idx as usize].set_check(c);
                }
            }
        }
    }
}
