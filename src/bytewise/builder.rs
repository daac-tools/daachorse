use core::num::NonZeroU32;

use alloc::vec::Vec;

use crate::bytewise::{
    BuildHelper, DoubleArrayAhoCorasick, MatchKind, State, DEAD_STATE_IDX, ROOT_STATE_IDX,
};
use crate::errors::{DaachorseError, Result};
use crate::intpack::U24;
use crate::nfa_builder::{NfaBuilder, DEAD_STATE_ID, ROOT_STATE_ID};
use crate::utils::FromU32;

// The length of each double-array block.
const BLOCK_LEN: u32 = 256;

// Specialized [`NfaBuilder`] handling labels of `u8`.
type BytewiseNfaBuilder<V> = NfaBuilder<u8, V>;

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
    /// A fixed length of memory is allocated in proportion to this value in construction. If an
    /// allocation error occurs during building the automaton even though the pattern set is small,
    /// try setting a smaller value.
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

    /// Builds and returns a new [`DoubleArrayAhoCorasick`] from input patterns. The value `i` is
    /// automatically associated with `patterns[i]`.
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
    pub fn build<I, P, V>(self, patterns: I) -> Result<DoubleArrayAhoCorasick<V>>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<[u8]>,
        V: Copy + Default + TryFrom<usize>,
    {
        // The following code implicitly replaces large indices with 0,
        // but build_with_values() returns an error variant for such iterators.
        let patvals = patterns
            .into_iter()
            .enumerate()
            .map(|(i, p)| (p, V::try_from(i).unwrap_or_default()));
        self.build_with_values(patvals)
    }

    /// Builds and returns a new [`DoubleArrayAhoCorasick`] from input pattern-value pairs.
    ///
    /// # Arguments
    ///
    /// * `patvals` - List of pattern-value pairs, where the value is of type [`u32`] and less than
    /// [`u32::MAX`].
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
    pub fn build_with_values<I, P, V>(mut self, patvals: I) -> Result<DoubleArrayAhoCorasick<V>>
    where
        I: IntoIterator<Item = (P, V)>,
        P: AsRef<[u8]>,
        V: Copy + Default,
    {
        let nfa = self.build_sparse_nfa(patvals)?;
        self.build_double_array(&nfa)?;

        // -1 is for dead state
        let num_states = u32::try_from(nfa.states.len() - 1)
            .map_err(|_| DaachorseError::automaton_scale("num_states", u32::MAX))?;

        Ok(DoubleArrayAhoCorasick {
            states: self.states,
            outputs: nfa.outputs,
            match_kind: self.match_kind,
            num_states,
        })
    }

    fn build_sparse_nfa<I, P, V>(&mut self, patvals: I) -> Result<BytewiseNfaBuilder<V>>
    where
        I: IntoIterator<Item = (P, V)>,
        P: AsRef<[u8]>,
        V: Copy + Default,
    {
        let mut nfa = BytewiseNfaBuilder::new(self.match_kind);
        for (pattern, value) in patvals {
            nfa.add(pattern.as_ref(), value)?;
        }
        if nfa.len == 0 {
            return Err(DaachorseError::invalid_argument("patvals.len()", ">=", 1));
        }
        if nfa.len > usize::from_u32(U24::MAX) {
            return Err(DaachorseError::automaton_scale("patvals.len()", U24::MAX));
        }
        let q = match self.match_kind {
            MatchKind::Standard => nfa.build_fails(),
            MatchKind::LeftmostLongest | MatchKind::LeftmostFirst => nfa.build_fails_leftmost(),
        };
        nfa.build_outputs(&q);
        Ok(nfa)
    }

    fn build_double_array<V>(&mut self, nfa: &BytewiseNfaBuilder<V>) -> Result<()> {
        let mut helper = self.init_array()?;

        let mut state_id_map = vec![DEAD_STATE_IDX; nfa.states.len()];
        state_id_map[usize::from_u32(ROOT_STATE_ID)] = ROOT_STATE_IDX;

        // Arranges base & check values
        let mut stack = vec![ROOT_STATE_ID];
        let mut labels = vec![];

        while let Some(state_id) = stack.pop() {
            debug_assert_ne!(state_id, DEAD_STATE_ID);
            let state = &nfa.states[usize::from_u32(state_id)];

            let state_idx = usize::from_u32(state_id_map[usize::from_u32(state_id)]);
            debug_assert_ne!(state_idx, usize::from_u32(DEAD_STATE_IDX));

            let s = &state.borrow();
            if s.edges.is_empty() {
                continue;
            }

            labels.clear();
            s.edges.keys().for_each(|&k| labels.push(k));

            let base = self.find_base(&labels, &helper);
            if usize::from_u32(base.get()) >= self.states.len() {
                self.extend_array(&mut helper)?;
            }

            for (&c, &child_id) in &s.edges {
                let child_idx = base.get() ^ u32::from(c);
                helper.use_index(child_idx);
                self.states[usize::from_u32(child_idx)].set_check(c);
                state_id_map[usize::from_u32(child_id)] = child_idx;
                stack.push(child_id);
            }
            self.states[state_idx].set_base(base);
            helper.use_base(base);
        }

        // Sets fail & output_pos values
        for (i, state) in nfa.states.iter().enumerate() {
            if i == usize::from_u32(DEAD_STATE_ID) {
                continue;
            }

            let idx = usize::from_u32(state_id_map[i]);
            debug_assert_ne!(idx, usize::from_u32(DEAD_STATE_IDX));

            let s = &state.borrow();
            self.states[idx].set_output_pos(s.output_pos)?;

            let fail_id = s.fail;
            if fail_id == DEAD_STATE_ID {
                self.states[idx].set_fail(DEAD_STATE_IDX);
            } else {
                let fail_idx = state_id_map[usize::from_u32(fail_id)];
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

    fn init_array(&mut self) -> Result<BuildHelper> {
        self.states
            .resize(usize::from_u32(BLOCK_LEN), State::default());
        let mut helper = BuildHelper::new(BLOCK_LEN, self.num_free_blocks)?;
        helper.push_block().unwrap();
        helper.use_index(ROOT_STATE_IDX);
        helper.use_index(DEAD_STATE_IDX);
        Ok(helper)
    }

    #[inline(always)]
    fn find_base(&self, labels: &[u8], helper: &BuildHelper) -> NonZeroU32 {
        for idx in helper.vacant_iter() {
            let base = idx ^ u32::from(labels[0]);
            if let Some(base) = Self::check_valid_base(base, labels, helper) {
                return base;
            }
        }
        // len() is not 0 since states has at least BLOCK_LEN items.
        NonZeroU32::new(u32::try_from(self.states.len()).unwrap()).unwrap()
    }

    #[inline(always)]
    fn check_valid_base(base: u32, labels: &[u8], helper: &BuildHelper) -> Option<NonZeroU32> {
        if helper.is_used_base(base) {
            return None;
        }
        for &c in labels {
            let idx = base ^ u32::from(c);
            if helper.is_used_index(idx) {
                return None;
            }
        }
        NonZeroU32::new(base)
    }

    fn extend_array(&mut self, helper: &mut BuildHelper) -> Result<()> {
        if self.states.len() > usize::from_u32(u32::MAX - BLOCK_LEN) {
            return Err(DaachorseError::automaton_scale("states.len()", u32::MAX));
        }

        if let Some(closed_block_idx) = helper.dropped_block() {
            self.remove_invalid_checks(closed_block_idx, helper);
        }

        helper.push_block()?;
        self.states.resize(
            self.states.len() + usize::from_u32(BLOCK_LEN),
            State::default(),
        );

        Ok(())
    }

    /// Embeds valid CHECK values for all vacant elements in the block to avoid invalid transitions.
    fn remove_invalid_checks(&mut self, block_idx: u32, helper: &BuildHelper) {
        if let Some(unused_base) = helper.unused_base_in_block(block_idx) {
            for c in u8::MIN..=u8::MAX {
                let idx = unused_base ^ u32::from(c);
                if idx == ROOT_STATE_IDX || idx == DEAD_STATE_IDX || !helper.is_used_index(idx) {
                    self.states[usize::from_u32(idx)].set_check(c);
                }
            }
        }
    }
}
