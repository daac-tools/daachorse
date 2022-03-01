use alloc::vec::Vec;

use crate::errors::{DaachorseError, Result};
use crate::nfa_builder::{NfaBuilder, DEAD_STATE_ID, ROOT_STATE_ID, VALUE_INVALID};
use crate::{DoubleArrayAhoCorasick, MatchKind, State, DEAD_STATE_IDX, FAIL_MAX, ROOT_STATE_IDX};

// The maximum value of each double-array block.
const BLOCK_MAX: u8 = u8::MAX;
// The length of each double-array block.
const BLOCK_LEN: u32 = BLOCK_MAX as u32 + 1;

// Specialized [`NfaBuilder`] handling labels of `u8`.
type BytewiseNfaBuilder = NfaBuilder<u8>;

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
    extras: Vec<Extra>,
    head_idx: u32,
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
    pub const fn new() -> Self {
        Self {
            states: vec![],
            extras: vec![],
            head_idx: DEAD_STATE_IDX,
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
    /// When the RAM capacity is small, this should be a small value.
    ///
    /// # Arguments
    ///
    /// * `n` - The number of last blocks.
    ///
    /// # Panics
    ///
    /// `n` must be greater than or equal to 1.
    #[must_use]
    pub const fn num_free_blocks(mut self, n: u32) -> Self {
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
        let q = match self.match_kind {
            MatchKind::Standard => nfa.build_fails(),
            MatchKind::LeftmostLongest | MatchKind::LeftmostFirst => nfa.build_fails_leftmost(),
        };
        nfa.build_outputs(&q)?;
        Ok(nfa)
    }

    fn build_double_array(&mut self, nfa: &BytewiseNfaBuilder) -> Result<()> {
        self.init_array();

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

            let base = self.find_base(&labels);
            if base as usize >= self.states.len() {
                self.extend_array()?;
            }

            for (&c, &child_id) in &s.edges {
                let child_idx = base ^ u32::from(c);
                self.fix_state(child_idx);
                self.states[child_idx as usize].set_check(c);
                state_id_map[child_id as usize] = child_idx;
                stack.push(child_id);
            }
            self.states[state_idx].set_base(base);
            self.extra_mut_ref(base).use_base();
        }

        // Sets fail & output_pos values
        for (i, state) in nfa.states.iter().enumerate() {
            if i == DEAD_STATE_ID as usize {
                continue;
            }

            let idx = state_id_map[i] as usize;
            debug_assert_ne!(idx, DEAD_STATE_IDX as usize);

            let s = &state.borrow();
            self.states[idx].set_output_pos(s.output_pos);

            let fail_id = s.fail;
            if fail_id == DEAD_STATE_ID {
                self.states[idx].set_fail(DEAD_STATE_IDX);
            } else {
                let fail_idx = state_id_map[fail_id as usize];
                debug_assert_ne!(fail_idx, DEAD_STATE_IDX);
                if fail_idx > FAIL_MAX {
                    return Err(DaachorseError::automaton_scale("fail_idx", FAIL_MAX));
                }
                self.states[idx].set_fail(fail_idx);
            }
        }

        // If the root block has not been closed, it has to be closed for setting CHECK[0] to a valid value.
        if self.states.len() <= self.extras.len() {
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
        self.extras
            .resize((BLOCK_LEN * self.num_free_blocks) as usize, Extra::default());
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
    fn find_base(&self, labels: &[u8]) -> u32 {
        if self.head_idx == DEAD_STATE_IDX {
            return self.states.len().try_into().unwrap();
        }
        let mut idx = self.head_idx;
        loop {
            debug_assert!(!self.extra_ref(idx).is_used_index());
            let base = idx ^ u32::from(labels[0]);
            if self.check_valid_base(base, labels) {
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
    fn check_valid_base(&self, base: u32, labels: &[u8]) -> bool {
        if self.extra_ref(base).is_used_base() {
            return false;
        }
        for &c in labels {
            let idx = base ^ u32::from(c);
            if self.extra_ref(idx).is_used_index() {
                return false;
            }
        }
        true
    }

    fn extend_array(&mut self) -> Result<()> {
        let old_len = self.states.len().try_into().unwrap();
        // The following condition is same as `new_len > STATE_INDEX_IVALID`.
        // We use the following condition to avoid overflow.
        if old_len > u32::MAX - BLOCK_LEN {
            return Err(DaachorseError::automaton_scale("states.len()", u32::MAX));
        }
        let new_len = old_len + BLOCK_LEN;

        // It is necessary to close the head block before appending a new block
        // so that the builder works in extras[..FREE_STATES].
        if self.extras.len() <= old_len as usize {
            #[allow(clippy::cast_possible_truncation)]
            self.close_block((old_len - self.extras.len() as u32) / BLOCK_LEN);
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
        let free_states = self.extras.len();
        debug_assert!(self.states.len() <= i as usize + free_states);
        self.extras[i as usize % free_states] = Extra::default();
    }

    #[inline(always)]
    fn extra_ref(&self, i: u32) -> &Extra {
        let free_states = self.extras.len();
        debug_assert!(self.states.len() <= i as usize + free_states);
        &self.extras[i as usize % free_states]
    }

    #[inline(always)]
    fn extra_mut_ref(&mut self, i: u32) -> &mut Extra {
        let free_states = self.extras.len();
        debug_assert!(self.states.len() <= i as usize + free_states);
        &mut self.extras[i as usize % free_states]
    }
}
