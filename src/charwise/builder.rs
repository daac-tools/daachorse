use core::num::NonZeroU32;

use alloc::vec::Vec;

use crate::charwise::{CharwiseDoubleArrayAhoCorasick, CodeMapper, MatchKind, State};
use crate::errors::{DaachorseError, Result};
use crate::nfa_builder::NfaBuilder;

use crate::charwise::{DEAD_STATE_IDX, ROOT_STATE_IDX};
use crate::nfa_builder::{DEAD_STATE_ID, ROOT_STATE_ID, VALUE_INVALID};

// Specialized [`NfaBuilder`] handling labels of `char`.
type CharwiseNfaBuilder = NfaBuilder<char>;

/// Builder for [`CharwiseDoubleArrayAhoCorasick`].
pub struct CharwiseDoubleArrayAhoCorasickBuilder {
    states: Vec<State>,
    mapper: CodeMapper,
    match_kind: MatchKind,
}

impl Default for CharwiseDoubleArrayAhoCorasickBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl CharwiseDoubleArrayAhoCorasickBuilder {
    /// Creates a new [`CharwiseDoubleArrayAhoCorasickBuilder`].
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasickBuilder;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    ///
    /// let builder = CharwiseDoubleArrayAhoCorasickBuilder::new();
    /// let pma = builder.build(patterns).unwrap();
    ///
    /// let mut it = pma.find_iter("全世界中に");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((12, 15, 2), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn new() -> Self {
        Self {
            states: vec![],
            mapper: CodeMapper::default(),
            match_kind: MatchKind::Standard,
        }
    }

    /// Specifies [`MatchKind`] to build.
    ///
    /// # Arguments
    ///
    /// * `kind` - Match kind.
    #[must_use]
    pub const fn match_kind(mut self, kind: MatchKind) -> Self {
        self.match_kind = kind;
        self
    }

    /// Builds and returns a new [`CharwiseDoubleArrayAhoCorasick`] from input patterns.
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
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasickBuilder;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new().build(patterns).unwrap();
    ///
    /// let mut it = pma.find_iter("全世界中に");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((12, 15, 2), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn build<I, P>(self, patterns: I) -> Result<CharwiseDoubleArrayAhoCorasick>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<str>,
    {
        let patvals = patterns
            .into_iter()
            .enumerate()
            .map(|(i, p)| (p, i.try_into().unwrap_or(VALUE_INVALID)));
        self.build_with_values(patvals)
    }

    /// Builds and returns a new [`CharwiseDoubleArrayAhoCorasick`] from input pattern-value pairs.
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
    /// use daachorse::charwise::CharwiseDoubleArrayAhoCorasickBuilder;
    ///
    /// let patvals = vec![("全世界", 0), ("世界", 10), ("に", 100)];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new().build_with_values(patvals).unwrap();
    ///
    /// let mut it = pma.find_iter("全世界中に");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((12, 15, 100), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    pub fn build_with_values<I, P>(mut self, patvals: I) -> Result<CharwiseDoubleArrayAhoCorasick>
    where
        I: IntoIterator<Item = (P, u32)>,
        P: AsRef<str>,
    {
        let nfa = self.build_original_nfa_and_mapper(patvals)?;
        let num_states = nfa.states.len() - 1; // -1 is for dead state

        self.build_double_array(&nfa)?;

        Ok(CharwiseDoubleArrayAhoCorasick {
            states: self.states,
            mapper: self.mapper,
            outputs: nfa.outputs,
            match_kind: self.match_kind,
            num_states,
        })
    }

    fn build_original_nfa_and_mapper<I, P>(&mut self, patvals: I) -> Result<CharwiseNfaBuilder>
    where
        I: IntoIterator<Item = (P, u32)>,
        P: AsRef<str>,
    {
        let mut nfa = CharwiseNfaBuilder::new(self.match_kind);
        let mut freqs = vec![];
        {
            let mut chars = vec![];
            for (pattern, value) in patvals {
                chars.clear();
                pattern.as_ref().chars().for_each(|c| chars.push(c));
                nfa.add(&chars, value)?;

                for &c in &chars {
                    let c = usize::try_from(u32::from(c)).unwrap();
                    if freqs.len() <= c {
                        freqs.resize(c + 1, 0);
                    }
                    freqs[c] += 1;
                }
            }
        }
        self.mapper = CodeMapper::new(&freqs);

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

    fn build_double_array(&mut self, nfa: &CharwiseNfaBuilder) -> Result<()> {
        self.init_array();

        let mut state_id_map = vec![DEAD_STATE_IDX; nfa.states.len()];
        state_id_map[ROOT_STATE_ID as usize] = ROOT_STATE_IDX;

        // Arranges base & check values
        let mut stack = vec![ROOT_STATE_ID];
        let mut mapped = vec![];

        while let Some(state_id) = stack.pop() {
            debug_assert_ne!(state_id, DEAD_STATE_ID);
            let state = &nfa.states[state_id as usize];

            let state_idx = state_id_map[state_id as usize];
            debug_assert_ne!(state_idx, DEAD_STATE_IDX);

            let s = &state.borrow();
            if s.edges.is_empty() {
                continue;
            }

            mapped.clear();
            for (&label, &child_id) in &s.edges {
                mapped.push((self.mapper.get(label).unwrap(), child_id));
            }
            mapped.sort_by(|(c1, _), (c2, _)| c1.cmp(c2));

            let base = self.find_base(&mapped);
            let max_idx = base + i32::try_from(mapped.last().unwrap().0).unwrap();

            let max_idx = u32::try_from(max_idx).unwrap();
            if self.states.len() <= max_idx as usize {
                self.extend_array(max_idx);
            }

            for &(c, child_id) in &mapped {
                let child_idx = base + i32::try_from(c).unwrap();

                let child_idx = u32::try_from(child_idx).unwrap();
                self.fix_state(child_idx);
                self.states[child_idx as usize].set_check(state_idx);

                state_id_map[child_id as usize] = child_idx;
                stack.push(child_id);
            }
            self.states[state_idx as usize].set_base(base);
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
                self.states[idx].set_fail(fail_idx);
            }
        }

        self.states.shrink_to_fit();
        Ok(())
    }

    fn init_array(&mut self) {
        self.states.resize(2, State::default());
        self.set_next(DEAD_STATE_IDX, DEAD_STATE_IDX);
        self.set_prev(DEAD_STATE_IDX, DEAD_STATE_IDX);
        self.set_fixed(ROOT_STATE_IDX);
    }

    #[inline(always)]
    fn fix_state(&mut self, idx: u32) {
        debug_assert_ne!(idx, DEAD_STATE_IDX);
        debug_assert!(!self.is_fixed(idx));

        let next = self.get_next(idx);
        let prev = self.get_prev(idx);
        self.set_next(prev, next);
        self.set_prev(next, prev);
        self.set_fixed(idx);
    }

    // edges = [(char, next_id)] sorted by char
    #[inline(always)]
    fn find_base(&self, edges: &[(u32, u32)]) -> i32 {
        debug_assert!(!edges.is_empty());

        let mut idx = self.get_next(DEAD_STATE_IDX);
        while idx != DEAD_STATE_IDX {
            debug_assert!(!self.is_fixed(idx));
            let base = i32::try_from(idx).unwrap() - i32::try_from(edges[0].0).unwrap();
            if self.verify_base(base, edges) {
                return base;
            }
            idx = self.get_next(idx);
        }
        i32::try_from(self.states.len()).unwrap() - i32::try_from(edges[0].0).unwrap()
    }

    #[inline(always)]
    fn verify_base(&self, base: i32, edges: &[(u32, u32)]) -> bool {
        for &(c, _) in edges {
            let idx = base + i32::try_from(c).unwrap();
            let idx = u32::try_from(idx).unwrap();
            if self.states.len() <= idx as usize {
                return true;
            }
            if self.is_fixed(idx) {
                return false;
            }
        }
        true
    }

    #[inline(always)]
    fn extend_array(&mut self, max_idx: u32) {
        while self.states.len() <= max_idx as usize {
            self.push_state();
        }
    }

    #[inline(always)]
    fn push_state(&mut self) {
        let head_idx = DEAD_STATE_IDX;
        let tail_idx = self.get_prev(head_idx);

        let new_idx = u32::try_from(self.states.len()).unwrap();
        self.states.push(State::default());

        self.set_next(new_idx, head_idx);
        self.set_prev(head_idx, new_idx);
        self.set_prev(new_idx, tail_idx);
        self.set_next(tail_idx, new_idx);
    }

    #[inline(always)]
    fn get_next(&self, i: u32) -> u32 {
        self.states[i as usize].fail()
    }

    #[inline(always)]
    fn get_prev(&self, i: u32) -> u32 {
        self.states[i as usize].output_pos().unwrap().get()
    }

    #[inline(always)]
    fn set_next(&mut self, i: u32, x: u32) {
        self.states[i as usize].set_fail(x);
    }

    #[inline(always)]
    fn set_prev(&mut self, i: u32, x: u32) {
        self.states[i as usize].set_output_pos(NonZeroU32::new(x));
    }

    #[inline(always)]
    fn is_fixed(&self, i: u32) -> bool {
        i == DEAD_STATE_IDX || self.states[i as usize].output_pos().is_none()
    }

    #[inline(always)]
    fn set_fixed(&mut self, i: u32) {
        debug_assert_ne!(i, DEAD_STATE_IDX);
        self.states[i as usize].set_fail(DEAD_STATE_IDX);
        self.states[i as usize].set_output_pos(None);
    }
}
