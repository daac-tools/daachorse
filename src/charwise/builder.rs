use core::num::NonZeroU32;

use alloc::vec::Vec;

use crate::charwise::{CharwiseDoubleArrayAhoCorasick, CodeMapper, MatchKind, State};
use crate::errors::{DaachorseError, Result};
use crate::nfa_builder::NfaBuilder;
use crate::BuildHelper;

use crate::charwise::{DEAD_STATE_IDX, ROOT_STATE_IDX};
use crate::nfa_builder::{DEAD_STATE_ID, ROOT_STATE_ID};

// Specialized [`NfaBuilder`] handling labels of `char`.
type CharwiseNfaBuilder = NfaBuilder<char>;

/// Builder for [`CharwiseDoubleArrayAhoCorasick`].
pub struct CharwiseDoubleArrayAhoCorasickBuilder {
    states: Vec<State>,
    mapper: CodeMapper,
    match_kind: MatchKind,
    block_len: u32,
    num_free_blocks: u32,
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
    #[must_use]
    pub fn new() -> Self {
        Self {
            states: vec![],
            mapper: CodeMapper::default(),
            match_kind: MatchKind::Standard,
            block_len: 0,
            num_free_blocks: 16,
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

    /// Specifies the number of last blocks to search bases.
    ///
    /// The smaller the number is, the faster the construction time will be;
    /// however, the memory efficiency can be degraded.
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
        // The following code implicitly replaces large indices with 0,
        // but build_with_values() returns an error variant for such iterators.
        let patvals = patterns
            .into_iter()
            .enumerate()
            .map(|(i, p)| (p, i.try_into().unwrap_or(0)));
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
        nfa.build_outputs(&q);
        Ok(nfa)
    }

    fn build_double_array(&mut self, nfa: &CharwiseNfaBuilder) -> Result<()> {
        let mut helper = self.init_array()?;

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

            let base = self.find_base(&mapped, &helper);
            if self.states.len() <= base.get() as usize {
                self.extend_array(&mut helper)?;
            }

            for &(c, child_id) in &mapped {
                let child_idx = base.get() ^ c;
                helper.use_index(child_idx);
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

    fn init_array(&mut self) -> Result<BuildHelper> {
        self.block_len = self.mapper.alphabet_size().next_power_of_two().max(2);
        self.states
            .resize(usize::try_from(self.block_len).unwrap(), State::default());
        let mut helper = BuildHelper::new(self.block_len, self.num_free_blocks)?;
        helper.push_block().unwrap();
        helper.use_index(ROOT_STATE_IDX);
        helper.use_index(DEAD_STATE_IDX);
        Ok(helper)
    }

    #[inline(always)]
    fn find_base(&self, edges: &[(u32, u32)], helper: &BuildHelper) -> NonZeroU32 {
        debug_assert!(!edges.is_empty());

        for idx in helper.vacant_iter() {
            let base = idx ^ edges[0].0;
            if self.verify_base(base, edges, helper) {
                if let Some(base) = NonZeroU32::new(base) {
                    return base;
                }
            }
        }
        // len() is not 0 since states has at least block_len items.
        // The following value is always larger than or equal to len() since block_len is
        // alphabet_size().next_power_of_two().
        NonZeroU32::new(u32::try_from(self.states.len()).unwrap() ^ edges[0].0).unwrap()
    }

    #[inline(always)]
    fn verify_base(&self, base: u32, edges: &[(u32, u32)], helper: &BuildHelper) -> bool {
        for &(c, _) in edges {
            let idx = base ^ c;
            if helper.is_used_index(idx) {
                return false;
            }
        }
        true
    }

    #[inline(always)]
    fn extend_array(&mut self, helper: &mut BuildHelper) -> Result<()> {
        if self.states.len() > usize::try_from(u32::MAX - self.block_len).unwrap() {
            return Err(DaachorseError::automaton_scale("states.len()", u32::MAX));
        }

        helper.push_block()?;
        self.states.resize(
            self.states.len() + usize::try_from(self.block_len).unwrap(),
            State::default(),
        );

        Ok(())
    }
}
