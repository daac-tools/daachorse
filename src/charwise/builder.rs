use alloc::string::{String, ToString};
use alloc::vec::Vec;

use crate::build_helper::{BuildHelper, Profile};
use crate::charwise::{CharwiseDoubleArrayAhoCorasick, CodeMapper, MatchKind, State};
use crate::errors::{DaachorseError, Result};
use crate::nfa_builder::NfaBuilder;
use crate::nfa_builder::DEAD_STATE_ID;
use crate::prefilter::{Prefilter, PrefilterBuilder};
use crate::utils::FromU32;
use crate::DEAD_STATE_IDX;

// Specialized [`NfaBuilder`] handling labels of `char`.
type CharwiseNfaBuilder<V> = NfaBuilder<char, V>;

/// Builder for [`CharwiseDoubleArrayAhoCorasick`].
pub struct CharwiseDoubleArrayAhoCorasickBuilder {
    states: Vec<State>,
    mapper: CodeMapper,
    match_kind: MatchKind,
    corpus: Vec<String>,
    use_prefilter: bool,
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
    /// use daachorse::CharwiseDoubleArrayAhoCorasickBuilder;
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
            corpus: vec![],
            use_prefilter: true,
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

    /// Specifies whether to build the match-candidate prefilter, which is enabled by default.
    ///
    /// The prefilter accelerates the slice-based search methods on pattern sets where it is
    /// likely to pay off, in exchange for 64KiB of additional heap memory and serialized size.
    /// Disable it when the memory matters more than the search speed.
    ///
    /// # Arguments
    ///
    /// * `yes` - Whether to build the prefilter.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasickBuilder;
    ///
    /// let patterns = vec!["全世界", "世界"];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
    ///     .use_prefilter(false)
    ///     .build(patterns)
    ///     .unwrap();
    ///
    /// let mut it = pma.find_overlapping_iter("全世界");
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((0, 9, 0), (m.start(), m.end(), m.value()));
    ///
    /// let m = it.next().unwrap();
    /// assert_eq!((3, 9, 1), (m.start(), m.end(), m.value()));
    ///
    /// assert_eq!(None, it.next());
    /// ```
    #[must_use]
    pub const fn use_prefilter(mut self, yes: bool) -> Self {
        self.use_prefilter = yes;
        self
    }

    /// Specifies a corpus of sample documents for the profile-guided layout optimization.
    ///
    /// States frequently accessed in scanning the corpus are packed densely at small indices
    /// so that matching on documents similar to the corpus becomes more cache-efficient.
    /// The corpus never changes match results, only the memory layout of the automaton.
    ///
    /// Since the states accessed in scanning the corpus are placed by scanning all the blocks
    /// of the double array, the construction time can increase, especially when the corpus
    /// covers most states of a large pattern set.
    ///
    /// # Arguments
    ///
    /// * `haystacks` - Sample documents to be scanned.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasickBuilder;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
    ///     .corpus(["全世界中に"])
    ///     .build(patterns)
    ///     .unwrap();
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
    pub fn corpus<I, P>(mut self, haystacks: I) -> Self
    where
        I: IntoIterator<Item = P>,
        P: AsRef<str>,
    {
        self.corpus = haystacks
            .into_iter()
            .map(|h| h.as_ref().to_string())
            .collect();
        self
    }

    /// Builds and returns a new [`CharwiseDoubleArrayAhoCorasick`] from input patterns. The value
    /// `i` is automatically associated with `patterns[i]`.
    ///
    /// # Arguments
    ///
    /// * `patterns` - List of patterns.
    ///
    /// # Errors
    ///
    /// [`DaachorseError`] is returned when
    ///   - the conversion from the index `i` to the specified type `V` fails,
    ///   - the scale of `patterns` exceeds the expected one, or
    ///   - the scale of the resulting automaton exceeds the expected one.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasickBuilder;
    ///
    /// let patterns = vec!["全世界", "世界", "に"];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
    ///     .build(patterns)
    ///     .unwrap();
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
    pub fn build<I, P, V>(self, patterns: I) -> Result<CharwiseDoubleArrayAhoCorasick<V>>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<str>,
        V: Copy + TryFrom<usize>,
    {
        // The following code implicitly replaces large indices with 0,
        // but build_with_values() returns an error variant for such iterators.
        let patvals: Vec<_> = patterns
            .into_iter()
            .enumerate()
            .map(|(i, p)| V::try_from(i).map(|i| (p, i)))
            .collect::<Result<_, _>>()
            .map_err(|_| DaachorseError::invalid_conversion("index", "V"))?;
        self.build_with_values(patvals)
    }

    /// Builds and returns a new [`CharwiseDoubleArrayAhoCorasick`] from input pattern-value pairs.
    ///
    /// # Arguments
    ///
    /// * `patvals` - List of pattern-value pairs.
    ///
    /// # Errors
    ///
    /// [`DaachorseError`] is returned when
    ///   - the scale of `patvals` exceeds the expected one, or
    ///   - the scale of the resulting automaton exceeds the expected one.
    ///
    /// # Examples
    ///
    /// ```
    /// use daachorse::CharwiseDoubleArrayAhoCorasickBuilder;
    ///
    /// let patvals = vec![("全世界", 0), ("世界", 10), ("に", 100)];
    /// let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
    ///     .build_with_values(patvals)
    ///     .unwrap();
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
    pub fn build_with_values<I, P, V>(
        mut self,
        patvals: I,
    ) -> Result<CharwiseDoubleArrayAhoCorasick<V>>
    where
        I: IntoIterator<Item = (P, V)>,
        P: AsRef<str>,
        V: Copy,
    {
        let (nfa, prefilter) = self.build_original_nfa_and_mapper(patvals)?;

        let profile = if self.corpus.is_empty() {
            Profile::default()
        } else {
            self.profile_corpus(&nfa)
        };
        self.build_double_array(&nfa, &profile)?;

        // -1 is for dead state
        let num_states = u32::try_from(nfa.states.len() - 1)
            .map_err(|_| DaachorseError::automaton_scale("num_states", u32::MAX))?;

        Ok(CharwiseDoubleArrayAhoCorasick {
            states: self.states,
            mapper: self.mapper,
            outputs: nfa.outputs,
            match_kind: self.match_kind,
            num_states,
            prefilter,
        })
    }

    fn build_original_nfa_and_mapper<I, P, V>(
        &mut self,
        patvals: I,
    ) -> Result<(CharwiseNfaBuilder<V>, Option<Prefilter>)>
    where
        I: IntoIterator<Item = (P, V)>,
        P: AsRef<str>,
        V: Copy,
    {
        let mut nfa = CharwiseNfaBuilder::new(self.match_kind);
        let mut prefilter_builder = self.use_prefilter.then(PrefilterBuilder::new);
        let mut freqs = vec![];
        {
            let mut chars = vec![];
            for (pattern, value) in patvals {
                if let Some(builder) = &mut prefilter_builder {
                    builder.add(pattern.as_ref().as_bytes());
                }
                chars.clear();
                pattern.as_ref().chars().for_each(|c| chars.push(c));
                nfa.add(&chars, value)?;

                for &c in &chars {
                    let c = usize::from_u32(u32::from(c));
                    if freqs.len() <= c {
                        freqs.resize(c + 1, 0);
                    }
                    freqs[c] += 1;
                }
            }
        }
        self.mapper = CodeMapper::new(&freqs);

        let q = match self.match_kind {
            MatchKind::Standard => nfa.build_fails(),
            MatchKind::LeftmostLongest | MatchKind::LeftmostFirst => nfa.build_fails_leftmost(),
        };
        nfa.build_outputs(&q);
        Ok((nfa, prefilter_builder.and_then(PrefilterBuilder::build)))
    }

    fn profile_corpus<V>(&self, nfa: &CharwiseNfaBuilder<V>) -> Profile
    where
        V: Copy,
    {
        let mut profile = Profile::default();
        profile.resize(nfa.states.len());
        let mut chars = vec![];
        for haystack in &self.corpus {
            chars.clear();
            chars.extend(haystack.chars());
            // The character-wise version has no dense root table, and characters not in the
            // mapper reset the state to the root without accessing the double array.
            nfa.profile_haystack(&chars, &mut profile, false, |c| {
                self.mapper.get(c).is_some()
            });
        }
        profile
    }

    fn build_double_array<V>(
        &mut self,
        nfa: &CharwiseNfaBuilder<V>,
        profile: &Profile,
    ) -> Result<()>
    where
        V: Copy,
    {
        let block_len = self.mapper.block_len();
        let groups = nfa.sibling_groups(profile, |c| self.mapper.get(c).unwrap());
        let helper = BuildHelper::new(&groups, nfa.states.len(), block_len, false)?;

        self.states
            .resize(usize::from_u32(helper.num_elements()), State::default());
        for group in &groups {
            let parent_idx = helper.idx_map[usize::from_u32(group.parent)];
            for &(_, child_id) in &group.children {
                self.states[usize::from_u32(helper.idx_map[usize::from_u32(child_id)])]
                    .set_check(parent_idx);
            }
            // BuildHelper::new() assigns a BASE value to every group.
            self.states[usize::from_u32(parent_idx)]
                .set_base(helper.bases[usize::from_u32(group.parent)].unwrap());
        }

        self.set_fails_and_outputs(nfa, &helper.idx_map);

        Ok(())
    }

    fn set_fails_and_outputs<V>(&mut self, nfa: &CharwiseNfaBuilder<V>, state_id_map: &[u32]) {
        for (i, s) in nfa.states.iter().enumerate() {
            if i == usize::from_u32(DEAD_STATE_ID) {
                continue;
            }

            let idx = usize::from_u32(state_id_map[i]);
            debug_assert_ne!(idx, usize::from_u32(DEAD_STATE_IDX));

            self.states[idx].set_output_pos(s.output_pos.get());

            let fail_id = s.fail.get();
            if fail_id == DEAD_STATE_ID {
                self.states[idx].set_fail(DEAD_STATE_IDX);
            } else {
                let fail_idx = state_id_map[usize::from_u32(fail_id)];
                debug_assert_ne!(fail_idx, DEAD_STATE_IDX);
                self.states[idx].set_fail(fail_idx);
            }
        }
    }
}
