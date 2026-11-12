use core::cell::Cell;
use core::cmp::Reverse;
use core::num::NonZeroU32;

use alloc::vec::Vec;

use crate::build_helper::{Profile, SiblingGroup};
use crate::edge_map::EdgeMap;
use crate::errors::{DaachorseError, Result};
use crate::utils::FromU32;
use crate::{Emit, MatchKind, Output};

// The root state id of SparseNFA.
pub const ROOT_STATE_ID: u32 = 0;
// The dead state id of SparseNFA.
pub const DEAD_STATE_ID: u32 = 1;

pub trait EdgeLabel: Copy + Ord + core::fmt::Debug {
    fn num_bytes(&self) -> usize;
}

impl EdgeLabel for u8 {
    fn num_bytes(&self) -> usize {
        1
    }
}

impl EdgeLabel for char {
    fn num_bytes(&self) -> usize {
        self.len_utf8()
    }
}

/// State of [`NfaBuilder`].
#[derive(Clone)]
pub struct NfaBuilderState<L, V> {
    pub(crate) edges: EdgeMap<L>,
    // Failure state index.
    pub(crate) fail: Cell<u32>,
    // In experimental leftmost matching, flags if this state or any state along its failure chain has an emit.
    pub(crate) fail_has_emit: Cell<bool>,
    pub(crate) output: Vec<(V, u32)>,
    // 1-based index into `outputs` (standard/legacy) or `emits` (experimental).
    pub(crate) output_pos: Cell<Option<NonZeroU32>>,
}

impl<L, V> Default for NfaBuilderState<L, V> {
    fn default() -> Self {
        Self {
            edges: EdgeMap::<L>::default(),
            fail: Cell::new(ROOT_STATE_ID),
            fail_has_emit: Cell::new(false),
            output: vec![],
            output_pos: Cell::new(None),
        }
    }
}

/// Builder of an Aho-Corasick automaton.
pub struct NfaBuilder<L, V> {
    pub(crate) states: Vec<NfaBuilderState<L, V>>,
    pub(crate) outputs: Vec<Output<V>>, // in which common parts are merged.
    pub(crate) emits: Vec<Emit<V>>, // Committed match chains for experimental leftmost matching.
    pub(crate) len: usize,
    pub(crate) match_kind: MatchKind,
}

impl<L, V> NfaBuilder<L, V>
where
    L: EdgeLabel,
    V: Copy,
{
    pub(crate) fn new(match_kind: MatchKind) -> Self {
        Self {
            states: vec![
                NfaBuilderState::<L, V>::default(), // root
                NfaBuilderState::<L, V>::default(), // dead
            ],
            outputs: vec![],
            emits: vec![],
            len: 0,
            match_kind,
        }
    }

    #[inline(always)]
    pub(crate) fn add(&mut self, pattern: &[L], value: V) -> Result<()> {
        let pattern_len = pattern
            .iter()
            .fold(0, |acc, c| acc + c.num_bytes())
            .try_into()
            .map_err(|_| DaachorseError::invalid_argument("pattern.len()", "<=", u32::MAX))?;

        let mut state_id = ROOT_STATE_ID;
        for &c in pattern {
            if self.match_kind.is_leftmost_first() {
                // If state_id has an output, the descendants will never be searched.
                if !self.states[usize::from_u32(state_id)].output.is_empty() {
                    return Ok(());
                }
            }

            if let Some(next_state_id) = self.child_id(state_id, c) {
                state_id = next_state_id;
            } else if let Ok(next_state_id) = u32::try_from(self.states.len()) {
                self.states[usize::from_u32(state_id)]
                    .edges
                    .insert(c, next_state_id);
                self.states.push(NfaBuilderState::<L, V>::default());
                state_id = next_state_id;
            } else {
                return Err(DaachorseError::automaton_scale("state_id", u32::MAX));
            }
        }

        self.states[usize::from_u32(state_id)]
            .output
            .push((value, pattern_len));

        self.len += 1;
        Ok(())
    }

    pub(crate) fn build_fails(&self) -> Vec<u32> {
        let mut q = Vec::with_capacity(self.states.len());
        for &child_id in self.states[usize::from_u32(ROOT_STATE_ID)].edges.values() {
            q.push(child_id);
        }

        let mut qi = 0;
        while qi < q.len() {
            let state_id = usize::from_u32(q[qi]);
            qi += 1;

            let s = &self.states[state_id];
            for &(c, child_id) in s.edges.iter() {
                let mut fail_id = s.fail.get();
                let new_fail_id = loop {
                    if let Some(child_fail_id) = self.child_id(fail_id, c) {
                        break child_fail_id;
                    }
                    let next_fail_id = self.states[usize::from_u32(fail_id)].fail.get();
                    if fail_id == ROOT_STATE_ID && next_fail_id == ROOT_STATE_ID {
                        break ROOT_STATE_ID;
                    }
                    fail_id = next_fail_id;
                };
                self.states[usize::from_u32(child_id)].fail.set(new_fail_id);
                q.push(child_id);
            }
        }
        q
    }

    pub(crate) fn build_fails_leftmost(&self) -> Vec<u32> {
        let mut q = Vec::with_capacity(self.states.len());
        for &child_id in self.states[usize::from_u32(ROOT_STATE_ID)].edges.values() {
            q.push(child_id);
        }
        if !self.states[usize::from_u32(ROOT_STATE_ID)]
            .output
            .is_empty()
        {
            for &child_id in self.states[usize::from_u32(ROOT_STATE_ID)].edges.values() {
                self.states[usize::from_u32(child_id)]
                    .fail
                    .set(DEAD_STATE_ID);
            }
        }

        let mut qi = 0;
        while qi < q.len() {
            let state_id = usize::from_u32(q[qi]);
            qi += 1;

            let s = &self.states[state_id];

            // Sets the output state to the dead fail.
            if !s.output.is_empty() {
                s.fail.set(DEAD_STATE_ID);
            }

            for &(c, child_id) in s.edges.iter() {
                let mut fail_id = s.fail.get();

                // If the parent has the dead fail, the child also has the dead fail.
                let new_fail_id = if fail_id == DEAD_STATE_ID {
                    DEAD_STATE_ID
                } else {
                    loop {
                        if let Some(child_fail_id) = self.child_id(fail_id, c) {
                            break child_fail_id;
                        }
                        let next_fail_id = self.states[usize::from_u32(fail_id)].fail.get();
                        if next_fail_id == DEAD_STATE_ID {
                            break DEAD_STATE_ID;
                        }
                        if fail_id == ROOT_STATE_ID && next_fail_id == ROOT_STATE_ID {
                            break ROOT_STATE_ID;
                        }
                        fail_id = next_fail_id;
                    }
                };

                self.states[usize::from_u32(child_id)].fail.set(new_fail_id);
                q.push(child_id);
            }
        }
        q
    }
}

impl<L, V> NfaBuilder<L, V>
where
    L: EdgeLabel,
    V: Copy,
{
    /// Builds failure transitions and match emit chains for experimental leftmost matching.
    ///
    /// Precalculates `fail` (the pending suffix) and `emit` (committed matches) in BFS order.
    /// When an upcoming character causes a mismatch, the engine emits the committed matches
    /// and transitions directly to the pending suffix.
    pub(crate) fn build_fails_and_emits_leftmost_experimental(&mut self) {
        let num_states = self.states.len();
        let mut q = Vec::with_capacity(num_states);
        let mut parents = vec![ROOT_STATE_ID; num_states];
        let mut edge_labels: Vec<Option<L>> = vec![None; num_states];

        // Stage 1: BFS Traversal to Establish Topological Order and Parent Links.
        //
        // This traversal computes:
        // 1. `q`: Topological BFS ordering ensuring ancestor states are processed before descendants.
        // 2. `parents` and `edge_labels`: Structural links for parent lookup and DP transitions.
        //
        // Initialize BFS queue starting with ROOT_STATE_ID:
        q.push(ROOT_STATE_ID);
        let mut qi = 0;
        while qi < q.len() {
            let state_id = q[qi];
            qi += 1;

            for &(ch, child_id) in self.states[usize::from_u32(state_id)].edges.iter() {
                parents[usize::from_u32(child_id)] = state_id;
                edge_labels[usize::from_u32(child_id)] = Some(ch);
                q.push(child_id);
            }
        }

        // Construction-time store for deduplicating and indexing emit nodes.
        let mut store = EmitStore::with_capacity(q.len());

        // If ROOT has an output (empty pattern ""), register its emit node.
        if let Some(&output) = self.states[usize::from_u32(ROOT_STATE_ID)].output.first() {
            let emit = Emit::from_output(output, 0, None);
            let key = DedupKey {
                output_state_id: ROOT_STATE_ID,
                gap: 0,
                pred: None,
            };
            self.states[usize::from_u32(ROOT_STATE_ID)]
                .output_pos
                .set(Some(store.insert(emit, key)));
        }

        // Reusable scratch buffer for harvesting matches during failure fallback walks.
        let mut scratch_buffer = Vec::new();

        // Stage 2: Resolving pending suffix fail transitions and committed match chains.
        for &state_id in &q[1..] {
            // If `state_id` itself is a complete pattern from root, under leftmost-longest priority
            // it supersedes any suffix fallback.
            if let Some(&output) = self.states[usize::from_u32(state_id)].output.first() {
                let emit = Emit::from_output(output, 0, None);
                let key = DedupKey {
                    output_state_id: state_id,
                    gap: 0,
                    pred: None,
                };
                self.states[usize::from_u32(state_id)]
                    .output_pos
                    .set(Some(store.insert(emit, key)));
                self.states[usize::from_u32(state_id)]
                    .fail
                    .set(ROOT_STATE_ID);
                continue;
            }

            // Inherit the parent's in-flight head match and advance its trailing gap by |c| bytes.
            let parent_id = parents[usize::from_u32(state_id)];
            let ch = edge_labels[usize::from_u32(state_id)].unwrap();
            // Direct children of ROOT start with an empty match chain (initial_head = None).
            // Even if ROOT holds an output for the empty pattern (""), child transitions
            // pursue non-empty extensions whose prefix does not commit the empty pattern.
            let initial_head = if parent_id == ROOT_STATE_ID {
                None
            } else {
                self.states[usize::from_u32(parent_id)]
                    .output_pos
                    .get()
                    .map(|pos| {
                        (
                            store.get(pos).with_incremented_gap(ch.num_bytes()),
                            store.key_of(pos).output_state_id,
                        )
                    })
            };

            let mut chain = EmitChain::new(initial_head);

            // 1. Walk the failure chain: when suffix candidate curr cannot transition on ch,
            // append its committed matches onto chain.
            let mut curr = self.states[usize::from_u32(parent_id)].fail.get();
            let mut next_child = self.child_id(curr, ch);
            while curr != ROOT_STATE_ID && next_child.is_none() {
                if let Some(curr_head) = self.states[usize::from_u32(curr)].output_pos.get() {
                    scratch_buffer.clear();
                    scratch_buffer.extend(store.iter_chain(curr_head));
                    // Matches along curr's prefix ended at the parent; advance the head gap by |c| to align with state_id:
                    scratch_buffer[0].0 = scratch_buffer[0].0.with_incremented_gap(ch.num_bytes());
                    scratch_buffer[0].1.gap += u32::try_from(ch.num_bytes()).unwrap();
                    chain.extend_from(&scratch_buffer, &mut store);
                }
                curr = self.states[usize::from_u32(curr)].fail.get();
                next_child = self.child_id(curr, ch);
            }

            // 2. Pending suffix transition and leaf match handling:
            let mut fail_state = ROOT_STATE_ID;
            if parent_id != ROOT_STATE_ID {
                if let Some(child_id) = next_child {
                    if !self.states[usize::from_u32(child_id)].edges.is_empty() {
                        fail_state = child_id;
                    } else {
                        // Suffix completes a leaf pattern at the very end of `state_id`.
                        let leaf_output = self.states[usize::from_u32(child_id)].output[0];
                        chain.push_leaf(leaf_output, child_id, &mut store);
                        fail_state = ROOT_STATE_ID;
                    }
                }
            }

            // 3. Finalize match chain:
            let final_pos = chain.finish(&mut store);
            self.states[usize::from_u32(state_id)]
                .output_pos
                .set(final_pos);
            self.states[usize::from_u32(state_id)].fail.set(fail_state);
        }

        // Stage 3: Flag whether each state or any state along its failure chain has an emit.
        //
        // ROOT is intentionally excluded: the empty pattern ("") is handled specially via cursor
        // interpolation in the iterator, whereas failure chain draining stops at ROOT. Setting bit 31
        // on ROOT would cause all states to set this flag whenever an empty pattern is present.
        for &state_id in &q[1..] {
            let state = &self.states[usize::from_u32(state_id)];
            let fail_id = state.fail.get();
            let fail_has_emit = self.states[usize::from_u32(fail_id)].fail_has_emit.get();
            if state.output_pos.get().is_some() || fail_has_emit {
                state.fail_has_emit.set(true);
            }
        }

        self.emits = store.into_emits();
    }
}

impl<L, V> NfaBuilder<L, V>
where
    L: EdgeLabel,
    V: Copy,
{
    pub(crate) fn build_outputs(&mut self, q: &[u32]) {
        {
            let s = &self.states[usize::from_u32(ROOT_STATE_ID)];
            let mut last_pos = None;
            for output in s.output.iter().rev() {
                self.outputs.push(Output::new(output.0, output.1, last_pos));
                last_pos = NonZeroU32::new(u32::try_from(self.outputs.len()).unwrap());
            }
            s.output_pos.set(last_pos);
        }
        for &state_id in q {
            let s = &self.states[usize::from_u32(state_id)];
            let mut last_pos = self.states[usize::from_u32(s.fail.get())].output_pos.get();
            for output in s.output.iter().rev() {
                self.outputs.push(Output::new(output.0, output.1, last_pos));
                last_pos = NonZeroU32::new(u32::try_from(self.outputs.len()).unwrap());
            }
            s.output_pos.set(last_pos);
        }
    }

    #[inline(always)]
    fn child_id(&self, state_id: u32, c: L) -> Option<u32> {
        self.states[usize::from_u32(state_id)]
            .edges
            .get(&c)
            .copied()
    }

    fn profile_step(
        &self,
        mut state_id: u32,
        c: L,
        profile: &mut Profile,
        dense_root: bool,
    ) -> u32 {
        loop {
            // The runtime handles such root transitions with a dense table without accessing
            // the double array, so no access is counted.
            if dense_root && state_id == ROOT_STATE_ID {
                return self.child_id(ROOT_STATE_ID, c).unwrap_or(ROOT_STATE_ID);
            }
            let s = &self.states[usize::from_u32(state_id)];
            // The runtime reads the double-array element of the current state.
            profile.visits[usize::from_u32(state_id)] += 1;
            if !s.edges.is_empty() {
                if let Some(&child_id) = s.edges.get(&c) {
                    // A successful probe reads the element of the child.
                    profile.visits[usize::from_u32(child_id)] += 1;
                    return child_id;
                }
                // A failed probe reads an element in the block where the children of this
                // state are placed.
                profile.probes[usize::from_u32(state_id)] += 1;
            }
            if state_id == ROOT_STATE_ID {
                return ROOT_STATE_ID;
            }
            let fail_id = s.fail.get();
            if fail_id == DEAD_STATE_ID {
                return ROOT_STATE_ID;
            }
            state_id = fail_id;
        }
    }

    pub(crate) fn profile_haystack<F>(
        &self,
        haystack: &[L],
        profile: &mut Profile,
        dense_root: bool,
        mut has_label: F,
    ) where
        F: FnMut(L) -> bool,
    {
        let leftmost = self.match_kind.is_leftmost();
        let mut state_id = ROOT_STATE_ID;
        let mut match_end = None;
        let mut pos = 0;
        while pos < haystack.len() {
            let c = haystack[pos];
            state_id = if has_label(c) {
                self.profile_step(state_id, c, profile, dense_root)
            } else {
                ROOT_STATE_ID
            };
            if leftmost {
                if state_id == ROOT_STATE_ID {
                    // The leftmost iterators yield the pending match here and restart
                    // scanning at its end position in the next call.
                    if let Some(end) = match_end.take() {
                        pos = end;
                        continue;
                    }
                } else if self.states[usize::from_u32(state_id)]
                    .output_pos
                    .get()
                    .is_some()
                {
                    match_end = Some(pos + 1);
                }
            }
            pos += 1;
        }
    }

    pub(crate) fn sibling_groups<M>(&self, profile: &Profile, mut map_label: M) -> Vec<SiblingGroup>
    where
        M: FnMut(L) -> u32,
    {
        let mut groups = vec![];
        let mut stack = vec![ROOT_STATE_ID];
        let profiled = !profile.is_empty();
        while let Some(state_id) = stack.pop() {
            let s = &self.states[usize::from_u32(state_id)];
            if s.edges.is_empty() {
                continue;
            }
            let mut children = Vec::with_capacity(s.edges.len());
            let mut weight = if profiled {
                profile.probes[usize::from_u32(state_id)]
            } else {
                0
            };
            for &(c, child_id) in s.edges.iter() {
                if profiled {
                    weight += profile.visits[usize::from_u32(child_id)];
                }
                children.push((map_label(c), child_id));
                stack.push(child_id);
            }
            groups.push(SiblingGroup {
                parent: state_id,
                children,
                weight,
            });
        }
        // With no profile, the sort is skipped and the groups keep the depth-first order, in
        // which they are placed in the same order as the classic depth-first construction.
        // The sort must be stable so that groups with equal weights also keep that order.
        if profiled {
            groups.sort_by_key(|g| Reverse(g.weight));
        }
        groups
    }
}

/// Helper for accumulating match emit chains during experimental leftmost construction.
///
/// Tracks an in-flight head match whose trailing gap is maintained relative to the
/// current state's byte boundary. Inter-match gaps and predecessor links are delta-encoded
/// so common predecessor chains are structurally shared across trie branches.
#[derive(Clone, Copy, Debug)]
struct EmitChain<V> {
    head: Option<(Emit<V>, u32)>,
}

impl<V> Default for EmitChain<V> {
    #[inline(always)]
    fn default() -> Self {
        Self { head: None }
    }
}

impl<V: Copy> EmitChain<V> {
    /// Initializes a match chain with an optional in-flight head match.
    #[inline(always)]
    const fn new(head: Option<(Emit<V>, u32)>) -> Self {
        Self { head }
    }

    /// Appends all matches from a candidate match chain into this chain.
    ///
    /// `emits` contains the matches in reverse chronological order `[M_k, ..., M_1]`,
    /// with `emits[0].gap` already adjusted relative to the current state.
    #[inline(always)]
    fn extend_from(&mut self, emits: &[(Emit<V>, DedupKey)], store: &mut EmitStore<V>) {
        if emits.is_empty() {
            return;
        }

        // Link earliest incoming match to the previous head:
        let mut pred = if let Some((prev, prev_state)) = self.head {
            let span: u32 = emits.iter().map(|(em, _)| em.gap + em.length).sum();
            debug_assert!(
                prev.gap >= span,
                "candidate match cannot overlap with committed match"
            );
            let inter_gap = prev.gap - span;
            Some(store.insert(
                prev.with_gap(inter_gap),
                DedupKey {
                    output_state_id: prev_state,
                    gap: inter_gap,
                    pred: prev.pred,
                },
            ))
        } else {
            None
        };

        // Chain intermediate matches:
        for (em, key) in emits[1..].iter().rev() {
            pred = Some(store.insert(
                Emit::new(em.value, em.length, em.gap, pred),
                DedupKey {
                    output_state_id: key.output_state_id,
                    gap: em.gap,
                    pred,
                },
            ));
        }

        // Install the latest match as the new in-flight head:
        self.head = Some((emits[0].0.with_pred(pred), emits[0].1.output_state_id));
    }

    /// Appends a newly completed leaf pattern ending at the current state.
    #[inline(always)]
    fn push_leaf(&mut self, output: (V, u32), output_state_id: u32, store: &mut EmitStore<V>) {
        let pred = if let Some((prev, prev_state)) = self.head {
            debug_assert!(
                prev.gap >= output.1,
                "leaf pattern cannot overlap with committed match"
            );
            let inter_gap = prev.gap - output.1;
            Some(store.insert(
                prev.with_gap(inter_gap),
                DedupKey {
                    output_state_id: prev_state,
                    gap: inter_gap,
                    pred: prev.pred,
                },
            ))
        } else {
            None
        };
        self.head = Some((Emit::from_output(output, 0, pred), output_state_id));
    }

    /// Finalizes the match chain by committing the in-flight head to `store`.
    #[inline(always)]
    fn finish(self, store: &mut EmitStore<V>) -> Option<NonZeroU32> {
        self.head.map(|(h, output_state_id)| {
            store.insert(
                h,
                DedupKey {
                    output_state_id,
                    gap: h.gap,
                    pred: h.pred,
                },
            )
        })
    }
}

/// Deduplication key for [`Emit`] nodes.
///
/// Identifies an emit node by its originating pattern state instead of its value,
/// so deduplication never touches `V` and the builder only requires `V: Copy`.
/// Each pattern corresponds to exactly one terminal trie state, hence
/// `output_state_id` determines `(value, length)` and the key is canonical.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
struct DedupKey {
    output_state_id: u32,
    gap: u32,
    pred: Option<NonZeroU32>,
}

/// Storage and deduplication cache for [`Emit`] nodes during construction.
///
/// Combines the emit node vector with an open-addressing deduplication table.
/// Once construction finishes, converts into the finalized `Vec<Emit<V>>`.
struct EmitStore<V> {
    emits: Vec<Emit<V>>,
    keys: Vec<DedupKey>,
    dedup: EmitDedup,
}

impl<V: Copy> EmitStore<V> {
    /// Creates an empty store with initial capacity.
    fn with_capacity(cap: usize) -> Self {
        Self {
            emits: Vec::with_capacity(cap),
            keys: Vec::with_capacity(cap),
            dedup: EmitDedup::with_capacity(cap),
        }
    }

    /// Retrieves an [`Emit`] node by its 1-based index.
    #[inline(always)]
    fn get(&self, pos: NonZeroU32) -> Emit<V> {
        self.emits[usize::from_u32(pos.get() - 1)]
    }

    /// Retrieves the [`DedupKey`] of the node at its 1-based index.
    #[inline(always)]
    fn key_of(&self, pos: NonZeroU32) -> DedupKey {
        self.keys[usize::from_u32(pos.get() - 1)]
    }

    /// Inserts an [`Emit`] node with deduplication, returning its canonical 1-based index.
    #[inline(always)]
    fn insert(&mut self, emit: Emit<V>, key: DedupKey) -> NonZeroU32 {
        if let Some(pos) = self.dedup.get(&key) {
            return pos;
        }
        self.emits.push(emit);
        self.keys.push(key);
        let pos = NonZeroU32::new(u32::try_from(self.emits.len()).unwrap()).unwrap();
        self.dedup.insert(key, pos);
        pos
    }

    /// Returns an iterator over matches along a chain from head to tail.
    #[inline(always)]
    const fn iter_chain(&self, head: NonZeroU32) -> ChainIter<'_, V> {
        ChainIter {
            store: self,
            pos: Some(head),
        }
    }

    /// Unwraps the store to extract the finalized [`Vec<Emit<V>>`].
    #[inline(always)]
    fn into_emits(self) -> Vec<Emit<V>> {
        self.emits
    }
}

/// An iterator traversing an [`Emit`] chain from head to tail,
/// yielding each node with its [`DedupKey`] for re-insertion.
struct ChainIter<'a, V> {
    store: &'a EmitStore<V>,
    pos: Option<NonZeroU32>,
}

impl<'a, V: Copy> Iterator for ChainIter<'a, V> {
    type Item = (Emit<V>, DedupKey);

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let pos = self.pos?;
        let em = self.store.get(pos);
        let key = self.store.key_of(pos);
        self.pos = em.pred;
        Some((em, key))
    }
}

/// An open-addressing hash table for deduplicating [`Emit`] nodes during construction.
///
/// Unifies identical `(output_state_id, gap, pred)` tuples into a single canonical index
/// so common predecessor chains are structurally shared across trie branches.
struct EmitDedup {
    entries: Vec<Option<(DedupKey, NonZeroU32)>>,
    mask: usize,
    count: usize,
}

impl EmitDedup {
    fn with_capacity(cap: usize) -> Self {
        let size = cap.next_power_of_two().max(1024);
        Self {
            entries: vec![None; size],
            mask: size - 1,
            count: 0,
        }
    }

    #[inline(always)]
    fn get(&self, key: &DedupKey) -> Option<NonZeroU32> {
        let h = hash_key(key);
        let mut idx = h & self.mask;
        loop {
            match self.entries[idx] {
                None => return None,
                Some((existing, pos)) => {
                    if existing == *key {
                        return Some(pos);
                    }
                }
            }
            idx = (idx + 1) & self.mask;
        }
    }

    fn insert(&mut self, key: DedupKey, pos: NonZeroU32) {
        if self.count * 2 >= self.entries.len() {
            self.grow();
        }
        let h = hash_key(&key);
        let mut idx = h & self.mask;
        loop {
            match self.entries[idx] {
                None => {
                    self.entries[idx] = Some((key, pos));
                    self.count += 1;
                    return;
                }
                Some((existing, _)) => {
                    if existing == key {
                        return;
                    }
                }
            }
            idx = (idx + 1) & self.mask;
        }
    }

    fn grow(&mut self) {
        let new_size = self.entries.len() * 2;
        let new_mask = new_size - 1;
        let mut new_entries = vec![None; new_size];
        for (key, pos) in self.entries.drain(..).flatten() {
            let h = hash_key(&key);
            let mut idx = h & new_mask;
            while new_entries[idx].is_some() {
                idx = (idx + 1) & new_mask;
            }
            new_entries[idx] = Some((key, pos));
        }
        self.entries = new_entries;
        self.mask = new_mask;
    }
}

#[inline(always)]
#[allow(clippy::as_conversions, clippy::cast_possible_truncation)]
fn hash_key(key: &DedupKey) -> usize {
    // FxHash-style mixer over plain u32 fields; no `V` involved.
    const SEED: u64 = 0x517c_c1b7_2722_0a95;
    let mut h: u64 = 0;
    h = (h.rotate_left(5) ^ u64::from(key.output_state_id)).wrapping_mul(SEED);
    h = (h.rotate_left(5) ^ u64::from(key.gap)).wrapping_mul(SEED);
    h = (h.rotate_left(5) ^ u64::from(key.pred.map_or(0, NonZeroU32::get))).wrapping_mul(SEED);
    h as usize
}
