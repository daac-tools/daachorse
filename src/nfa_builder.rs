use core::cell::Cell;
use core::cmp::Reverse;
use core::num::NonZeroU32;

use alloc::vec::Vec;

use crate::build_helper::{Profile, SiblingGroup};
use crate::edge_map::EdgeMap;
use crate::errors::{DaachorseError, Result};
use crate::utils::FromU32;
use crate::{MatchKind, Output};

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
    pub(crate) fail: Cell<u32>,
    pub(crate) output: Vec<(V, u32)>,
    pub(crate) output_pos: Cell<Option<NonZeroU32>>,
}

impl<L, V> Default for NfaBuilderState<L, V> {
    fn default() -> Self {
        Self {
            edges: EdgeMap::<L>::default(),
            fail: Cell::new(ROOT_STATE_ID),
            output: vec![],
            output_pos: Cell::new(None),
        }
    }
}

/// Builder of an Aho-Corasick automaton.
pub struct NfaBuilder<L, V> {
    pub(crate) states: Vec<NfaBuilderState<L, V>>,
    pub(crate) outputs: Vec<Output<V>>, // in which common parts are merged.
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
        while let Some(state_id) = stack.pop() {
            let s = &self.states[usize::from_u32(state_id)];
            if s.edges.is_empty() {
                continue;
            }
            let mut children = Vec::with_capacity(1);
            let mut weight = profile.probes[usize::from_u32(state_id)];
            for &(c, child_id) in s.edges.iter() {
                weight += profile.visits[usize::from_u32(child_id)];
                children.push((map_label(c), child_id));
                stack.push(child_id);
            }
            groups.push(SiblingGroup {
                parent: state_id,
                children,
                weight,
            });
        }
        // The sort must be stable so that groups with equal weights (in particular, all the
        // groups when no corpus is given) keep the depth-first order and are placed in the
        // same order as the classic depth-first construction.
        groups.sort_by_key(|g| Reverse(g.weight));
        groups
    }
}
