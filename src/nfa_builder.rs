use core::cell::Cell;
use core::num::NonZeroU32;

use alloc::vec::Vec;

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
}
