use core::cell::RefCell;
use core::num::NonZeroU32;

use alloc::vec::Vec;

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

/// Mapping edge lables to child ids using `BTreeMap`.
type EdgeMap<L> = alloc::collections::BTreeMap<L, u32>;

/// State of [`NfaBuilder`].
#[derive(Clone)]
pub struct NfaBuilderState<L, V> {
    pub(crate) edges: EdgeMap<L>,
    pub(crate) fail: u32,
    pub(crate) output: Option<(V, NonZeroU32)>,
    pub(crate) output_pos: Option<NonZeroU32>,
}

impl<L, V> Default for NfaBuilderState<L, V> {
    fn default() -> Self {
        Self {
            edges: EdgeMap::<L>::default(),
            fail: ROOT_STATE_ID,
            output: None,
            output_pos: None,
        }
    }
}

/// Builder of an Aho-Corasick automaton.
pub struct NfaBuilder<L, V> {
    pub(crate) states: Vec<RefCell<NfaBuilderState<L, V>>>,
    pub(crate) outputs: Vec<Output<V>>, // in which common parts are merged.
    pub(crate) len: usize,
    pub(crate) match_kind: MatchKind,
}

impl<L, V> NfaBuilder<L, V>
where
    L: EdgeLabel,
    V: Copy + Default,
{
    pub(crate) fn new(match_kind: MatchKind) -> Self {
        Self {
            states: vec![
                RefCell::new(NfaBuilderState::<L, V>::default()), // root
                RefCell::new(NfaBuilderState::<L, V>::default()), // dead
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
        let pattern_len = NonZeroU32::new(pattern_len)
            .ok_or_else(|| DaachorseError::invalid_argument("pattern.len()", ">=", 1))?;

        let mut state_id = ROOT_STATE_ID;
        for &c in pattern {
            if self.match_kind.is_leftmost_first() {
                // If state_id has an output, the descendants will never searched.
                let output = &self.states[usize::from_u32(state_id)].borrow().output;
                if output.is_some() {
                    return Ok(());
                }
            }

            if let Some(next_state_id) = self.get_child_id(state_id, c) {
                state_id = next_state_id;
            } else if let Ok(next_state_id) = u32::try_from(self.states.len()) {
                self.states[usize::from_u32(state_id)]
                    .borrow_mut()
                    .edges
                    .insert(c, next_state_id);
                self.states
                    .push(RefCell::new(NfaBuilderState::<L, V>::default()));
                state_id = next_state_id;
            } else {
                return Err(DaachorseError::automaton_scale("state_id", u32::MAX));
            }
        }

        let output = &mut self.states[usize::from_u32(state_id)].borrow_mut().output;
        if output.replace((value, pattern_len)).is_some() {
            return Err(DaachorseError::duplicate_pattern(format!("{:?}", pattern)));
        }

        self.len += 1;
        Ok(())
    }

    pub(crate) fn build_fails(&mut self) -> Vec<u32> {
        let mut q = Vec::with_capacity(self.states.len());
        for &child_id in self.states[usize::from_u32(ROOT_STATE_ID)]
            .borrow()
            .edges
            .values()
        {
            q.push(child_id);
        }

        let mut qi = 0;
        while qi < q.len() {
            let state_id = usize::from_u32(q[qi]);
            qi += 1;

            let s = &self.states[state_id].borrow();
            for (&c, &child_id) in &s.edges {
                let mut fail_id = s.fail;
                let new_fail_id = loop {
                    if let Some(child_fail_id) = self.get_child_id(fail_id, c) {
                        break child_fail_id;
                    }
                    let next_fail_id = self.states[usize::from_u32(fail_id)].borrow().fail;
                    if fail_id == ROOT_STATE_ID && next_fail_id == ROOT_STATE_ID {
                        break ROOT_STATE_ID;
                    }
                    fail_id = next_fail_id;
                };
                self.states[usize::from_u32(child_id)].borrow_mut().fail = new_fail_id;
                q.push(child_id);
            }
        }
        q
    }

    pub(crate) fn build_fails_leftmost(&mut self) -> Vec<u32> {
        let mut q = Vec::with_capacity(self.states.len());
        for &child_id in self.states[usize::from_u32(ROOT_STATE_ID)]
            .borrow()
            .edges
            .values()
        {
            q.push(child_id);
        }

        let mut qi = 0;
        while qi < q.len() {
            let state_id = usize::from_u32(q[qi]);
            qi += 1;

            let s = &mut self.states[state_id].borrow_mut();

            // Sets the output state to the dead fail.
            if s.output.is_some() {
                s.fail = DEAD_STATE_ID;
            }

            for (&c, &child_id) in &s.edges {
                let mut fail_id = s.fail;

                // If the parent has the dead fail, the child also has the dead fail.
                let new_fail_id = if fail_id == DEAD_STATE_ID {
                    DEAD_STATE_ID
                } else {
                    loop {
                        if let Some(child_fail_id) = self.get_child_id(fail_id, c) {
                            break child_fail_id;
                        }
                        let next_fail_id = self.states[usize::from_u32(fail_id)].borrow().fail;
                        if next_fail_id == DEAD_STATE_ID {
                            break DEAD_STATE_ID;
                        }
                        if fail_id == ROOT_STATE_ID && next_fail_id == ROOT_STATE_ID {
                            break ROOT_STATE_ID;
                        }
                        fail_id = next_fail_id;
                    }
                };

                self.states[usize::from_u32(child_id)].borrow_mut().fail = new_fail_id;
                q.push(child_id);
            }
        }
        q
    }

    pub(crate) fn build_outputs(&mut self, q: &[u32]) {
        // The queue (built in build_fails or _leftmost) will not have the root state id,
        // so in the following processing the output of the root state will not be handled.
        // But, there is no problem since Daachorse does not allow an empty pattern.
        debug_assert_ne!(q[0], ROOT_STATE_ID);

        // Adds a dummy output so that the output_pos is positive.
        self.outputs.push(Output::new(V::default(), 0, None));

        for &state_id in q {
            let s = &mut self.states[usize::from_u32(state_id)].borrow_mut();
            if let Some(output) = s.output {
                s.output_pos = NonZeroU32::new(u32::try_from(self.outputs.len()).unwrap());
                let parent = self.states[usize::from_u32(s.fail)].borrow().output_pos;
                self.outputs
                    .push(Output::new(output.0, output.1.get(), parent));
            } else {
                s.output_pos = self.states[usize::from_u32(s.fail)].borrow().output_pos;
            }
        }
    }

    #[inline(always)]
    fn get_child_id(&self, state_id: u32, c: L) -> Option<u32> {
        self.states[usize::from_u32(state_id)]
            .borrow()
            .edges
            .get(&c)
            .copied()
    }
}
