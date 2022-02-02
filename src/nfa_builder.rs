use std::cell::RefCell;

use crate::errors::{DaachorseError, Result};
use crate::{MatchKind, Output, OUTPUT_POS_INVALID};

// The maximum value of a pattern used as an invalid value.
pub const VALUE_INVALID: u32 = std::u32::MAX;
// The maximum length of a pattern used as an invalid value.
pub const LENGTH_INVALID: u32 = std::u32::MAX >> 1;
// The root state id of SparseNFA.
pub const ROOT_STATE_ID: u32 = 0;
// The dead state id of SparseNFA.
pub const DEAD_STATE_ID: u32 = 1;

pub trait EdgeLabel: Copy + Ord + std::fmt::Debug {
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
type EdgeMap<L> = std::collections::BTreeMap<L, u32>;

/// State of [`NfaBuilder`].
#[derive(Clone)]
pub struct NfaBuilderState<L> {
    pub(crate) edges: EdgeMap<L>,
    pub(crate) fail: u32,
    pub(crate) output: (u32, u32),
    pub(crate) output_pos: u32,
}

impl<L> Default for NfaBuilderState<L> {
    fn default() -> Self {
        Self {
            edges: EdgeMap::<L>::default(),
            fail: ROOT_STATE_ID,
            output: (VALUE_INVALID, LENGTH_INVALID),
            output_pos: OUTPUT_POS_INVALID,
        }
    }
}

/// Builder of an Aho-Corasick automaton.
pub struct NfaBuilder<L> {
    pub(crate) states: Vec<RefCell<NfaBuilderState<L>>>,
    pub(crate) outputs: Vec<Output>, // in which common parts are merged.
    pub(crate) len: usize,
    pub(crate) match_kind: MatchKind,
}

impl<L> NfaBuilder<L>
where
    L: EdgeLabel,
{
    pub(crate) fn new(match_kind: MatchKind) -> Self {
        Self {
            states: vec![
                RefCell::new(NfaBuilderState::<L>::default()), // root
                RefCell::new(NfaBuilderState::<L>::default()), // dead
            ],
            outputs: vec![],
            len: 0,
            match_kind,
        }
    }

    #[inline(always)]
    pub(crate) fn add(&mut self, pattern: &[L], value: u32) -> Result<()> {
        // Clippy suggests to use `==` in the following comparison instead, but that is dangerous.
        // Since `VALUE_INVALID` is defined as a constant variable, so developers may forget to
        // change this operator when they change the constant value.
        #[allow(clippy::absurd_extreme_comparisons)]
        if value >= VALUE_INVALID {
            return Err(DaachorseError::invalid_argument(
                "value",
                "<",
                VALUE_INVALID,
            ));
        }
        if pattern.len() >= LENGTH_INVALID as usize {
            return Err(DaachorseError::invalid_argument(
                "pattern.len()",
                "<",
                LENGTH_INVALID,
            ));
        }
        if pattern.is_empty() {
            return Err(DaachorseError::invalid_argument("pattern.len()", ">=", 1));
        }

        let mut state_id = ROOT_STATE_ID;
        for &c in pattern {
            if self.match_kind.is_leftmost_first() {
                // If state_id has an output, the descendants will never searched.
                let output = &self.states[state_id as usize].borrow().output;
                if output.0 != VALUE_INVALID {
                    return Ok(());
                }
            }

            if let Some(next_state_id) = self.get_child_id(state_id, c) {
                state_id = next_state_id;
            } else if let Ok(next_state_id) = self.states.len().try_into() {
                self.states[state_id as usize]
                    .borrow_mut()
                    .edges
                    .insert(c, next_state_id);
                self.states
                    .push(RefCell::new(NfaBuilderState::<L>::default()));
                state_id = next_state_id;
            } else {
                return Err(DaachorseError::automaton_scale("state_id", u32::MAX));
            }
        }

        let output = &mut self.states[state_id as usize].borrow_mut().output;
        if output.0 != VALUE_INVALID {
            return Err(DaachorseError::duplicate_pattern(format!("{:?}", pattern)));
        }

        *output = (
            value,
            pattern
                .iter()
                .fold(0, |acc, c| acc + c.num_bytes())
                .try_into()
                .unwrap(),
        );
        self.len += 1;
        Ok(())
    }

    pub(crate) fn build_fails(&mut self) -> Vec<u32> {
        let mut q = Vec::with_capacity(self.states.len());
        for &child_id in self.states[ROOT_STATE_ID as usize].borrow().edges.values() {
            q.push(child_id);
        }

        let mut qi = 0;
        while qi < q.len() {
            let state_id = q[qi] as usize;
            qi += 1;

            let s = &self.states[state_id].borrow();
            for (&c, &child_id) in &s.edges {
                let mut fail_id = s.fail;
                let new_fail_id = loop {
                    if let Some(child_fail_id) = self.get_child_id(fail_id, c) {
                        break child_fail_id;
                    }
                    let next_fail_id = self.states[fail_id as usize].borrow().fail;
                    if fail_id == ROOT_STATE_ID && next_fail_id == ROOT_STATE_ID {
                        break ROOT_STATE_ID;
                    }
                    fail_id = next_fail_id;
                };
                self.states[child_id as usize].borrow_mut().fail = new_fail_id;
                q.push(child_id);
            }
        }
        q
    }

    pub(crate) fn build_fails_leftmost(&mut self) -> Vec<u32> {
        let mut q = Vec::with_capacity(self.states.len());
        for &child_id in self.states[ROOT_STATE_ID as usize].borrow().edges.values() {
            q.push(child_id);
        }

        let mut qi = 0;
        while qi < q.len() {
            let state_id = q[qi] as usize;
            qi += 1;

            let s = &mut self.states[state_id].borrow_mut();

            // Sets the output state to the dead fail.
            if s.output.0 != VALUE_INVALID {
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
                        let next_fail_id = self.states[fail_id as usize].borrow().fail;
                        if next_fail_id == DEAD_STATE_ID {
                            break DEAD_STATE_ID;
                        }
                        if fail_id == ROOT_STATE_ID && next_fail_id == ROOT_STATE_ID {
                            break ROOT_STATE_ID;
                        }
                        fail_id = next_fail_id;
                    }
                };

                self.states[child_id as usize].borrow_mut().fail = new_fail_id;
                q.push(child_id);
            }
        }
        q
    }

    pub(crate) fn build_outputs(&mut self, q: &[u32]) -> Result<()> {
        // The queue (built in build_fails or _leftmost) will not have the root state id,
        // so in the following processing the output of the root state will not be handled.
        // But, there is no problem since Daachorse does not allow an empty pattern.
        debug_assert_ne!(q[0], ROOT_STATE_ID);

        let mut processed = vec![false; self.states.len()];

        // Builds an output sequence in which common parts are merged.
        for &state_id in q.iter().rev() {
            {
                let s = &mut self.states[state_id as usize].borrow_mut();
                if s.output.0 == VALUE_INVALID {
                    continue;
                }

                if processed[state_id as usize] {
                    debug_assert_ne!(s.output_pos, OUTPUT_POS_INVALID);
                    continue;
                }
                debug_assert_eq!(s.output_pos, OUTPUT_POS_INVALID);
                processed[state_id as usize] = true;

                s.output_pos = self.outputs.len().try_into().unwrap();
                self.outputs.push(Output::new(s.output.0, s.output.1, true));
                Self::check_outputs_error(&self.outputs)?;
            }

            let mut fail_id = state_id;
            loop {
                fail_id = self.states[fail_id as usize].borrow().fail;
                if fail_id == ROOT_STATE_ID || fail_id == DEAD_STATE_ID {
                    break;
                }

                let s = &mut self.states[fail_id as usize].borrow_mut();
                if s.output.0 == VALUE_INVALID {
                    continue;
                }

                if processed[fail_id as usize] {
                    debug_assert_ne!(s.output_pos, OUTPUT_POS_INVALID);
                    let mut clone_pos = s.output_pos as usize;
                    debug_assert!(!self.outputs[clone_pos].is_begin());
                    while !self.outputs[clone_pos].is_begin() {
                        self.outputs.push(self.outputs[clone_pos]);
                        clone_pos += 1;
                    }
                    Self::check_outputs_error(&self.outputs)?;
                    break;
                }
                processed[fail_id as usize] = true;

                s.output_pos = self.outputs.len().try_into().unwrap();
                self.outputs
                    .push(Output::new(s.output.0, s.output.1, false));
                Self::check_outputs_error(&self.outputs)?;
            }
        }

        // Puts a sentinel
        self.outputs
            .push(Output::new(VALUE_INVALID, LENGTH_INVALID, true));
        self.outputs.shrink_to_fit();
        Self::check_outputs_error(&self.outputs)?;

        self.set_dummy_outputs(q, &processed);

        Ok(())
    }

    fn set_dummy_outputs(&mut self, q: &[u32], processed: &[bool]) {
        for &state_id in q {
            let state_id = state_id as usize;
            let s = &mut self.states[state_id].borrow_mut();
            if processed[state_id] {
                debug_assert_ne!(s.output_pos, OUTPUT_POS_INVALID);
                continue;
            }
            debug_assert_eq!(s.output_pos, OUTPUT_POS_INVALID);
            debug_assert_eq!(s.output.0, VALUE_INVALID);

            let fail_id = s.fail;
            if fail_id != DEAD_STATE_ID {
                s.output_pos = self.states[fail_id as usize].borrow().output_pos;
            }
        }
    }

    #[inline(always)]
    fn check_outputs_error(outputs: &[Output]) -> Result<()> {
        if outputs.len() > OUTPUT_POS_INVALID as usize {
            Err(DaachorseError::automaton_scale(
                "outputs.len()",
                OUTPUT_POS_INVALID,
            ))
        } else {
            Ok(())
        }
    }

    #[inline(always)]
    fn get_child_id(&self, state_id: u32, c: L) -> Option<u32> {
        self.states[state_id as usize]
            .borrow()
            .edges
            .get(&c)
            .cloned()
    }
}
