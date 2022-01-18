use std::cell::RefCell;

use crate::errors::{
    AutomatonScaleError, DaachorseError, DuplicatePatternError, PatternScaleError,
};
use crate::{MatchKind, Output, OUTPUT_POS_INVALID};

// The maximum value of a pattern used as an invalid value.
pub const VALUE_INVALID: u32 = std::u32::MAX;
// The maximum length of a pattern used as an invalid value.
pub const LENGTH_INVALID: u32 = std::u32::MAX >> 1;
// The root state id of SparseNFA.
pub const ROOT_STATE_ID: u32 = 0;
// The dead state id of SparseNFA.
pub const DEAD_STATE_ID: u32 = 1;

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
    L: Copy + Ord + std::fmt::Debug,
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
    pub(crate) fn add(&mut self, pattern: &[L], value: u32) -> Result<(), DaachorseError> {
        if value == VALUE_INVALID {
            let e = PatternScaleError {
                msg: format!("Input value must be < {}", VALUE_INVALID),
            };
            return Err(DaachorseError::PatternScale(e));
        }
        if pattern.len() >= LENGTH_INVALID as usize {
            let e = PatternScaleError {
                msg: format!("Pattern length must be < {}", LENGTH_INVALID),
            };
            return Err(DaachorseError::PatternScale(e));
        }
        if pattern.is_empty() {
            let e = PatternScaleError {
                msg: "Pattern must not be empty".to_string(),
            };
            return Err(DaachorseError::PatternScale(e));
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
                let e = AutomatonScaleError {
                    msg: "A state id must be represented with u32".to_string(),
                };
                return Err(DaachorseError::AutomatonScale(e));
            }
        }

        let output = &mut self.states[state_id as usize].borrow_mut().output;
        if output.0 != VALUE_INVALID {
            let e = DuplicatePatternError {
                pattern: format!("{:?}", pattern),
            };
            return Err(DaachorseError::DuplicatePattern(e));
        }
        *output = (value, pattern.len().try_into().unwrap());
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

    pub(crate) fn build_outputs(&mut self, q: &[u32]) -> Result<(), DaachorseError> {
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
    fn check_outputs_error(outputs: &[Output]) -> Result<(), DaachorseError> {
        if outputs.len() > OUTPUT_POS_INVALID as usize {
            let e = AutomatonScaleError {
                msg: format!("outputs.len() must be <= {}", OUTPUT_POS_INVALID),
            };
            Err(DaachorseError::AutomatonScale(e))
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
