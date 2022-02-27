//! Definition of errors.

use core::result;

use alloc::fmt;
use alloc::string::String;

#[cfg(feature = "std")]
use std::error::Error;

/// Errors in daachorse.
#[derive(Debug)]
pub enum DaachorseError {
    /// Contains [`InvalidArgumentError`].
    InvalidArgument(InvalidArgumentError),

    /// Contains [`DuplicatePatternError`].
    DuplicatePattern(DuplicatePatternError),

    /// Contains [`AutomatonScaleError`].
    AutomatonScale(AutomatonScaleError),
}

impl fmt::Display for DaachorseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InvalidArgument(e) => e.fmt(f),
            Self::DuplicatePattern(e) => e.fmt(f),
            Self::AutomatonScale(e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl Error for DaachorseError {}

impl DaachorseError {
    pub(crate) const fn invalid_argument(arg: &'static str, op: &'static str, value: u32) -> Self {
        Self::InvalidArgument(InvalidArgumentError { arg, op, value })
    }

    pub(crate) const fn duplicate_pattern(pattern: String) -> Self {
        Self::DuplicatePattern(DuplicatePatternError { pattern })
    }

    pub(crate) const fn automaton_scale(arg: &'static str, max_value: u32) -> Self {
        Self::AutomatonScale(AutomatonScaleError { arg, max_value })
    }
}

/// Error used when the argument is invalid.
#[derive(Debug)]
pub struct InvalidArgumentError {
    /// Name of the argument.
    arg: &'static str,

    /// Condition operator.
    op: &'static str,

    /// Condition value.
    value: u32,
}

impl fmt::Display for InvalidArgumentError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "InvalidArgumentError: {} must be {} {}",
            self.arg, self.op, self.value
        )
    }
}

#[cfg(feature = "std")]
impl Error for InvalidArgumentError {}

/// Error used when some patterns are duplicated.
#[derive(Debug)]
pub struct DuplicatePatternError {
    /// A duplicate pattern.
    pattern: String,
}

impl fmt::Display for DuplicatePatternError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DuplicatePatternError: {}", self.pattern)
    }
}

#[cfg(feature = "std")]
impl Error for DuplicatePatternError {}

/// Error used when the scale of the automaton exceeds the expected one.
#[derive(Debug)]
pub struct AutomatonScaleError {
    /// Name of the argument.
    arg: &'static str,

    /// The maximum value (inclusive).
    max_value: u32,
}

impl fmt::Display for AutomatonScaleError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "AutomatonScaleError: {} must be <= {}",
            self.arg, self.max_value
        )
    }
}

#[cfg(feature = "std")]
impl Error for AutomatonScaleError {}

/// A specialized Result type for Daachorse.
pub type Result<T, E = DaachorseError> = result::Result<T, E>;
