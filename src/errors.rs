//! Definition of errors.

use std::error::Error;
use std::fmt;

/// Errors in daachorse.
#[derive(Debug)]
pub enum DaachorseError {
    /// Contains [`InvalidArgumentError`].
    InvalidArgument(InvalidArgumentError),

    /// Contains [`DuplicatePatternError`].
    DuplicatePattern(DuplicatePatternError),

    /// Contains [`PatternScaleError`].
    PatternScale(PatternScaleError),

    /// Contains [`AutomatonScaleError`].
    AutomatonScale(AutomatonScaleError),
}

impl fmt::Display for DaachorseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InvalidArgument(e) => e.fmt(f),
            Self::DuplicatePattern(e) => e.fmt(f),
            Self::PatternScale(e) => e.fmt(f),
            Self::AutomatonScale(e) => e.fmt(f),
        }
    }
}

impl Error for DaachorseError {}

/// Error used when the argument is invalid.
#[derive(Debug)]
pub struct InvalidArgumentError {
    /// Name of the argument.
    pub(crate) arg: &'static str,

    /// Error message.
    pub(crate) msg: String,
}

impl fmt::Display for InvalidArgumentError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "InvalidArgumentError: {}: {}", self.arg, self.msg)
    }
}

impl Error for InvalidArgumentError {}

/// Error used when some patterns are duplicated.
#[derive(Debug)]
pub struct DuplicatePatternError {
    /// A duplicate pattern.
    pub(crate) pattern: String,
}

impl fmt::Display for DuplicatePatternError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DuplicatePatternError: {}", self.pattern)
    }
}

impl Error for DuplicatePatternError {}

/// Error used when the scale of input patterns exceeds the expected one.
#[derive(Debug)]
pub struct PatternScaleError {
    pub(crate) msg: String,
}

impl fmt::Display for PatternScaleError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PatternScaleError: {}", self.msg)
    }
}

impl Error for PatternScaleError {}

/// Error used when the scale of the automaton exceeds the expected one.
#[derive(Debug)]
pub struct AutomatonScaleError {
    pub(crate) msg: String,
}

impl fmt::Display for AutomatonScaleError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "AutomatonScaleError: {}", self.msg)
    }
}

impl Error for AutomatonScaleError {}
