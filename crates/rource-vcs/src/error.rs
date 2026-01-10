//! Error types for VCS parsing.
//!
//! This module defines the error types used throughout the VCS parsing
//! subsystem, providing detailed error information for debugging.

use std::fmt;
use std::io;

/// Errors that can occur during VCS log parsing.
#[derive(Debug)]
pub enum ParseError {
    /// An I/O error occurred while reading the log.
    Io(io::Error),

    /// A line in the log could not be parsed.
    InvalidLine {
        /// The line number (1-indexed) where the error occurred.
        line_number: usize,
        /// The content of the invalid line.
        line: String,
        /// Description of what was expected.
        expected: &'static str,
    },

    /// A required field was missing from a log entry.
    MissingField {
        /// The line number (1-indexed) where the error occurred.
        line_number: usize,
        /// The name of the missing field.
        field: &'static str,
    },

    /// A timestamp could not be parsed.
    InvalidTimestamp {
        /// The line number (1-indexed) where the error occurred.
        line_number: usize,
        /// The invalid timestamp string.
        value: String,
    },

    /// A file action character was not recognized.
    InvalidAction {
        /// The line number (1-indexed) where the error occurred.
        line_number: usize,
        /// The invalid action string.
        value: String,
    },

    /// A color value could not be parsed.
    InvalidColor {
        /// The line number (1-indexed) where the error occurred.
        line_number: usize,
        /// The invalid color string.
        value: String,
    },

    /// The log format could not be detected.
    UnknownFormat,

    /// The log is empty or contains no valid commits.
    EmptyLog,

    /// UTF-8 decoding error.
    Utf8Error(std::str::Utf8Error),

    /// A custom error message.
    Custom(String),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(err) => write!(f, "I/O error: {err}"),
            Self::InvalidLine {
                line_number,
                line,
                expected,
            } => {
                write!(
                    f,
                    "line {line_number}: invalid format, expected {expected}: {line:?}"
                )
            }
            Self::MissingField { line_number, field } => {
                write!(f, "line {line_number}: missing required field '{field}'")
            }
            Self::InvalidTimestamp { line_number, value } => {
                write!(f, "line {line_number}: invalid timestamp: {value:?}")
            }
            Self::InvalidAction { line_number, value } => {
                write!(f, "line {line_number}: invalid action: {value:?}")
            }
            Self::InvalidColor { line_number, value } => {
                write!(f, "line {line_number}: invalid color: {value:?}")
            }
            Self::UnknownFormat => write!(f, "could not detect log format"),
            Self::EmptyLog => write!(f, "log is empty or contains no valid commits"),
            Self::Utf8Error(err) => write!(f, "UTF-8 error: {err}"),
            Self::Custom(msg) => write!(f, "{msg}"),
        }
    }
}

impl std::error::Error for ParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(err) => Some(err),
            Self::Utf8Error(err) => Some(err),
            _ => None,
        }
    }
}

impl From<io::Error> for ParseError {
    fn from(err: io::Error) -> Self {
        Self::Io(err)
    }
}

impl From<std::str::Utf8Error> for ParseError {
    fn from(err: std::str::Utf8Error) -> Self {
        Self::Utf8Error(err)
    }
}

/// Result type for parsing operations.
pub type ParseResult<T> = Result<T, ParseError>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_display() {
        let err = ParseError::InvalidLine {
            line_number: 42,
            line: "bad|line".to_string(),
            expected: "timestamp|user|action|path",
        };
        let msg = err.to_string();
        assert!(msg.contains("42"));
        assert!(msg.contains("bad|line"));
    }

    #[test]
    fn test_error_from_io() {
        let io_err = io::Error::new(io::ErrorKind::NotFound, "file not found");
        let parse_err: ParseError = io_err.into();
        assert!(matches!(parse_err, ParseError::Io(_)));
    }

    #[test]
    fn test_error_is_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<ParseError>();
    }
}
