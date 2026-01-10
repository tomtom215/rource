//! VCS log format parsers.
//!
//! This module provides parsers for various version control system log formats:
//!
//! - [`CustomParser`] - Pipe-delimited custom format (Gource-compatible)
//! - [`GitParser`] - Git log output format
//!
//! # Usage
//!
//! ```
//! use rource_vcs::parser::{CustomParser, Parser};
//!
//! let log = "1234567890|John Doe|A|src/main.rs\n";
//! let parser = CustomParser::new();
//! let commits = parser.parse_str(log).unwrap();
//! assert_eq!(commits.len(), 1);
//! ```

mod custom;
mod git;

pub use custom::CustomParser;
pub use git::GitParser;

use crate::commit::Commit;
use crate::error::ParseResult;
use std::path::Path;

/// Trait for VCS log parsers.
///
/// Implementations of this trait can parse commit logs from various sources.
/// This trait is object-safe, allowing parsers to be used as trait objects.
pub trait Parser: Send + Sync {
    /// Returns the name of this parser (e.g., "custom", "git").
    fn name(&self) -> &'static str;

    /// Parses commits from a string.
    ///
    /// # Arguments
    ///
    /// * `input` - The log content as a string
    ///
    /// # Returns
    ///
    /// A vector of parsed commits, or an error if parsing failed.
    fn parse_str(&self, input: &str) -> ParseResult<Vec<Commit>>;

    /// Checks if this parser can handle the given input.
    ///
    /// Used for auto-detection. Implementations should check a small
    /// prefix of the input to determine if it matches the expected format.
    ///
    /// # Arguments
    ///
    /// * `input` - A sample of the log content (usually the first few lines)
    ///
    /// # Returns
    ///
    /// `true` if this parser can handle the input, `false` otherwise.
    fn can_parse(&self, input: &str) -> bool;
}

/// Parses commits from a file using the given parser.
///
/// # Arguments
///
/// * `parser` - The parser to use
/// * `path` - Path to the log file
///
/// # Returns
///
/// A vector of parsed commits, or an error if parsing failed.
pub fn parse_file<P: Parser + ?Sized>(parser: &P, path: impl AsRef<Path>) -> ParseResult<Vec<Commit>> {
    let content = std::fs::read_to_string(path)?;
    parser.parse_str(&content)
}

/// Options for parsing behavior.
#[derive(Debug, Clone)]
pub struct ParseOptions {
    /// Maximum number of commits to parse (0 = unlimited).
    pub max_commits: usize,

    /// Whether to skip commits with no file changes.
    pub skip_empty_commits: bool,

    /// Whether to continue parsing after encountering an invalid line.
    pub skip_invalid_lines: bool,

    /// Start timestamp filter (Unix timestamp, 0 = no filter).
    pub start_time: i64,

    /// End timestamp filter (Unix timestamp, 0 = no filter).
    pub end_time: i64,
}

impl Default for ParseOptions {
    fn default() -> Self {
        Self {
            max_commits: 0,
            skip_empty_commits: true,
            skip_invalid_lines: false,
            start_time: 0,
            end_time: 0,
        }
    }
}

impl ParseOptions {
    /// Creates options with unlimited commits and strict parsing.
    pub fn strict() -> Self {
        Self {
            skip_invalid_lines: false,
            ..Default::default()
        }
    }

    /// Creates options that skip invalid lines (lenient parsing).
    pub fn lenient() -> Self {
        Self {
            skip_invalid_lines: true,
            ..Default::default()
        }
    }

    /// Sets the maximum number of commits to parse.
    pub fn with_max_commits(mut self, max: usize) -> Self {
        self.max_commits = max;
        self
    }

    /// Sets the time range filter.
    pub fn with_time_range(mut self, start: i64, end: i64) -> Self {
        self.start_time = start;
        self.end_time = end;
        self
    }

    /// Checks if a timestamp passes the time filter.
    pub fn timestamp_in_range(&self, timestamp: i64) -> bool {
        (self.start_time == 0 || timestamp >= self.start_time)
            && (self.end_time == 0 || timestamp <= self.end_time)
    }

    /// Checks if the commit limit has been reached.
    pub fn limit_reached(&self, count: usize) -> bool {
        self.max_commits > 0 && count >= self.max_commits
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_options_default() {
        let opts = ParseOptions::default();
        assert_eq!(opts.max_commits, 0);
        assert!(opts.skip_empty_commits);
        assert!(!opts.skip_invalid_lines);
    }

    #[test]
    fn test_parse_options_strict() {
        let opts = ParseOptions::strict();
        assert!(!opts.skip_invalid_lines);
    }

    #[test]
    fn test_parse_options_lenient() {
        let opts = ParseOptions::lenient();
        assert!(opts.skip_invalid_lines);
    }

    #[test]
    fn test_timestamp_in_range() {
        let opts = ParseOptions::default().with_time_range(100, 200);
        assert!(!opts.timestamp_in_range(50));
        assert!(opts.timestamp_in_range(100));
        assert!(opts.timestamp_in_range(150));
        assert!(opts.timestamp_in_range(200));
        assert!(!opts.timestamp_in_range(250));

        // No filter
        let opts = ParseOptions::default();
        assert!(opts.timestamp_in_range(0));
        assert!(opts.timestamp_in_range(i64::MAX));
    }

    #[test]
    fn test_limit_reached() {
        let opts = ParseOptions::default().with_max_commits(10);
        assert!(!opts.limit_reached(0));
        assert!(!opts.limit_reached(9));
        assert!(opts.limit_reached(10));
        assert!(opts.limit_reached(11));

        // No limit
        let opts = ParseOptions::default();
        assert!(!opts.limit_reached(1000000));
    }
}
