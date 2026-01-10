//! VCS format auto-detection.
//!
//! This module provides automatic detection of VCS log formats
//! based on content analysis.

use crate::commit::Commit;
use crate::error::{ParseError, ParseResult};
use crate::parser::{CustomParser, GitParser, Parser};
use std::io::Read;
use std::path::Path;

/// Supported VCS log formats.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogFormat {
    /// Custom pipe-delimited format (Gource-compatible).
    Custom,
    /// Git log output format.
    Git,
}

impl LogFormat {
    /// Returns the human-readable name of this format.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Custom => "custom",
            Self::Git => "git",
        }
    }

    /// Creates a parser for this format.
    #[must_use]
    pub fn parser(self) -> Box<dyn Parser> {
        match self {
            Self::Custom => Box::new(CustomParser::new()),
            Self::Git => Box::new(GitParser::new()),
        }
    }
}

impl std::fmt::Display for LogFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// Auto-detects the format of a log string.
///
/// Analyzes the first few lines of the input to determine
/// which parser should be used.
///
/// # Arguments
///
/// * `input` - The log content to analyze
///
/// # Returns
///
/// The detected format, or an error if no format matches.
///
/// # Example
///
/// ```
/// use rource_vcs::detect::detect_format;
///
/// let custom_log = "1234567890|John|A|file.txt\n";
/// let format = detect_format(custom_log).unwrap();
/// assert_eq!(format.name(), "custom");
///
/// let git_log = "commit abc123def\nAuthor: John <j@test.com>\nDate: 1234567890\n";
/// let format = detect_format(git_log).unwrap();
/// assert_eq!(format.name(), "git");
/// ```
#[must_use]
pub fn detect_format(input: &str) -> Option<LogFormat> {
    // Order matters: more specific formats first
    let parsers: &[(LogFormat, Box<dyn Parser>)] = &[
        (LogFormat::Git, Box::new(GitParser::new())),
        (LogFormat::Custom, Box::new(CustomParser::new())),
    ];

    for (format, parser) in parsers {
        if parser.can_parse(input) {
            return Some(*format);
        }
    }

    None
}

/// Parses a log string with automatic format detection.
///
/// This function first detects the format, then parses the content
/// using the appropriate parser.
///
/// # Arguments
///
/// * `input` - The log content to parse
///
/// # Returns
///
/// A tuple of (detected format, parsed commits), or an error.
///
/// # Example
///
/// ```
/// use rource_vcs::detect::parse_auto;
///
/// let log = "1234567890|John|A|file.txt\n";
/// let (format, commits) = parse_auto(log).unwrap();
/// assert_eq!(commits.len(), 1);
/// ```
pub fn parse_auto(input: &str) -> ParseResult<(LogFormat, Vec<Commit>)> {
    let format = detect_format(input).ok_or(ParseError::UnknownFormat)?;
    let parser = format.parser();
    let commits = parser.parse_str(input)?;
    Ok((format, commits))
}

/// Parses a log file with automatic format detection.
///
/// # Arguments
///
/// * `path` - Path to the log file
///
/// # Returns
///
/// A tuple of (detected format, parsed commits), or an error.
pub fn parse_file_auto<P: AsRef<Path>>(path: P) -> ParseResult<(LogFormat, Vec<Commit>)> {
    let content = std::fs::read_to_string(path)?;
    parse_auto(&content)
}

/// Parses from a reader with automatic format detection.
///
/// # Arguments
///
/// * `reader` - Any type implementing `Read`
///
/// # Returns
///
/// A tuple of (detected format, parsed commits), or an error.
pub fn parse_reader_auto<R: Read>(mut reader: R) -> ParseResult<(LogFormat, Vec<Commit>)> {
    let mut content = String::new();
    reader.read_to_string(&mut content)?;
    parse_auto(&content)
}

/// Attempts to detect the VCS type from a directory.
///
/// Checks for common VCS directories like `.git`, `.svn`, etc.
///
/// # Arguments
///
/// * `path` - Path to the repository directory
///
/// # Returns
///
/// The detected VCS type, or `None` if no VCS is detected.
#[must_use]
pub fn detect_vcs_from_directory<P: AsRef<Path>>(path: P) -> Option<&'static str> {
    let path = path.as_ref();

    if path.join(".git").exists() {
        return Some("git");
    }
    if path.join(".svn").exists() {
        return Some("svn");
    }
    if path.join(".hg").exists() {
        return Some("mercurial");
    }
    if path.join(".bzr").exists() {
        return Some("bazaar");
    }
    if path.join("CVS").exists() {
        return Some("cvs");
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detect_custom_format() {
        let input = "1234567890|John Doe|A|src/main.rs\n";
        let format = detect_format(input).unwrap();
        assert_eq!(format, LogFormat::Custom);
    }

    #[test]
    fn test_detect_git_format() {
        let input = "\
commit abc123def456789012345678901234567890abcd
Author: John Doe <john@example.com>
Date: 1234567890

A\tsrc/main.rs
";
        let format = detect_format(input).unwrap();
        assert_eq!(format, LogFormat::Git);
    }

    #[test]
    fn test_detect_unknown_format() {
        let input = "This is not a valid log format";
        assert!(detect_format(input).is_none());
    }

    #[test]
    fn test_parse_auto_custom() {
        let input = "1234567890|John|A|file.txt\n1234567891|John|M|file.txt\n";
        let (format, commits) = parse_auto(input).unwrap();
        assert_eq!(format, LogFormat::Custom);
        assert_eq!(commits.len(), 2);
    }

    #[test]
    fn test_parse_auto_git() {
        let input = "\
commit abc123def456789012345678901234567890abcd
Author: John <john@test.com>
Date: 1234567890

A\tfile.txt
";
        let (format, commits) = parse_auto(input).unwrap();
        assert_eq!(format, LogFormat::Git);
        assert_eq!(commits.len(), 1);
    }

    #[test]
    fn test_parse_auto_unknown() {
        let input = "random text that isn't a log";
        let result = parse_auto(input);
        assert!(matches!(result, Err(ParseError::UnknownFormat)));
    }

    #[test]
    fn test_log_format_name() {
        assert_eq!(LogFormat::Custom.name(), "custom");
        assert_eq!(LogFormat::Git.name(), "git");
    }

    #[test]
    fn test_log_format_parser() {
        let parser = LogFormat::Custom.parser();
        assert_eq!(parser.name(), "custom");

        let parser = LogFormat::Git.parser();
        assert_eq!(parser.name(), "git");
    }

    #[test]
    fn test_log_format_display() {
        assert_eq!(format!("{}", LogFormat::Custom), "custom");
        assert_eq!(format!("{}", LogFormat::Git), "git");
    }

    #[test]
    fn test_detect_vcs_from_directory() {
        use std::fs;
        use std::env::temp_dir;

        let temp = temp_dir().join("rource_test_vcs_detect");
        let _ = fs::remove_dir_all(&temp);
        fs::create_dir_all(&temp).unwrap();

        // No VCS
        assert!(detect_vcs_from_directory(&temp).is_none());

        // Git
        fs::create_dir(temp.join(".git")).unwrap();
        assert_eq!(detect_vcs_from_directory(&temp), Some("git"));
        fs::remove_dir(temp.join(".git")).unwrap();

        // SVN
        fs::create_dir(temp.join(".svn")).unwrap();
        assert_eq!(detect_vcs_from_directory(&temp), Some("svn"));
        fs::remove_dir(temp.join(".svn")).unwrap();

        // Mercurial
        fs::create_dir(temp.join(".hg")).unwrap();
        assert_eq!(detect_vcs_from_directory(&temp), Some("mercurial"));
        fs::remove_dir(temp.join(".hg")).unwrap();

        // Bazaar
        fs::create_dir(temp.join(".bzr")).unwrap();
        assert_eq!(detect_vcs_from_directory(&temp), Some("bazaar"));
        fs::remove_dir(temp.join(".bzr")).unwrap();

        // CVS
        fs::create_dir(temp.join("CVS")).unwrap();
        assert_eq!(detect_vcs_from_directory(&temp), Some("cvs"));
        fs::remove_dir(temp.join("CVS")).unwrap();

        // Cleanup
        fs::remove_dir(&temp).unwrap();
    }

    #[test]
    fn test_parse_reader_auto() {
        use std::io::Cursor;

        let input = "1234567890|John|A|file.txt\n";
        let reader = Cursor::new(input);
        let (format, commits) = parse_reader_auto(reader).unwrap();
        assert_eq!(format, LogFormat::Custom);
        assert_eq!(commits.len(), 1);
    }
}
