// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Custom pipe-delimited log format parser.
//!
//! This parser handles the Gource-compatible custom log format:
//!
//! ```text
//! timestamp|username|action|filepath[|color]
//! ```
//!
//! Where:
//! - `timestamp`: Unix timestamp (seconds since epoch)
//! - `username`: Author/contributor name
//! - `action`: A (add/create), M (modify), D (delete)
//! - `filepath`: Path relative to repository root
//! - `color`: Optional hex color (e.g., "FF0000" for red)
//!
//! # Example
//!
//! ```text
//! 1234567890|John Doe|A|src/main.rs
//! 1234567891|John Doe|M|src/main.rs
//! 1234567892|Jane Smith|A|src/lib.rs|00FF00
//! 1234567893|John Doe|D|old/file.txt
//! ```
//!
//! Multiple entries with the same timestamp and username are grouped
//! into a single commit.

use crate::commit::{Commit, FileAction, FileChange};
use crate::error::{ParseError, ParseResult};
use crate::parser::{ParseOptions, Parser};
use std::collections::HashMap;

/// Parser for the custom pipe-delimited format.
///
/// This is the simplest and most portable log format, compatible with
/// the original Gource visualization tool.
#[derive(Debug, Clone)]
pub struct CustomParser {
    options: ParseOptions,
}

impl CustomParser {
    /// Creates a new custom format parser with default options.
    #[must_use]
    pub fn new() -> Self {
        Self {
            options: ParseOptions::default(),
        }
    }

    /// Creates a parser with the specified options.
    #[must_use]
    pub fn with_options(options: ParseOptions) -> Self {
        Self { options }
    }

    /// Parses a single line into its components.
    ///
    /// Returns (timestamp, username, action, filepath, `optional_color`)
    fn parse_line(
        line: &str,
        line_number: usize,
    ) -> ParseResult<(i64, &str, FileAction, &str, Option<&str>)> {
        let parts: Vec<&str> = line.split('|').collect();

        if parts.len() < 4 {
            return Err(ParseError::InvalidLine {
                line_number,
                line: line.to_string(),
                expected: "timestamp|username|action|filepath",
            });
        }

        // Parse timestamp
        let timestamp =
            parts[0]
                .trim()
                .parse::<i64>()
                .map_err(|_| ParseError::InvalidTimestamp {
                    line_number,
                    value: parts[0].to_string(),
                })?;

        // Parse username
        let username = parts[1].trim();
        if username.is_empty() {
            return Err(ParseError::MissingField {
                line_number,
                field: "username",
            });
        }

        // Parse action
        let action_str = parts[2].trim();
        let action =
            FileAction::from_char(action_str.chars().next().unwrap_or('?')).ok_or_else(|| {
                ParseError::InvalidAction {
                    line_number,
                    value: action_str.to_string(),
                }
            })?;

        // Parse filepath
        let filepath = parts[3].trim();
        if filepath.is_empty() {
            return Err(ParseError::MissingField {
                line_number,
                field: "filepath",
            });
        }

        // Parse optional color
        let color = if parts.len() > 4 {
            let color_str = parts[4].trim();
            if color_str.is_empty() {
                None
            } else {
                // Validate color format (should be 6 hex digits)
                if Self::is_valid_hex_color(color_str) {
                    Some(color_str)
                } else {
                    return Err(ParseError::InvalidColor {
                        line_number,
                        value: color_str.to_string(),
                    });
                }
            }
        } else {
            None
        };

        Ok((timestamp, username, action, filepath, color))
    }

    /// Validates a hex color string (6 hex digits).
    fn is_valid_hex_color(s: &str) -> bool {
        s.len() == 6 && s.chars().all(|c| c.is_ascii_hexdigit())
    }
}

impl Default for CustomParser {
    fn default() -> Self {
        Self::new()
    }
}

impl Parser for CustomParser {
    fn name(&self) -> &'static str {
        "custom"
    }

    fn parse_str(&self, input: &str) -> ParseResult<Vec<Commit>> {
        // Group entries by (timestamp, username) to form commits
        // Use a Vec to maintain insertion order
        let mut commit_map: HashMap<(i64, String), Vec<FileChange>> = HashMap::new();
        let mut commit_order: Vec<(i64, String)> = Vec::new();

        let mut line_number = 0;
        let mut error_count = 0;

        for line in input.lines() {
            line_number += 1;
            let line = line.trim();

            // Skip empty lines and comments
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            match Self::parse_line(line, line_number) {
                Ok((timestamp, username, action, filepath, _color)) => {
                    // Check time range filter
                    if !self.options.timestamp_in_range(timestamp) {
                        continue;
                    }

                    let key = (timestamp, username.to_string());
                    let file_change = FileChange::new(filepath, action);

                    if let Some(files) = commit_map.get_mut(&key) {
                        files.push(file_change);
                    } else {
                        commit_order.push(key.clone());
                        commit_map.insert(key, vec![file_change]);
                    }

                    // Check commit limit
                    if self.options.limit_reached(commit_order.len()) {
                        break;
                    }
                }
                Err(err) => {
                    if self.options.skip_invalid_lines {
                        error_count += 1;
                        continue;
                    }
                    return Err(err);
                }
            }
        }

        // Build commits in order
        let mut commits = Vec::with_capacity(commit_order.len());
        for (timestamp, username) in commit_order {
            if let Some(files) = commit_map.remove(&(timestamp, username.clone())) {
                // Skip empty commits if configured
                if self.options.skip_empty_commits && files.is_empty() {
                    continue;
                }

                // Generate a deterministic hash from timestamp and username
                let hash = format!("{:08x}{:08x}", timestamp as u32, hash_str(&username));

                let commit = Commit::new(hash, timestamp, username).with_files(files);
                commits.push(commit);
            }
        }

        if commits.is_empty() && error_count == 0 {
            return Err(ParseError::EmptyLog);
        }

        // Sort commits by timestamp (stable sort preserves order for same timestamp)
        commits.sort_by_key(|c| c.timestamp);

        Ok(commits)
    }

    fn can_parse(&self, input: &str) -> bool {
        // Check if the first non-empty, non-comment line matches the format
        for line in input.lines().take(10) {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            // Check if it looks like our format: number|text|letter|path
            let parts: Vec<&str> = line.split('|').collect();
            if parts.len() >= 4 {
                // Check timestamp is numeric
                if parts[0].trim().parse::<i64>().is_ok() {
                    // Check action is valid
                    let action = parts[2].trim();
                    if action.len() == 1
                        && FileAction::from_char(action.chars().next().unwrap()).is_some()
                    {
                        return true;
                    }
                }
            }

            // If first data line doesn't match, it's not our format
            return false;
        }

        false
    }
}

/// Simple string hash for generating deterministic commit hashes.
fn hash_str(s: &str) -> u32 {
    let mut hash: u32 = 5381;
    for b in s.bytes() {
        hash = hash.wrapping_mul(33).wrapping_add(u32::from(b));
    }
    hash
}

#[cfg(test)]
#[allow(clippy::unreadable_literal, clippy::items_after_statements)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_line() {
        let (ts, user, action, path, color) =
            CustomParser::parse_line("1234567890|John Doe|A|src/main.rs", 1).unwrap();

        assert_eq!(ts, 1234567890);
        assert_eq!(user, "John Doe");
        assert_eq!(action, FileAction::Create);
        assert_eq!(path, "src/main.rs");
        assert!(color.is_none());
    }

    #[test]
    fn test_parse_line_with_color() {
        let (_, _, _, _, color) =
            CustomParser::parse_line("1234567890|John|M|file.txt|FF0000", 1).unwrap();

        assert_eq!(color, Some("FF0000"));
    }

    #[test]
    fn test_parse_line_all_actions() {
        // Add/Create
        let (_, _, action, _, _) = CustomParser::parse_line("0|u|A|f", 1).unwrap();
        assert_eq!(action, FileAction::Create);

        // Modify
        let (_, _, action, _, _) = CustomParser::parse_line("0|u|M|f", 1).unwrap();
        assert_eq!(action, FileAction::Modify);

        // Delete
        let (_, _, action, _, _) = CustomParser::parse_line("0|u|D|f", 1).unwrap();
        assert_eq!(action, FileAction::Delete);

        // Lowercase
        let (_, _, action, _, _) = CustomParser::parse_line("0|u|a|f", 1).unwrap();
        assert_eq!(action, FileAction::Create);
    }

    #[test]
    fn test_parse_line_missing_fields() {
        let result = CustomParser::parse_line("1234567890|John Doe|A", 1);
        assert!(matches!(result, Err(ParseError::InvalidLine { .. })));
    }

    #[test]
    fn test_parse_line_invalid_timestamp() {
        let result = CustomParser::parse_line("not_a_number|John|A|file.txt", 1);
        assert!(matches!(result, Err(ParseError::InvalidTimestamp { .. })));
    }

    #[test]
    fn test_parse_line_invalid_action() {
        let result = CustomParser::parse_line("1234567890|John|X|file.txt", 1);
        assert!(matches!(result, Err(ParseError::InvalidAction { .. })));
    }

    #[test]
    fn test_parse_line_invalid_color() {
        let result = CustomParser::parse_line("1234567890|John|A|file.txt|GGGGGG", 1);
        assert!(matches!(result, Err(ParseError::InvalidColor { .. })));

        let result = CustomParser::parse_line("1234567890|John|A|file.txt|FF", 1);
        assert!(matches!(result, Err(ParseError::InvalidColor { .. })));
    }

    #[test]
    fn test_parse_line_empty_username() {
        let result = CustomParser::parse_line("1234567890||A|file.txt", 1);
        assert!(matches!(
            result,
            Err(ParseError::MissingField {
                field: "username",
                ..
            })
        ));
    }

    #[test]
    fn test_parse_line_empty_filepath() {
        let result = CustomParser::parse_line("1234567890|John|A|", 1);
        assert!(matches!(
            result,
            Err(ParseError::MissingField {
                field: "filepath",
                ..
            })
        ));
    }

    #[test]
    fn test_parse_single_commit() {
        let input = "1234567890|John Doe|A|src/main.rs\n";
        let parser = CustomParser::new();
        let commits = parser.parse_str(input).unwrap();

        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].author, "John Doe");
        assert_eq!(commits[0].timestamp, 1234567890);
        assert_eq!(commits[0].files.len(), 1);
        assert_eq!(commits[0].files[0].path.to_str().unwrap(), "src/main.rs");
        assert_eq!(commits[0].files[0].action, FileAction::Create);
    }

    #[test]
    fn test_parse_multiple_commits() {
        let input = "\
            1234567890|John Doe|A|src/main.rs\n\
            1234567891|Jane Smith|A|src/lib.rs\n\
            1234567892|John Doe|M|src/main.rs\n";

        let parser = CustomParser::new();
        let commits = parser.parse_str(input).unwrap();

        assert_eq!(commits.len(), 3);
        assert_eq!(commits[0].timestamp, 1234567890);
        assert_eq!(commits[1].timestamp, 1234567891);
        assert_eq!(commits[2].timestamp, 1234567892);
    }

    #[test]
    fn test_parse_grouped_commit() {
        // Same timestamp and username should be grouped
        let input = "\
            1234567890|John Doe|A|src/main.rs\n\
            1234567890|John Doe|A|src/lib.rs\n\
            1234567890|John Doe|M|Cargo.toml\n";

        let parser = CustomParser::new();
        let commits = parser.parse_str(input).unwrap();

        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].files.len(), 3);
    }

    #[test]
    fn test_parse_different_users_same_timestamp() {
        let input = "\
            1234567890|John Doe|A|src/main.rs\n\
            1234567890|Jane Smith|A|src/lib.rs\n";

        let parser = CustomParser::new();
        let commits = parser.parse_str(input).unwrap();

        assert_eq!(commits.len(), 2);
        assert_eq!(commits[0].author, "John Doe");
        assert_eq!(commits[1].author, "Jane Smith");
    }

    #[test]
    fn test_parse_skip_comments_and_empty() {
        let input = "\
            # This is a comment\n\
            \n\
            1234567890|John Doe|A|src/main.rs\n\
            \n\
            # Another comment\n\
            1234567891|Jane Smith|A|src/lib.rs\n";

        let parser = CustomParser::new();
        let commits = parser.parse_str(input).unwrap();

        assert_eq!(commits.len(), 2);
    }

    #[test]
    fn test_parse_sorted_by_timestamp() {
        let input = "\
            1234567892|John|A|c.txt\n\
            1234567890|John|A|a.txt\n\
            1234567891|John|A|b.txt\n";

        let parser = CustomParser::new();
        let commits = parser.parse_str(input).unwrap();

        assert_eq!(commits.len(), 3);
        assert_eq!(commits[0].timestamp, 1234567890);
        assert_eq!(commits[1].timestamp, 1234567891);
        assert_eq!(commits[2].timestamp, 1234567892);
    }

    #[test]
    fn test_parse_empty_input() {
        let parser = CustomParser::new();
        let result = parser.parse_str("");
        assert!(matches!(result, Err(ParseError::EmptyLog)));

        let result = parser.parse_str("# Only comments\n\n");
        assert!(matches!(result, Err(ParseError::EmptyLog)));
    }

    #[test]
    fn test_parse_with_max_commits() {
        let input = "\
            1234567890|John|A|a.txt\n\
            1234567891|John|A|b.txt\n\
            1234567892|John|A|c.txt\n\
            1234567893|John|A|d.txt\n\
            1234567894|John|A|e.txt\n";

        let parser = CustomParser::with_options(ParseOptions::default().with_max_commits(3));
        let commits = parser.parse_str(input).unwrap();

        assert_eq!(commits.len(), 3);
    }

    #[test]
    fn test_parse_with_time_range() {
        let input = "\
            1234567890|John|A|a.txt\n\
            1234567895|John|A|b.txt\n\
            1234567900|John|A|c.txt\n\
            1234567905|John|A|d.txt\n";

        let parser = CustomParser::with_options(
            ParseOptions::default().with_time_range(1234567895, 1234567900),
        );
        let commits = parser.parse_str(input).unwrap();

        assert_eq!(commits.len(), 2);
        assert_eq!(commits[0].timestamp, 1234567895);
        assert_eq!(commits[1].timestamp, 1234567900);
    }

    #[test]
    fn test_parse_lenient_mode() {
        let input = "\
            1234567890|John|A|a.txt\n\
            invalid line here\n\
            1234567891|John|A|b.txt\n";

        // Strict mode (default)
        let parser = CustomParser::new();
        let result = parser.parse_str(input);
        assert!(result.is_err());

        // Lenient mode
        let parser = CustomParser::with_options(ParseOptions::lenient());
        let commits = parser.parse_str(input).unwrap();
        assert_eq!(commits.len(), 2);
    }

    #[test]
    fn test_can_parse() {
        let parser = CustomParser::new();

        // Valid format
        assert!(parser.can_parse("1234567890|John|A|file.txt\n"));
        assert!(parser.can_parse("# Comment\n1234567890|John|A|file.txt\n"));

        // Invalid format
        assert!(!parser.can_parse("not a valid format\n"));
        assert!(!parser.can_parse("commit abc123\n"));
        assert!(!parser.can_parse(""));
    }

    #[test]
    fn test_deterministic_hash() {
        let input = "1234567890|John Doe|A|src/main.rs\n";
        let parser = CustomParser::new();

        let commits1 = parser.parse_str(input).unwrap();
        let commits2 = parser.parse_str(input).unwrap();

        assert_eq!(commits1[0].hash, commits2[0].hash);
    }

    #[test]
    fn test_hash_str() {
        // Same input should produce same hash
        assert_eq!(hash_str("test"), hash_str("test"));

        // Different input should produce different hash
        assert_ne!(hash_str("test1"), hash_str("test2"));
    }

    #[test]
    fn test_is_valid_hex_color() {
        assert!(CustomParser::is_valid_hex_color("FF0000"));
        assert!(CustomParser::is_valid_hex_color("00ff00"));
        assert!(CustomParser::is_valid_hex_color("123abc"));

        assert!(!CustomParser::is_valid_hex_color("FF00")); // Too short
        assert!(!CustomParser::is_valid_hex_color("FF00000")); // Too long
        assert!(!CustomParser::is_valid_hex_color("GGGGGG")); // Invalid hex
        assert!(!CustomParser::is_valid_hex_color("")); // Empty
    }

    #[test]
    fn test_parser_trait() {
        let parser = CustomParser::new();
        assert_eq!(parser.name(), "custom");

        // Test that it implements Parser trait
        fn assert_parser<T: Parser>(_: &T) {}
        assert_parser(&parser);
    }

    #[test]
    fn test_whitespace_handling() {
        // Extra whitespace should be trimmed
        let input = "  1234567890  |  John Doe  |  A  |  src/main.rs  \n";
        let parser = CustomParser::new();
        let commits = parser.parse_str(input).unwrap();

        assert_eq!(commits[0].author, "John Doe");
        assert_eq!(commits[0].files[0].path.to_str().unwrap(), "src/main.rs");
    }
}
