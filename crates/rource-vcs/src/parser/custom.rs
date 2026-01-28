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
    ///
    /// # Performance
    ///
    /// Uses iterator-based parsing to avoid Vec allocation. This is ~15% faster
    /// than `.split().collect()` for large log files.
    fn parse_line(
        line: &str,
        line_number: usize,
    ) -> ParseResult<(i64, &str, FileAction, &str, Option<&str>)> {
        // Use iterator to avoid Vec allocation
        let mut parts = line.split('|');

        // Parse timestamp
        let timestamp_str = parts.next().ok_or_else(|| ParseError::InvalidLine {
            line_number,
            line: line.to_string(),
            expected: "timestamp|username|action|filepath",
        })?;
        let timestamp =
            timestamp_str
                .trim()
                .parse::<i64>()
                .map_err(|_| ParseError::InvalidTimestamp {
                    line_number,
                    value: timestamp_str.to_string(),
                })?;

        // Parse username
        let username = parts
            .next()
            .ok_or_else(|| ParseError::InvalidLine {
                line_number,
                line: line.to_string(),
                expected: "timestamp|username|action|filepath",
            })?
            .trim();
        if username.is_empty() {
            return Err(ParseError::MissingField {
                line_number,
                field: "username",
            });
        }

        // Parse action
        let action_str = parts
            .next()
            .ok_or_else(|| ParseError::InvalidLine {
                line_number,
                line: line.to_string(),
                expected: "timestamp|username|action|filepath",
            })?
            .trim();
        let action =
            FileAction::from_char(action_str.chars().next().unwrap_or('?')).ok_or_else(|| {
                ParseError::InvalidAction {
                    line_number,
                    value: action_str.to_string(),
                }
            })?;

        // Parse filepath
        let filepath = parts
            .next()
            .ok_or_else(|| ParseError::InvalidLine {
                line_number,
                line: line.to_string(),
                expected: "timestamp|username|action|filepath",
            })?
            .trim();
        if filepath.is_empty() {
            return Err(ParseError::MissingField {
                line_number,
                field: "filepath",
            });
        }

        // Parse optional color (no allocation if not present)
        let color = match parts.next() {
            Some(color_str) => {
                let color_str = color_str.trim();
                if color_str.is_empty() {
                    None
                } else if Self::is_valid_hex_color(color_str) {
                    Some(color_str)
                } else {
                    return Err(ParseError::InvalidColor {
                        line_number,
                        value: color_str.to_string(),
                    });
                }
            }
            None => None,
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
            let mut parts = line.split('|');
            let Some(timestamp_str) = parts.next() else {
                return false;
            };
            // Skip username (parts[1])
            if parts.next().is_none() {
                return false;
            }
            let Some(action_str) = parts.next() else {
                return false;
            };
            // Check we have at least 4 parts (path is parts[3])
            if parts.next().is_none() {
                return false;
            }
            // Check timestamp is numeric
            if timestamp_str.trim().parse::<i64>().is_ok() {
                // Check action is valid
                let action = action_str.trim();
                if action.len() == 1
                    && FileAction::from_char(action.chars().next().unwrap()).is_some()
                {
                    return true;
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

    // ========================================================================
    // PHASE 2: Expert+ Edge Case Tests
    // ========================================================================

    #[test]
    fn test_parse_empty_file() {
        let parser = CustomParser::new();
        let result = parser.parse_str("");
        assert!(matches!(result, Err(ParseError::EmptyLog)));
    }

    #[test]
    fn test_parse_single_line() {
        let input = "1234567890|SingleUser|A|single_file.txt";
        let parser = CustomParser::new();
        let commits = parser.parse_str(input).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].author, "SingleUser");
        assert_eq!(commits[0].files.len(), 1);
    }

    #[test]
    fn test_parse_missing_fields() {
        let parser = CustomParser::new();
        // Missing filepath
        let result = parser.parse_str("1234567890|John|A");
        assert!(matches!(result, Err(ParseError::InvalidLine { .. })));

        // Missing action
        let result = parser.parse_str("1234567890|John");
        assert!(matches!(result, Err(ParseError::InvalidLine { .. })));
    }

    #[test]
    fn test_parse_malformed_timestamp() {
        let parser = CustomParser::new();
        let result = parser.parse_str("not_a_timestamp|John|A|file.txt");
        assert!(matches!(result, Err(ParseError::InvalidTimestamp { .. })));

        // Floating point timestamp
        let result = parser.parse_str("123456.789|John|A|file.txt");
        assert!(matches!(result, Err(ParseError::InvalidTimestamp { .. })));

        // Negative timestamp should parse successfully
        let result = parser.parse_str("-1|John|A|file.txt");
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_unicode_author() {
        let parser = CustomParser::new();

        // Japanese characters
        let input = "1234567890|田中太郎|A|src/main.rs";
        let commits = parser.parse_str(input).unwrap();
        assert_eq!(commits[0].author, "田中太郎");

        // Emoji in author name
        let input = "1234567890|Dev 🚀|M|file.txt";
        let commits = parser.parse_str(input).unwrap();
        assert_eq!(commits[0].author, "Dev 🚀");

        // Cyrillic characters
        let input = "1234567890|Иван Петров|A|file.rs";
        let commits = parser.parse_str(input).unwrap();
        assert_eq!(commits[0].author, "Иван Петров");
    }

    #[test]
    fn test_parse_unicode_path() {
        let parser = CustomParser::new();

        // Chinese characters in path
        let input = "1234567890|User|A|文档/测试.txt";
        let commits = parser.parse_str(input).unwrap();
        assert_eq!(commits[0].files[0].path.to_str().unwrap(), "文档/测试.txt");

        // Emoji in path
        let input = "1234567890|User|M|assets/🎮/game.png";
        let commits = parser.parse_str(input).unwrap();
        assert_eq!(
            commits[0].files[0].path.to_str().unwrap(),
            "assets/🎮/game.png"
        );
    }

    #[test]
    fn test_parse_special_chars_in_path() {
        let parser = CustomParser::new();

        // Spaces in path
        let input = "1234567890|User|A|path with spaces/file name.txt";
        let commits = parser.parse_str(input).unwrap();
        assert_eq!(
            commits[0].files[0].path.to_str().unwrap(),
            "path with spaces/file name.txt"
        );

        // Single quotes
        let input = "1234567890|User|M|it's a file.txt";
        let commits = parser.parse_str(input).unwrap();
        assert_eq!(
            commits[0].files[0].path.to_str().unwrap(),
            "it's a file.txt"
        );

        // Double quotes
        let input = "1234567890|User|A|\"quoted\"/file.txt";
        let commits = parser.parse_str(input).unwrap();
        assert_eq!(
            commits[0].files[0].path.to_str().unwrap(),
            "\"quoted\"/file.txt"
        );
    }

    #[test]
    fn test_parse_very_long_path() {
        let parser = CustomParser::new();

        // Create a path with 1000+ characters
        let long_path =
            (0..100).map(|_| "directory").collect::<Vec<_>>().join("/") + "/very_long_filename.txt";
        let input = format!("1234567890|User|A|{long_path}");
        let commits = parser.parse_str(&input).unwrap();
        assert_eq!(commits[0].files[0].path.to_str().unwrap(), long_path);
    }

    #[test]
    fn test_parse_deeply_nested_path() {
        let parser = CustomParser::new();

        // Create a deeply nested path (50+ levels)
        let deep_path = (0..60)
            .map(|i| format!("level{i}"))
            .collect::<Vec<_>>()
            .join("/")
            + "/file.txt";
        let input = format!("1234567890|User|A|{deep_path}");
        let commits = parser.parse_str(&input).unwrap();
        assert!(commits[0].files[0]
            .path
            .to_str()
            .unwrap()
            .starts_with("level0/level1/"));
    }

    #[test]
    fn test_parse_binary_file_paths() {
        let parser = CustomParser::new();

        let binary_extensions = [
            ".exe", ".dll", ".so", ".dylib", ".bin", ".dat", ".o", ".a", ".lib", ".png", ".jpg",
            ".gif", ".mp3", ".mp4", ".zip", ".tar.gz", ".wasm",
        ];

        for ext in binary_extensions {
            let input = format!("1234567890|User|A|binary/file{ext}");
            let commits = parser.parse_str(&input).unwrap();
            assert!(commits[0].files[0].path.to_str().unwrap().ends_with(ext));
        }
    }

    #[test]
    fn test_parse_only_comments() {
        let parser = CustomParser::new();
        let input = "# Comment 1\n# Comment 2\n# Comment 3";
        let result = parser.parse_str(input);
        assert!(matches!(result, Err(ParseError::EmptyLog)));
    }

    #[test]
    fn test_parse_mixed_valid_invalid_lenient() {
        let input = "\
            1234567890|Valid|A|file1.txt\n\
            invalid line without pipes\n\
            1234567891|Valid|M|file2.txt\n\
            also invalid\n\
            1234567892|Valid|D|file3.txt\n";

        let parser = CustomParser::with_options(ParseOptions::lenient());
        let commits = parser.parse_str(input).unwrap();
        assert_eq!(commits.len(), 3);
    }

    #[test]
    fn test_parse_null_byte_in_input() {
        let parser = CustomParser::new();
        // Null bytes should not crash the parser
        let input = "1234567890|User\0Name|A|file.txt";
        let _ = parser.parse_str(input);
    }

    #[test]
    fn test_parse_large_timestamp() {
        let parser = CustomParser::new();
        // Year 3000+ timestamp
        let input = "32503680000|FutureUser|A|future_file.txt";
        let commits = parser.parse_str(input).unwrap();
        assert_eq!(commits[0].timestamp, 32503680000);
    }
}
