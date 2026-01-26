// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Property-based tests for rource-vcs.
//!
//! These tests verify parser correctness and robustness using proptest
//! to generate random inputs.

use proptest::prelude::*;
use rource_vcs::commit::FileAction;
use rource_vcs::parser::{CustomParser, Parser};

// =============================================================================
// FileAction Property Tests
// =============================================================================

proptest! {
    /// FileAction from_char correctly parses all known action characters.
    #[test]
    fn file_action_known_chars_parse(c in prop::sample::select(vec!['A', 'a', 'M', 'm', 'D', 'd', 'C', 'c', 'R', 'r'])) {
        let action = FileAction::from_char(c);
        prop_assert!(action.is_some(), "Known char '{}' should parse", c);
    }

    /// FileAction from_char returns None for unknown characters.
    #[test]
    fn file_action_unknown_chars_none(c in "[^AaMmDdCcRr]") {
        // Get first char from string
        if let Some(ch) = c.chars().next() {
            let action = FileAction::from_char(ch);
            prop_assert!(action.is_none(), "Unknown char '{}' should return None", ch);
        }
    }

    /// FileAction as_char produces valid action characters.
    #[test]
    fn file_action_as_char_valid(action in prop::sample::select(vec![FileAction::Create, FileAction::Modify, FileAction::Delete])) {
        let c = action.as_char();
        prop_assert!(
            matches!(c, 'A' | 'M' | 'D'),
            "as_char should return A, M, or D, got '{}'",
            c
        );
    }

    /// FileAction round-trip: action -> char -> action preserves the action.
    #[test]
    fn file_action_roundtrip(action in prop::sample::select(vec![FileAction::Create, FileAction::Modify, FileAction::Delete])) {
        let c = action.as_char();
        let recovered = FileAction::from_char(c);

        prop_assert_eq!(
            recovered,
            Some(action),
            "Round-trip failed for {:?}",
            action
        );
    }

    /// FileAction color_rgb returns valid RGB values.
    #[test]
    fn file_action_color_valid(action in prop::sample::select(vec![FileAction::Create, FileAction::Modify, FileAction::Delete])) {
        let (r, g, b) = action.color_rgb();

        // All values should be valid u8 (0-255) - they are by type
        // Check they are the expected colors
        match action {
            FileAction::Create => prop_assert_eq!((r, g, b), (0, 255, 0), "Create should be green"),
            FileAction::Modify => prop_assert_eq!((r, g, b), (255, 128, 0), "Modify should be orange"),
            FileAction::Delete => prop_assert_eq!((r, g, b), (255, 0, 0), "Delete should be red"),
        }
    }
}

// =============================================================================
// Custom Parser Property Tests
// =============================================================================

/// Strategy for generating valid timestamps.
fn valid_timestamp() -> impl Strategy<Value = i64> {
    // Unix timestamps from year 2000 to 2100
    946684800i64..4102444800i64
}

/// Strategy for generating valid usernames (non-empty, no pipes).
fn valid_username() -> impl Strategy<Value = String> {
    // Generate non-empty strings without pipe characters
    "[a-zA-Z0-9_ ]{1,50}"
        .prop_map(|s| s.trim().to_string())
        .prop_filter("non-empty username", |s| !s.is_empty())
}

/// Strategy for generating valid file paths (non-empty, no pipes).
fn valid_filepath() -> impl Strategy<Value = String> {
    // Generate paths like src/main.rs, lib/utils/helper.py
    "[a-zA-Z0-9_/.-]{1,100}"
        .prop_map(|s| s.trim().to_string())
        .prop_filter("non-empty path", |s| !s.is_empty())
}

/// Strategy for generating valid action characters.
fn valid_action_char() -> impl Strategy<Value = char> {
    prop::sample::select(vec!['A', 'M', 'D'])
}

proptest! {
    /// Valid custom log lines should parse successfully.
    #[test]
    fn custom_parser_valid_lines(
        timestamp in valid_timestamp(),
        username in valid_username(),
        action in valid_action_char(),
        filepath in valid_filepath()
    ) {
        let line = format!("{}|{}|{}|{}", timestamp, username, action, filepath);
        let parser = CustomParser::new();

        let result = parser.parse_str(&line);

        prop_assert!(
            result.is_ok(),
            "Valid line should parse: '{}' -> {:?}",
            line,
            result
        );

        if let Ok(commits) = result {
            prop_assert_eq!(commits.len(), 1, "Should produce one commit");

            let commit = &commits[0];
            prop_assert_eq!(commit.timestamp, timestamp, "Timestamp should match");
            prop_assert_eq!(&commit.author, &username, "Author should match");
            prop_assert_eq!(commit.files.len(), 1, "Should have one file");
            prop_assert_eq!(
                commit.files[0].path.to_string_lossy(),
                filepath,
                "Path should match"
            );
        }
    }

    /// Multiple lines with same timestamp and author should be grouped.
    #[test]
    fn custom_parser_groups_commits(
        timestamp in valid_timestamp(),
        username in valid_username(),
        filepath1 in valid_filepath(),
        filepath2 in valid_filepath()
    ) {
        // Ensure different paths
        prop_assume!(filepath1 != filepath2);

        let log = format!(
            "{}|{}|A|{}\n{}|{}|M|{}",
            timestamp, username, filepath1,
            timestamp, username, filepath2
        );
        let parser = CustomParser::new();

        let result = parser.parse_str(&log);

        prop_assert!(result.is_ok(), "Valid log should parse");

        if let Ok(commits) = result {
            prop_assert_eq!(
                commits.len(),
                1,
                "Same timestamp+author should produce one commit"
            );
            prop_assert_eq!(
                commits[0].files.len(),
                2,
                "Should have two files in commit"
            );
        }
    }

    /// Empty lines should be skipped without error.
    #[test]
    fn custom_parser_skips_empty_lines(
        timestamp in valid_timestamp(),
        username in valid_username(),
        filepath in valid_filepath()
    ) {
        let log = format!(
            "\n{}|{}|A|{}\n\n\n",
            timestamp, username, filepath
        );
        let parser = CustomParser::new();

        let result = parser.parse_str(&log);

        prop_assert!(result.is_ok(), "Log with empty lines should parse");

        if let Ok(commits) = result {
            prop_assert_eq!(commits.len(), 1, "Should produce one commit");
        }
    }

    /// Comment lines (starting with #) should be skipped.
    #[test]
    fn custom_parser_skips_comments(
        timestamp in valid_timestamp(),
        username in valid_username(),
        filepath in valid_filepath(),
        comment in "[a-zA-Z0-9 ]{1,50}"
    ) {
        let log = format!(
            "# {}\n{}|{}|A|{}",
            comment, timestamp, username, filepath
        );
        let parser = CustomParser::new();

        let result = parser.parse_str(&log);

        prop_assert!(result.is_ok(), "Log with comments should parse");

        if let Ok(commits) = result {
            prop_assert_eq!(commits.len(), 1, "Should produce one commit (comment skipped)");
        }
    }

    /// Parser should never panic on arbitrary input.
    #[test]
    fn custom_parser_no_panic(data in ".*") {
        let parser = CustomParser::new();

        // This should not panic, regardless of input
        let _ = parser.parse_str(&data);
    }

    /// Parser should handle very long lines gracefully.
    #[test]
    fn custom_parser_long_lines(
        timestamp in valid_timestamp(),
        username in valid_username(),
        repeat in 1usize..100
    ) {
        // Create a very long path
        let long_path = "a/".repeat(repeat) + "file.txt";
        let line = format!("{}|{}|A|{}", timestamp, username, long_path);

        let parser = CustomParser::new();
        let result = parser.parse_str(&line);

        prop_assert!(result.is_ok(), "Long lines should parse");
    }
}

// =============================================================================
// Robustness Tests
// =============================================================================

proptest! {
    /// Parser handles unicode gracefully.
    #[test]
    fn custom_parser_unicode_username(
        timestamp in valid_timestamp(),
        filepath in valid_filepath()
    ) {
        // Various unicode usernames
        let unicode_names = vec![
            "山田太郎",
            "Müller",
            "Søren",
            "Иван",
            "محمد",
        ];

        for name in unicode_names {
            let line = format!("{}|{}|A|{}", timestamp, name, filepath);
            let parser = CustomParser::new();
            let result = parser.parse_str(&line);

            prop_assert!(result.is_ok(), "Unicode username '{}' should parse", name);
        }
    }

    /// Parser handles special path characters.
    #[test]
    fn custom_parser_special_paths(timestamp in valid_timestamp()) {
        let special_paths = vec![
            "src/file with spaces.rs",
            "path/to/file-with-dashes.txt",
            "path/to/file_with_underscores.py",
            "path.to.dotted/file.name.ext",
            "CamelCase/Path/File.java",
        ];

        for path in special_paths {
            let line = format!("{}|TestUser|A|{}", timestamp, path);
            let parser = CustomParser::new();
            let result = parser.parse_str(&line);

            prop_assert!(result.is_ok(), "Special path '{}' should parse", path);
        }
    }
}

// =============================================================================
// Determinism Tests
// =============================================================================

proptest! {
    /// Same input should always produce same output.
    #[test]
    fn custom_parser_deterministic(
        timestamp in valid_timestamp(),
        username in valid_username(),
        filepath in valid_filepath()
    ) {
        let line = format!("{}|{}|A|{}", timestamp, username, filepath);
        let parser = CustomParser::new();

        let result1 = parser.parse_str(&line);
        let result2 = parser.parse_str(&line);

        prop_assert_eq!(
            result1.is_ok(),
            result2.is_ok(),
            "Parse success should be deterministic"
        );

        if let (Ok(commits1), Ok(commits2)) = (result1, result2) {
            prop_assert_eq!(commits1.len(), commits2.len(), "Commit count should match");

            for (c1, c2) in commits1.iter().zip(commits2.iter()) {
                prop_assert_eq!(c1.timestamp, c2.timestamp, "Timestamps should match");
                prop_assert_eq!(&c1.author, &c2.author, "Authors should match");
                prop_assert_eq!(c1.files.len(), c2.files.len(), "File counts should match");
            }
        }
    }
}
