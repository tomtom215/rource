// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Git log format parser.
//!
//! This parser handles output from `git log` with the following format:
//!
//! ```text
//! git log --pretty=format:"commit %H%nAuthor: %an <%ae>%nDate: %at%n" --name-status
//! ```
//!
//! Which produces:
//!
//! ```text
//! commit abc123def456...
//! Author: John Doe <john@example.com>
//! Date: 1234567890
//!
//! A       src/new_file.rs
//! M       src/existing.rs
//! D       old/removed.txt
//! ```
//!
//! The parser is flexible and handles various git log output formats.

use crate::commit::{Commit, FileAction, FileChange};
use crate::error::{ParseError, ParseResult};
use crate::parser::{ParseOptions, Parser};

/// Parser for git log output.
///
/// This parser handles the standard `git log --name-status` format
/// as well as variations in formatting.
#[derive(Debug, Clone)]
pub struct GitParser {
    options: ParseOptions,
}

/// Checks if a character is a valid git file status action character.
fn is_git_action_char(c: char) -> bool {
    matches!(
        c,
        'A' | 'a' | 'M' | 'm' | 'D' | 'd' | 'R' | 'r' | 'C' | 'c' | 'T' | 't' | 'U' | 'u'
    )
}

impl GitParser {
    /// Creates a new Git parser with default options.
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

    /// Parses a file status line (e.g., "M\tsrc/file.rs").
    ///
    /// Git file status lines have the format:
    /// - Tab-separated: "M\tpath/to/file" (most common)
    /// - Space-separated: "M  path/to/file" (requires 2+ spaces to avoid matching commit messages)
    ///
    /// We require a tab OR at least 2 spaces to distinguish from commit message lines
    /// like "Add new feature" which would otherwise match as "A" action + "dd new feature" path.
    fn parse_file_status(line: &str, line_number: usize) -> ParseResult<Option<FileChange>> {
        let line = line.trim();
        if line.is_empty() {
            return Ok(None);
        }

        // Handle tab-separated format: "M\tpath" (the standard git format)
        let (action_str, path) = if let Some(idx) = line.find('\t') {
            (&line[..idx], line[idx + 1..].trim())
        } else {
            // For space-separated format, we need to be more careful to avoid
            // matching commit message lines like "Add feature" as file status lines.
            // Git --name-status uses tabs, so space-separated is rare.
            // We only accept it if:
            // 1. First char is a valid action letter
            // 2. Second char is a space (not part of a word)
            // 3. Path follows

            // Must be at least "A f" (action + space + at least 1 char for path)
            if line.len() < 3 {
                return Ok(None);
            }

            let bytes = line.as_bytes();
            let first_char = bytes[0] as char;
            let second_char = bytes[1] as char;

            // Check if first char is a valid git action and second is whitespace
            if !is_git_action_char(first_char) || !second_char.is_whitespace() {
                return Ok(None);
            }

            // For rename/copy format like "R100 old -> new", action can have digits
            let action_end = line[1..]
                .find(|c: char| !c.is_ascii_digit())
                .map_or(1, |i| i + 1);

            let action = &line[..action_end];
            let path = line[action_end..].trim_start();

            if path.is_empty() {
                return Ok(None);
            }

            (action, path)
        };

        // Parse the action
        let action_char = action_str.chars().next().unwrap_or('?');

        // Git uses these status codes:
        // A = Added
        // M = Modified
        // D = Deleted
        // R = Renamed (we treat as modify)
        // C = Copied (we treat as add)
        // T = Type changed (we treat as modify)
        // U = Unmerged (we treat as modify)
        let action = match action_char {
            'A' | 'a' | 'C' | 'c' => FileAction::Create,
            'M' | 'm' | 'R' | 'r' | 'T' | 't' | 'U' | 'u' => FileAction::Modify,
            'D' | 'd' => FileAction::Delete,
            _ => {
                // Unknown action, skip this line
                return Ok(None);
            }
        };

        // For rename/copy, the path format is "old -> new" or "old\tnew"
        // We take the new path. Using if-let chain for readability (not map_or_else).
        #[allow(clippy::option_if_let_else)]
        let path = if let Some(arrow_idx) = path.find(" -> ") {
            path[arrow_idx + 4..].trim()
        } else if let Some(tab_idx) = path.find('\t') {
            // Second tab in rename format
            path[tab_idx + 1..].trim()
        } else {
            path
        };

        if path.is_empty() {
            return Err(ParseError::MissingField {
                line_number,
                field: "filepath",
            });
        }

        Ok(Some(FileChange::new(path, action)))
    }

    /// Extracts email from "Author: Name <email>" format.
    fn parse_author_line(line: &str) -> (String, Option<String>) {
        // Format: "Author: Name <email>" or just "Name <email>"
        let line = line
            .strip_prefix("Author:")
            .or_else(|| line.strip_prefix("author:"))
            .map_or(line, str::trim);

        // Look for email in angle brackets
        // The email must be properly formatted: <email> with < before >
        if let Some(email_start) = line.rfind('<') {
            if let Some(email_end) = line.rfind('>') {
                // Ensure > comes after < (not malformed like "><" or "<<><<<<<")
                if email_end > email_start {
                    let name = line[..email_start].trim().to_string();
                    let email = line[email_start + 1..email_end].to_string();
                    return (name, Some(email));
                }
            }
        }

        (line.trim().to_string(), None)
    }

    /// Parses a Unix timestamp from a date line.
    fn parse_date_line(line: &str, line_number: usize) -> ParseResult<i64> {
        // Format: "Date: 1234567890" or just a number
        let line = line
            .strip_prefix("Date:")
            .or_else(|| line.strip_prefix("date:"))
            .map_or(line, str::trim)
            .trim();

        line.parse::<i64>()
            .map_err(|_| ParseError::InvalidTimestamp {
                line_number,
                value: line.to_string(),
            })
    }
}

impl Default for GitParser {
    fn default() -> Self {
        Self::new()
    }
}

/// Parser state machine states.
#[derive(Debug, PartialEq)]
enum ParserState {
    /// Looking for a commit line
    ExpectingCommit,
    /// Expecting author line after commit
    ExpectingAuthor,
    /// Expecting date line after author
    ExpectingDate,
    /// Reading file changes until next commit or EOF
    ReadingFiles,
}

impl Parser for GitParser {
    fn name(&self) -> &'static str {
        "git"
    }

    fn parse_str(&self, input: &str) -> ParseResult<Vec<Commit>> {
        let mut commits = Vec::new();
        let mut state = ParserState::ExpectingCommit;

        let mut current_hash = String::new();
        let mut current_author = String::new();
        let mut current_email: Option<String> = None;
        let mut current_timestamp: i64 = 0;
        let mut current_files: Vec<FileChange> = Vec::new();

        let mut line_number = 0;

        for line in input.lines() {
            line_number += 1;
            let line = line.trim();

            // Skip empty lines in certain states
            if line.is_empty() {
                if state == ParserState::ReadingFiles {
                    // Empty line might separate commits, continue reading
                    continue;
                }
                continue;
            }

            match state {
                ParserState::ExpectingCommit => {
                    if line.starts_with("commit ") || line.starts_with("Commit ") {
                        current_hash = line[7..].trim().to_string();
                        state = ParserState::ExpectingAuthor;
                    }
                    // Otherwise skip lines until we see a commit
                }

                ParserState::ExpectingAuthor => {
                    if line.starts_with("Author:") || line.starts_with("author:") {
                        let (author, email) = Self::parse_author_line(line);
                        current_author = author;
                        current_email = email;
                        state = ParserState::ExpectingDate;
                    } else if let Some(hash) = line.strip_prefix("commit ") {
                        // New commit without author? Reset
                        current_hash = hash.trim().to_string();
                    }
                    // Skip other lines (like Merge: lines)
                }

                ParserState::ExpectingDate => {
                    if line.starts_with("Date:") || line.starts_with("date:") {
                        current_timestamp = Self::parse_date_line(line, line_number)?;
                        state = ParserState::ReadingFiles;
                    } else if let Some(hash) = line.strip_prefix("commit ") {
                        // New commit without date? Reset
                        current_hash = hash.trim().to_string();
                        state = ParserState::ExpectingAuthor;
                    }
                    // Skip other lines
                }

                ParserState::ReadingFiles => {
                    if line.starts_with("commit ") || line.starts_with("Commit ") {
                        // Save current commit if it has files
                        if !current_files.is_empty() || !self.options.skip_empty_commits {
                            if self.options.timestamp_in_range(current_timestamp) {
                                let mut commit = Commit::new(
                                    current_hash.clone(),
                                    current_timestamp,
                                    current_author.clone(),
                                );
                                if let Some(ref email) = current_email {
                                    commit = commit.with_email(email.clone());
                                }
                                // Use drain to reuse Vec capacity for next commit
                                #[allow(clippy::iter_with_drain)]
                                let files = current_files.drain(..);
                                commit = commit.with_files(files);
                                commits.push(commit);

                                if self.options.limit_reached(commits.len()) {
                                    return Ok(commits);
                                }
                            } else {
                                current_files.clear();
                            }
                        }

                        // Start new commit
                        current_hash = line[7..].trim().to_string();
                        current_files.clear();
                        state = ParserState::ExpectingAuthor;
                    } else if let Some(file_change) = Self::parse_file_status(line, line_number)? {
                        current_files.push(file_change);
                    }
                    // Skip commit message lines and other content
                }
            }
        }

        // Don't forget the last commit
        if state == ParserState::ReadingFiles
            && (!current_files.is_empty() || !self.options.skip_empty_commits)
            && self.options.timestamp_in_range(current_timestamp)
        {
            let mut commit = Commit::new(current_hash, current_timestamp, current_author);
            if let Some(email) = current_email {
                commit = commit.with_email(email);
            }
            commit = commit.with_files(current_files);
            commits.push(commit);
        }

        if commits.is_empty() {
            return Err(ParseError::EmptyLog);
        }

        // Sort by timestamp
        commits.sort_by_key(|c| c.timestamp);

        Ok(commits)
    }

    fn can_parse(&self, input: &str) -> bool {
        // Look for git log signature in first few lines
        for line in input.lines().take(20) {
            let line = line.trim();
            if line.starts_with("commit ") && line.len() > 10 {
                // Check if it looks like a git hash (40 hex chars, or short hash 7+)
                let hash_part = &line[7..];
                if hash_part.len() >= 7 && hash_part.chars().all(|c| c.is_ascii_hexdigit()) {
                    return true;
                }
            }
        }
        false
    }
}

#[cfg(test)]
#[allow(clippy::unreadable_literal)]
mod tests {
    use super::*;

    const SAMPLE_GIT_LOG: &str = "\
commit abc123def456789012345678901234567890abcd
Author: John Doe <john@example.com>
Date: 1234567890

    Initial commit

A\tsrc/main.rs
A\tCargo.toml

commit def456789012345678901234567890abcdef12
Author: Jane Smith <jane@example.com>
Date: 1234567900

    Add library

A\tsrc/lib.rs
M\tsrc/main.rs
";

    #[test]
    fn test_parse_git_log() {
        let parser = GitParser::new();
        let commits = parser.parse_str(SAMPLE_GIT_LOG).unwrap();

        assert_eq!(commits.len(), 2);

        // First commit (sorted by timestamp)
        assert_eq!(commits[0].hash, "abc123def456789012345678901234567890abcd");
        assert_eq!(commits[0].author, "John Doe");
        assert_eq!(commits[0].email, Some("john@example.com".to_string()));
        assert_eq!(commits[0].timestamp, 1234567890);
        assert_eq!(commits[0].files.len(), 2);

        // Second commit
        assert_eq!(commits[1].hash, "def456789012345678901234567890abcdef12");
        assert_eq!(commits[1].author, "Jane Smith");
        assert_eq!(commits[1].timestamp, 1234567900);
        assert_eq!(commits[1].files.len(), 2);
    }

    #[test]
    fn test_parse_file_status() {
        // Tab-separated
        let change = GitParser::parse_file_status("M\tsrc/file.rs", 1)
            .unwrap()
            .unwrap();
        assert_eq!(change.action, FileAction::Modify);
        assert_eq!(change.path.to_str().unwrap(), "src/file.rs");

        // Space-separated
        let change = GitParser::parse_file_status("A src/new.rs", 1)
            .unwrap()
            .unwrap();
        assert_eq!(change.action, FileAction::Create);

        // Delete
        let change = GitParser::parse_file_status("D\told/removed.txt", 1)
            .unwrap()
            .unwrap();
        assert_eq!(change.action, FileAction::Delete);
    }

    #[test]
    fn test_parse_file_status_rename() {
        // Rename format: R100\told.txt -> new.txt
        let change = GitParser::parse_file_status("R100\told.txt -> new.txt", 1)
            .unwrap()
            .unwrap();
        assert_eq!(change.action, FileAction::Modify);
        assert_eq!(change.path.to_str().unwrap(), "new.txt");
    }

    #[test]
    fn test_parse_file_status_empty() {
        assert!(GitParser::parse_file_status("", 1).unwrap().is_none());
        assert!(GitParser::parse_file_status("   ", 1).unwrap().is_none());
    }

    #[test]
    fn test_parse_author_line() {
        let (name, email) = GitParser::parse_author_line("Author: John Doe <john@example.com>");
        assert_eq!(name, "John Doe");
        assert_eq!(email, Some("john@example.com".to_string()));

        let (name, email) = GitParser::parse_author_line("John Doe <john@example.com>");
        assert_eq!(name, "John Doe");
        assert_eq!(email, Some("john@example.com".to_string()));

        let (name, email) = GitParser::parse_author_line("John Doe");
        assert_eq!(name, "John Doe");
        assert!(email.is_none());
    }

    #[test]
    fn test_parse_date_line() {
        assert_eq!(
            GitParser::parse_date_line("Date: 1234567890", 1).unwrap(),
            1234567890
        );
        assert_eq!(
            GitParser::parse_date_line("date:   1234567890  ", 1).unwrap(),
            1234567890
        );
        assert_eq!(
            GitParser::parse_date_line("1234567890", 1).unwrap(),
            1234567890
        );

        assert!(GitParser::parse_date_line("Date: not a number", 1).is_err());
    }

    #[test]
    fn test_all_git_actions() {
        let log = "\
commit abc123def456789012345678901234567890abcd
Author: Test <test@test.com>
Date: 1000

A\tadded.txt
M\tmodified.txt
D\tdeleted.txt
R100\told.txt\tnew.txt
C\tcopied.txt
T\ttype_changed.txt
";

        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();

        assert_eq!(commits[0].files.len(), 6);
    }

    #[test]
    fn test_empty_commit() {
        let log = "\
commit abc123def456789012345678901234567890abcd
Author: Test <test@test.com>
Date: 1000

    Empty commit message

commit def456789012345678901234567890abcdef12
Author: Test <test@test.com>
Date: 1001

A\tfile.txt
";

        // Default: skip empty commits
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);

        // Include empty commits
        let parser = GitParser::with_options(ParseOptions {
            skip_empty_commits: false,
            ..Default::default()
        });
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 2);
    }

    #[test]
    fn test_can_parse() {
        let parser = GitParser::new();

        assert!(parser.can_parse(SAMPLE_GIT_LOG));
        assert!(parser.can_parse("commit abc1234\nAuthor: Test\n"));

        assert!(!parser.can_parse("1234567890|John|A|file.txt"));
        assert!(!parser.can_parse("not a git log"));
        assert!(!parser.can_parse("commit xyz")); // Too short, not hex
    }

    #[test]
    fn test_parser_name() {
        let parser = GitParser::new();
        assert_eq!(parser.name(), "git");
    }

    #[test]
    fn test_max_commits() {
        let log = "\
commit aaa1234567890123456789012345678901234567
Author: Test <test@test.com>
Date: 1000
A\ta.txt

commit bbb1234567890123456789012345678901234567
Author: Test <test@test.com>
Date: 1001
A\tb.txt

commit ccc1234567890123456789012345678901234567
Author: Test <test@test.com>
Date: 1002
A\tc.txt
";

        let parser = GitParser::with_options(ParseOptions::default().with_max_commits(2));
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 2);
    }

    #[test]
    fn test_time_range() {
        let log = "\
commit aaa1234567890123456789012345678901234567
Author: Test <test@test.com>
Date: 1000
A\ta.txt

commit bbb1234567890123456789012345678901234567
Author: Test <test@test.com>
Date: 2000
A\tb.txt

commit ccc1234567890123456789012345678901234567
Author: Test <test@test.com>
Date: 3000
A\tc.txt
";

        let parser = GitParser::with_options(ParseOptions::default().with_time_range(1500, 2500));
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].timestamp, 2000);
    }

    #[test]
    fn test_sorted_by_timestamp() {
        let log = "\
commit ccc1234567890123456789012345678901234567
Author: Test <test@test.com>
Date: 3000
A\tc.txt

commit aaa1234567890123456789012345678901234567
Author: Test <test@test.com>
Date: 1000
A\ta.txt

commit bbb1234567890123456789012345678901234567
Author: Test <test@test.com>
Date: 2000
A\tb.txt
";

        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();

        assert_eq!(commits[0].timestamp, 1000);
        assert_eq!(commits[1].timestamp, 2000);
        assert_eq!(commits[2].timestamp, 3000);
    }

    #[test]
    fn test_merge_commit_handling() {
        // Merge commits have an extra "Merge:" line
        let log = "\
commit abc1234567890123456789012345678901234567
Merge: abc123 def456
Author: Test <test@test.com>
Date: 1000

    Merge branch 'feature'

M\tmerged.txt
";

        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].files.len(), 1);
    }

    #[test]
    fn test_empty_log() {
        let parser = GitParser::new();
        assert!(matches!(parser.parse_str(""), Err(ParseError::EmptyLog)));
        assert!(matches!(
            parser.parse_str("some random text"),
            Err(ParseError::EmptyLog)
        ));
    }

    #[test]
    fn test_short_hash() {
        // Short hash format (7 chars)
        let log = "\
commit abc1234
Author: Test <test@test.com>
Date: 1000
A\tfile.txt
";
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits[0].hash, "abc1234");
    }

    // Regression tests for fuzzer-discovered issues

    #[test]
    fn test_malformed_author_with_reversed_brackets() {
        // Fuzzer crash input contained: author:<<><<<<<
        // This caused panic when > appears before < in rfind
        let log = "\
commit abc1234567890123456789012345678901234567
Author: test:<<><<<<<\"
Date: 1000
A\tfile.txt
";
        let parser = GitParser::new();
        // Should not panic, just parse without email
        let result = parser.parse_str(log);
        // This is valid (has files) so should succeed
        assert!(result.is_ok());
    }

    #[test]
    fn test_malformed_author_angle_brackets() {
        // Various malformed angle bracket patterns
        let (name, email) = GitParser::parse_author_line("Author: test><");
        assert_eq!(name, "test><");
        assert!(email.is_none());

        let (name, email) = GitParser::parse_author_line("Author: <<><<<");
        assert_eq!(name, "<<><<<");
        assert!(email.is_none());

        let (name, email) = GitParser::parse_author_line("Author: >");
        assert_eq!(name, ">");
        assert!(email.is_none());
    }

    #[test]
    fn test_input_with_null_bytes() {
        // Parser should handle null bytes gracefully
        let parser = GitParser::new();
        let input = "commit abc1234\nAuthor: test\0\0\0\nDate: 1000\nA\tfile.txt\n";
        // Should not panic
        let _ = parser.parse_str(input);
    }

    #[test]
    fn test_input_with_carriage_returns() {
        // Parser should handle carriage returns
        let parser = GitParser::new();
        let input = "commit abc1234\r\nAuthor: test\r\nDate: 1000\r\nA\tfile.txt\r\n";
        let result = parser.parse_str(input);
        assert!(result.is_ok());
    }

    // ========================================================================
    // PHASE 2: Expert+ Edge Case Tests
    // ========================================================================

    #[test]
    fn test_git_parse_merge_commit() {
        // Merge commit with multiple parents
        let log = "\
commit abc1234567890123456789012345678901234567
Merge: aaa1234 bbb5678
Author: Merger <merger@test.com>
Date: 1000

    Merge branch 'feature'

M\tmerged_file.rs
";
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].author, "Merger");
    }

    #[test]
    fn test_git_parse_octopus_merge() {
        // Octopus merge with 3+ parents
        let log = "\
commit abc1234567890123456789012345678901234567
Merge: aaa1234 bbb5678 ccc9012 ddd3456
Author: Octopus <octopus@test.com>
Date: 1000

    Octopus merge of multiple branches

M\toctopus.rs
";
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].author, "Octopus");
    }

    #[test]
    fn test_git_parse_empty_commit() {
        // Commit with no files
        let log = "\
commit abc1234567890123456789012345678901234567
Author: Empty <empty@test.com>
Date: 1000

    Empty commit message

commit def1234567890123456789012345678901234567
Author: NotEmpty <notempty@test.com>
Date: 1001

A\tfile.txt
";
        // Default skips empty commits
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].author, "NotEmpty");
    }

    #[test]
    fn test_git_parse_rename() {
        // File rename with similarity percentage
        let log = "\
commit abc1234567890123456789012345678901234567
Author: Renamer <renamer@test.com>
Date: 1000

    Rename file

R100\told/path.rs\tnew/path.rs
R095\tsrc/old.rs\tsrc/new.rs
";
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].files.len(), 2);
        assert_eq!(commits[0].files[0].action, FileAction::Modify);
        assert_eq!(commits[0].files[0].path.to_str().unwrap(), "new/path.rs");
    }

    #[test]
    fn test_git_parse_mode_change() {
        // File mode change
        let log = "\
commit abc1234567890123456789012345678901234567
Author: ModeChanger <mode@test.com>
Date: 1000

    Make script executable

T\tscript.sh
";
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].files[0].action, FileAction::Modify);
    }

    #[test]
    fn test_git_parse_binary_diff() {
        // Binary file changes
        let log = "\
commit abc1234567890123456789012345678901234567
Author: Binary <binary@test.com>
Date: 1000

    Add binary files

A\timage.png
A\tdata.bin
M\texisting.so
";
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].files.len(), 3);
    }

    #[test]
    fn test_git_parse_submodule() {
        // Submodule changes
        let log = "\
commit abc1234567890123456789012345678901234567
Author: SubModule <submodule@test.com>
Date: 1000

    Update submodule

M\tvendor/external-lib
";
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(
            commits[0].files[0].path.to_str().unwrap(),
            "vendor/external-lib"
        );
    }

    #[test]
    fn test_git_parse_gpg_signed() {
        // GPG-signed commit (extra headers)
        let log = "\
commit abc1234567890123456789012345678901234567
gpgsig -----BEGIN PGP SIGNATURE-----

 iQEzBAABCAAdFiEE...
 -----END PGP SIGNATURE-----
Author: Signer <signer@test.com>
Date: 1000

    Signed commit

A\tsigned.rs
";
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].author, "Signer");
    }

    #[test]
    fn test_git_parse_unicode_author() {
        let log = "\
commit abc1234567890123456789012345678901234567
Author: 田中太郎 <tanaka@example.com>
Date: 1000

    Unicode author

A\tfile.rs
";
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits[0].author, "田中太郎");
    }

    #[test]
    fn test_git_parse_unicode_path() {
        let log = "\
commit abc1234567890123456789012345678901234567
Author: Test <test@test.com>
Date: 1000

    Unicode path

A\t文档/测试.rs
";
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits[0].files[0].path.to_str().unwrap(), "文档/测试.rs");
    }

    #[test]
    fn test_git_parse_copy() {
        // Copy operation
        let log = "\
commit abc1234567890123456789012345678901234567
Author: Copier <copy@test.com>
Date: 1000

    Copy file

C100\tsrc/original.rs\tsrc/copy.rs
";
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].files[0].action, FileAction::Create);
        assert_eq!(commits[0].files[0].path.to_str().unwrap(), "src/copy.rs");
    }

    #[test]
    fn test_git_parse_unmerged() {
        // Unmerged file status
        let log = "\
commit abc1234567890123456789012345678901234567
Author: Unmerged <unmerged@test.com>
Date: 1000

    Resolve conflict

U\tconflicted.rs
";
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits[0].files[0].action, FileAction::Modify);
    }

    #[test]
    fn test_git_parse_commit_message_with_action_like_start() {
        // Commit message that looks like a file status line but isn't
        let log = "\
commit abc1234567890123456789012345678901234567
Author: Test <test@test.com>
Date: 1000

    Add new feature

A\tfile.rs
";
        let parser = GitParser::new();
        let commits = parser.parse_str(log).unwrap();
        // Should only have one file, not parse \"Add new feature\" as a file
        assert_eq!(commits[0].files.len(), 1);
        assert_eq!(commits[0].files[0].path.to_str().unwrap(), "file.rs");
    }

    // =========================================================================
    // Mutation Testing: Kill missed mutants
    // =========================================================================

    /// Kill mutant: is_git_action_char → replace with true
    /// Non-action characters must return false.
    #[test]
    fn test_is_git_action_char_false_cases() {
        assert!(!is_git_action_char('X'));
        assert!(!is_git_action_char('Z'));
        assert!(!is_git_action_char('1'));
        assert!(!is_git_action_char(' '));
        assert!(!is_git_action_char('\t'));
        assert!(is_git_action_char('A'));
        assert!(is_git_action_char('M'));
        assert!(is_git_action_char('D'));
        assert!(is_git_action_char('R'));
        assert!(is_git_action_char('C'));
        assert!(is_git_action_char('T'));
        assert!(is_git_action_char('U'));
        assert!(is_git_action_char('a'));
        assert!(is_git_action_char('m'));
        assert!(is_git_action_char('d'));
        assert!(is_git_action_char('r'));
        assert!(is_git_action_char('c'));
        assert!(is_git_action_char('t'));
        assert!(is_git_action_char('u'));
    }

    /// Kill mutant: parse_file_status line.len() < 3 boundary
    /// A 2-character space-separated line should return None.
    #[test]
    fn test_parse_file_status_short_line() {
        // Exactly 2 chars: too short, should return None
        let result = GitParser::parse_file_status("A ", 1).unwrap();
        assert!(result.is_none(), "2-char line should return None");
        // Exactly 3 chars with space format: "A f" should parse
        let result = GitParser::parse_file_status("A f", 1).unwrap();
        assert!(result.is_some(), "3-char 'A f' should parse");
        // Tab format works regardless of length
        let result = GitParser::parse_file_status("M\tx", 1).unwrap();
        assert!(result.is_some());
    }

    /// Kill mutant: parse_file_status !is_git_action_char → delete !
    /// Non-action first char in space-separated format should return None.
    #[test]
    fn test_parse_file_status_non_action_char_space() {
        let result = GitParser::parse_file_status("X  file.rs", 1).unwrap();
        assert!(result.is_none(), "non-action char should return None");
        let result = GitParser::parse_file_status("Z  file.rs", 1).unwrap();
        assert!(result.is_none());
    }

    /// Kill mutant: parse_author_line email_end > email_start → >=
    /// Malformed brackets where > comes before or at < position.
    #[test]
    fn test_parse_author_line_malformed_brackets() {
        // "><" case: rfind('<') = 1, rfind('>') = 0 → not after <
        let (name, email) = GitParser::parse_author_line("Author: ><");
        assert_eq!(name, "><");
        assert!(email.is_none());
        // Normal case
        let (name, email) = GitParser::parse_author_line("Author: John <john@test.com>");
        assert_eq!(name, "John");
        assert_eq!(email.unwrap(), "john@test.com");
    }

    /// Kill mutant: can_parse && → || and >= 7 → >= boundary
    /// Short hash (< 7 chars) or non-hex must NOT match.
    #[test]
    fn test_can_parse_short_hash() {
        let parser = GitParser::new();
        assert!(
            !parser.can_parse("commit abcde\n"),
            "5-char hash too short"
        );
        assert!(
            parser.can_parse("commit abcdef0\n"),
            "7-char hex hash should match"
        );
        assert!(
            !parser.can_parse("commit abcdefghij\n"),
            "non-hex chars should not match"
        );
    }

    /// Kill mutant: can_parse line.len() > 10 boundary
    #[test]
    fn test_can_parse_line_length_boundary() {
        let parser = GitParser::new();
        // "commit abc" = 10 chars total, len() > 10 is false
        assert!(!parser.can_parse("commit abc"));
        // "commit abcdef0" = 14 chars, 7 hex chars
        assert!(parser.can_parse("commit abcdef0"));
    }

    /// Kill mutant: parse_str +=→*= on line counting
    #[test]
    fn test_parse_str_multiple_commits_line_tracking() {
        let parser = GitParser::new();
        let log = "\
commit abc1234567890123456789012345678901234567
Author: A <a@t.com>
Date: 100

A\tfile1.rs

commit def4567890123456789012345678901234567890
Author: B <b@t.com>
Date: 200

M\tfile2.rs
";
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 2);
        assert_eq!(commits[0].files[0].action, FileAction::Create);
        assert_eq!(commits[1].files[0].action, FileAction::Modify);
    }

    /// Kill mutant: with_options → Default
    #[test]
    fn test_with_options_preserves_options() {
        let opts = ParseOptions::default().with_max_commits(3);
        let parser = GitParser::with_options(opts);
        // Parse log with 3+ commits, should stop at 3
        let log = "\
commit aaa1234567890123456789012345678901234567
Author: A <a@t.com>
Date: 100

A\tfile1.rs

commit bbb4567890123456789012345678901234567890
Author: B <b@t.com>
Date: 200

M\tfile2.rs

commit ccc4567890123456789012345678901234567890
Author: C <c@t.com>
Date: 300

A\tfile3.rs

commit ddd4567890123456789012345678901234567890
Author: D <d@t.com>
Date: 400

A\tfile4.rs
";
        let commits = parser.parse_str(log).unwrap();
        assert!(
            commits.len() <= 3,
            "with_max_commits(3) should limit to 3, got {}",
            commits.len()
        );
    }
}
