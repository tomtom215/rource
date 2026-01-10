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
    matches!(c, 'A' | 'a' | 'M' | 'm' | 'D' | 'd' | 'R' | 'r' | 'C' | 'c' | 'T' | 't' | 'U' | 'u')
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
        // We take the new path
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
            .map(str::trim)
            .unwrap_or(line);

        if let Some(email_start) = line.rfind('<') {
            if let Some(email_end) = line.rfind('>') {
                let name = line[..email_start].trim().to_string();
                let email = line[email_start + 1..email_end].to_string();
                return (name, Some(email));
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
            .map(str::trim)
            .unwrap_or(line)
            .trim();

        line.parse::<i64>().map_err(|_| ParseError::InvalidTimestamp {
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
                    } else if line.starts_with("commit ") {
                        // New commit without author? Reset
                        current_hash = line[7..].trim().to_string();
                    }
                    // Skip other lines (like Merge: lines)
                }

                ParserState::ExpectingDate => {
                    if line.starts_with("Date:") || line.starts_with("date:") {
                        current_timestamp = Self::parse_date_line(line, line_number)?;
                        state = ParserState::ReadingFiles;
                    } else if line.starts_with("commit ") {
                        // New commit without date? Reset
                        current_hash = line[7..].trim().to_string();
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
                                commit = commit.with_files(current_files.drain(..));
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
        {
            if self.options.timestamp_in_range(current_timestamp) {
                let mut commit =
                    Commit::new(current_hash, current_timestamp, current_author);
                if let Some(email) = current_email {
                    commit = commit.with_email(email);
                }
                commit = commit.with_files(current_files);
                commits.push(commit);
            }
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

        let parser =
            GitParser::with_options(ParseOptions::default().with_time_range(1500, 2500));
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
        assert!(matches!(
            parser.parse_str(""),
            Err(ParseError::EmptyLog)
        ));
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
}
