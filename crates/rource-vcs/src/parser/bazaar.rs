//! Bazaar (bzr) log parser.
//!
//! This parser handles Bazaar log output formats:
//!
//! ## Standard verbose format (`bzr log -v`)
//!
//! ```text
//! ------------------------------------------------------------
//! revno: 1
//! committer: John Doe <john@example.com>
//! branch nick: trunk
//! timestamp: Mon 2024-01-01 12:00:00 +0000
//! message:
//!   Initial commit
//! added:
//!   src/main.rs
//! modified:
//!   README.md
//! ```
//!
//! ## Short format (`bzr log --short`)
//!
//! ```text
//!     1 John Doe 2024-01-01 Initial commit
//! ```
//!
//! To generate compatible output, use:
//!
//! ```bash
//! bzr log -v
//! ```

use crate::commit::{Commit, FileAction, FileChange};
use crate::error::{ParseError, ParseResult};
use crate::parser::{ParseOptions, Parser};
use std::path::PathBuf;

/// Parser for Bazaar log output.
#[derive(Debug, Clone)]
pub struct BazaarParser {
    options: ParseOptions,
}

impl BazaarParser {
    /// Creates a new Bazaar parser with default options.
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

    /// Parses verbose bzr log format.
    fn parse_verbose(&self, input: &str) -> Vec<Commit> {
        let mut commits = Vec::new();
        let mut current_revno: Option<String> = None;
        let mut current_author: Option<String> = None;
        let mut current_date: Option<i64> = None;
        let mut current_files: Vec<FileChange> = Vec::new();
        let mut current_action: Option<FileAction> = None;
        let mut in_message = false;

        for line in input.lines() {
            // Check for separator line
            if line.starts_with("----") && line.chars().filter(|&c| c == '-').count() >= 10 {
                // Save previous commit if exists
                if let (Some(author), Some(timestamp)) = (&current_author, current_date) {
                    if !current_files.is_empty() && self.options.timestamp_in_range(timestamp) {
                        let hash = current_revno.take().unwrap_or_default();
                        let files = std::mem::take(&mut current_files);
                        commits
                            .push(Commit::new(hash, timestamp, author.clone()).with_files(files));

                        if self.options.limit_reached(commits.len()) {
                            return commits;
                        }
                    }
                }

                // Start new commit
                current_revno = None;
                current_author = None;
                current_date = None;
                current_files.clear();
                current_action = None;
                in_message = false;
                continue;
            }

            let trimmed = line.trim();

            // Check for section headers
            if trimmed.starts_with("revno:") {
                // Extract revision number (may include merge marker like "123 [merge]")
                let revno_str = trimmed.trim_start_matches("revno:").trim();
                current_revno = Some(
                    revno_str
                        .split_whitespace()
                        .next()
                        .unwrap_or("")
                        .to_string(),
                );
                in_message = false;
                current_action = None;
            } else if trimmed.starts_with("committer:") || trimmed.starts_with("author:") {
                let author_str = if trimmed.starts_with("committer:") {
                    trimmed.trim_start_matches("committer:")
                } else {
                    trimmed.trim_start_matches("author:")
                };
                current_author = Some(extract_author_name(author_str.trim()).to_string());
                in_message = false;
                current_action = None;
            } else if trimmed.starts_with("timestamp:") {
                let date_str = trimmed.trim_start_matches("timestamp:").trim();
                current_date = parse_bzr_date(date_str);
                in_message = false;
                current_action = None;
            } else if trimmed == "message:" {
                in_message = true;
                current_action = None;
            } else if trimmed == "added:" {
                current_action = Some(FileAction::Create);
                in_message = false;
            } else if trimmed == "modified:" {
                current_action = Some(FileAction::Modify);
                in_message = false;
            } else if trimmed == "removed:" {
                current_action = Some(FileAction::Delete);
                in_message = false;
            } else if trimmed == "renamed:" {
                current_action = Some(FileAction::Modify); // Treat rename as modify
                in_message = false;
            } else if let Some(action) = current_action {
                if !in_message && !trimmed.is_empty() {
                    // This is a file path
                    let path = parse_bzr_file_path(trimmed);
                    if !path.is_empty() {
                        current_files.push(FileChange {
                            path: PathBuf::from(path),
                            action,
                        });
                    }
                }
            }
            // Skip other metadata lines we don't care about (branch nick, tags, etc.)
        }

        // Don't forget the last commit
        if let (Some(author), Some(timestamp)) = (&current_author, current_date) {
            if !current_files.is_empty() && self.options.timestamp_in_range(timestamp) {
                let hash = current_revno.unwrap_or_default();
                commits
                    .push(Commit::new(hash, timestamp, author.clone()).with_files(current_files));
            }
        }

        commits
    }

    /// Parses short format: "    1 John Doe 2024-01-01 message"
    /// This format doesn't include file changes, so it's not very useful for visualization.
    fn parse_short(&self, input: &str) -> ParseResult<Vec<Commit>> {
        let mut commits = Vec::new();

        for (line_num, line) in input.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }

            // Short format: revno author date message
            let parts: Vec<&str> = trimmed.splitn(4, char::is_whitespace).collect();
            if parts.len() < 3 {
                if self.options.skip_invalid_lines {
                    continue;
                }
                return Err(ParseError::InvalidLine {
                    line_number: line_num + 1,
                    line: line.to_string(),
                    expected: "revno author date [message]",
                });
            }

            let revno = parts[0].to_string();

            // Find the date (YYYY-MM-DD format)
            let mut date_idx = None;
            for (i, part) in parts.iter().enumerate().skip(1) {
                if is_date_format(part) {
                    date_idx = Some(i);
                    break;
                }
            }

            if let Some(idx) = date_idx {
                // Author is everything between revno and date
                let author = if idx > 1 {
                    parts[1..idx].join(" ")
                } else {
                    "Unknown".to_string()
                };

                if let Some(timestamp) = parse_date_only(parts[idx]) {
                    if self.options.timestamp_in_range(timestamp) {
                        // Short format doesn't include files, create empty commit
                        // This won't be useful for visualization but maintains compatibility
                        if !self.options.skip_empty_commits {
                            commits.push(Commit::new(revno, timestamp, author));

                            if self.options.limit_reached(commits.len()) {
                                break;
                            }
                        }
                    }
                }
            }
        }

        Ok(commits)
    }
}

impl Default for BazaarParser {
    fn default() -> Self {
        Self::new()
    }
}

impl Parser for BazaarParser {
    fn name(&self) -> &'static str {
        "bazaar"
    }

    fn parse_str(&self, input: &str) -> ParseResult<Vec<Commit>> {
        // Detect format by looking for separator lines
        if input.contains("------------------------------------------------------------") {
            Ok(self.parse_verbose(input))
        } else if input.lines().any(|l| {
            let t = l.trim();
            !t.is_empty() && t.chars().next().is_some_and(|c| c.is_ascii_digit())
        }) {
            self.parse_short(input)
        } else {
            // Try verbose anyway
            Ok(self.parse_verbose(input))
        }
    }

    fn can_parse(&self, input: &str) -> bool {
        let input = input.trim_start();

        // Check for verbose format (starts with dashes separator)
        if input.starts_with("----") && input.lines().any(|l| l.trim().starts_with("revno:")) {
            return true;
        }

        // Check for verbose format without leading separator
        if input.starts_with("revno:") {
            return true;
        }

        // Check for lines containing bzr-specific markers
        let first_lines: Vec<&str> = input.lines().take(10).collect();
        for line in &first_lines {
            let trimmed = line.trim();
            if trimmed.starts_with("committer:")
                || trimmed.starts_with("branch nick:")
                || trimmed.starts_with("timestamp:")
            {
                return true;
            }
        }

        false
    }
}

/// Extracts the author name from various formats.
///
/// Handles:
/// - "John Doe" -> "John Doe"
/// - "John Doe <john@example.com>" -> "John Doe"
/// - "<john@example.com>" -> "john@example.com"
fn extract_author_name(author: &str) -> &str {
    author.find('<').map_or_else(
        || author.trim(),
        |pos| {
            let name = author[..pos].trim();
            if name.is_empty() {
                // Extract email as name if no name before <
                author.trim_start_matches('<').trim_end_matches('>').trim()
            } else {
                name
            }
        },
    )
}

/// Parses a date string from bzr log output.
///
/// Handles formats:
/// - "Mon 2024-01-01 12:00:00 +0000"
/// - "Mon Jan 01 12:00:00 2024 +0000"
/// - "2024-01-01"
fn parse_bzr_date(date_str: &str) -> Option<i64> {
    let date_str = date_str.trim();

    // Skip day name if present
    let date_str = skip_day_name(date_str);
    let parts: Vec<&str> = date_str.split_whitespace().collect();

    if parts.is_empty() {
        return None;
    }

    // Try YYYY-MM-DD format first
    if is_date_format(parts[0]) {
        let date_parts: Vec<&str> = parts[0].split('-').collect();
        if date_parts.len() >= 3 {
            let year: i32 = date_parts[0].parse().ok()?;
            let month: u32 = date_parts[1].parse().ok()?;
            let day: u32 = date_parts[2].parse().ok()?;

            let mut timestamp = i64::from(days_since_unix_epoch(year, month, day)?) * 86400;

            // Parse time if present
            if parts.len() >= 2 {
                if let Some((h, m, s)) = parse_time(parts[1]) {
                    timestamp += i64::from(h) * 3600 + i64::from(m) * 60 + i64::from(s);
                }
            }

            return Some(timestamp);
        }
    }

    // Try "Jan 01 12:00:00 2024" format
    if is_month(parts[0]) && parts.len() >= 4 {
        let month = parse_month(parts[0])?;
        let day: u32 = parts[1].parse().ok()?;
        let time = parts[2];
        let year: i32 = parts[3].parse().ok()?;

        let timestamp = i64::from(days_since_unix_epoch(year, month, day)?) * 86400;
        if let Some((h, m, s)) = parse_time(time) {
            return Some(timestamp + i64::from(h) * 3600 + i64::from(m) * 60 + i64::from(s));
        }
        return Some(timestamp);
    }

    None
}

/// Parse time string "HH:MM:SS"
fn parse_time(s: &str) -> Option<(u32, u32, u32)> {
    let parts: Vec<&str> = s.split(':').collect();
    if parts.len() >= 3 {
        let h: u32 = parts[0].parse().ok()?;
        let m: u32 = parts[1].parse().ok()?;
        let s: u32 = parts[2].parse().ok()?;
        return Some((h, m, s));
    }
    None
}

/// Parse file path from bzr log output.
/// Handles indented paths and rename format "old => new"
fn parse_bzr_file_path(line: &str) -> &str {
    let trimmed = line.trim();

    // Handle rename format: "old_path => new_path"
    if let Some(arrow_pos) = trimmed.find(" => ") {
        // Return the new path (after =>)
        return trimmed[arrow_pos + 4..].trim();
    }

    trimmed
}

/// Check if a string looks like YYYY-MM-DD date
fn is_date_format(s: &str) -> bool {
    let parts: Vec<&str> = s.split('-').collect();
    if parts.len() == 3 {
        if let (Ok(y), Ok(m), Ok(d)) = (
            parts[0].parse::<i32>(),
            parts[1].parse::<u32>(),
            parts[2].parse::<u32>(),
        ) {
            return (1970..=2100).contains(&y) && (1..=12).contains(&m) && (1..=31).contains(&d);
        }
    }
    false
}

/// Parse YYYY-MM-DD to timestamp at midnight
fn parse_date_only(s: &str) -> Option<i64> {
    let parts: Vec<&str> = s.split('-').collect();
    if parts.len() >= 3 {
        let year: i32 = parts[0].parse().ok()?;
        let month: u32 = parts[1].parse().ok()?;
        let day: u32 = parts[2].parse().ok()?;
        return Some(i64::from(days_since_unix_epoch(year, month, day)?) * 86400);
    }
    None
}

/// Skips the day name prefix from a date string.
fn skip_day_name(s: &str) -> &str {
    let s = s.trim();
    // Check for day names
    let day_names = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];
    for day in &day_names {
        if s.len() > day.len() && s[..day.len()].eq_ignore_ascii_case(day) {
            let rest = &s[day.len()..];
            // Skip comma and/or whitespace
            return rest.trim_start_matches(|c: char| c == ',' || c.is_whitespace());
        }
    }
    s
}

/// Checks if a string looks like a month abbreviation.
fn is_month(s: &str) -> bool {
    matches!(
        s.to_lowercase().as_str(),
        "jan"
            | "feb"
            | "mar"
            | "apr"
            | "may"
            | "jun"
            | "jul"
            | "aug"
            | "sep"
            | "oct"
            | "nov"
            | "dec"
    )
}

/// Parses a month abbreviation to a number (1-12).
fn parse_month(s: &str) -> Option<u32> {
    match s.to_lowercase().as_str() {
        "jan" => Some(1),
        "feb" => Some(2),
        "mar" => Some(3),
        "apr" => Some(4),
        "may" => Some(5),
        "jun" => Some(6),
        "jul" => Some(7),
        "aug" => Some(8),
        "sep" => Some(9),
        "oct" => Some(10),
        "nov" => Some(11),
        "dec" => Some(12),
        _ => None,
    }
}

/// Calculate days since Unix epoch (Jan 1, 1970).
///
/// Returns `None` if the date is invalid (year < 1970, month not in 1-12, or day not in 1-31).
fn days_since_unix_epoch(year: i32, month: u32, day: u32) -> Option<u32> {
    // Days per month (non-leap year)
    const DAYS_PER_MONTH: [u32; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];

    // Validate inputs to prevent array bounds violations and underflow
    if year < 1970 {
        return None;
    }
    if !(1..=12).contains(&month) {
        return None;
    }
    if !(1..=31).contains(&day) {
        return None;
    }

    let mut days: u32 = 0;

    // Add days for complete years
    for y in 1970..year {
        days += if is_leap_year(y) { 366 } else { 365 };
    }

    // Add days for complete months in current year
    // Safe: month is validated to be 1-12, so (month - 1) is 0-11
    for m in 1..month {
        days += DAYS_PER_MONTH[m as usize - 1];
        if m == 2 && is_leap_year(year) {
            days += 1;
        }
    }

    // Add remaining days
    // Safe: day is validated to be >= 1, so day - 1 won't underflow
    days += day - 1;

    Some(days)
}

/// Check if a year is a leap year.
const fn is_leap_year(year: i32) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bazaar_parser_new() {
        let parser = BazaarParser::new();
        assert_eq!(parser.name(), "bazaar");
    }

    #[test]
    fn test_parse_verbose_format() {
        let log = r"------------------------------------------------------------
revno: 1
committer: Alice <alice@example.com>
branch nick: trunk
timestamp: Mon 2024-01-01 12:00:00 +0000
message:
  Initial commit
added:
  src/main.rs
  src/lib.rs
modified:
  README.md

------------------------------------------------------------
revno: 2
committer: Bob <bob@example.com>
branch nick: trunk
timestamp: Tue 2024-01-02 14:30:00 +0000
message:
  Add feature
added:
  src/feature.rs
removed:
  old_file.txt
";
        let parser = BazaarParser::new();
        let commits = parser.parse_str(log).unwrap();

        assert_eq!(commits.len(), 2);
        assert_eq!(commits[0].author, "Alice");
        assert_eq!(commits[0].hash, "1");
        assert_eq!(commits[0].files.len(), 3);
        assert_eq!(commits[0].files[0].action, FileAction::Create);
        assert_eq!(commits[0].files[2].action, FileAction::Modify);

        assert_eq!(commits[1].author, "Bob");
        assert_eq!(commits[1].hash, "2");
        assert_eq!(commits[1].files.len(), 2);
    }

    #[test]
    fn test_parse_verbose_with_merge() {
        let log = r"------------------------------------------------------------
revno: 5 [merge]
tags: v1.0
committer: Alice
timestamp: Wed 2024-01-03 10:00:00 +0000
message:
  Merge feature branch
modified:
  src/main.rs
";
        let parser = BazaarParser::new();
        let commits = parser.parse_str(log).unwrap();

        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].hash, "5");
    }

    #[test]
    fn test_parse_verbose_with_rename() {
        let log = r"------------------------------------------------------------
revno: 3
committer: Charlie
timestamp: Thu 2024-01-04 09:00:00 +0000
message:
  Rename files
renamed:
  old_name.rs => new_name.rs
  src/old.rs => src/new.rs
";
        let parser = BazaarParser::new();
        let commits = parser.parse_str(log).unwrap();

        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].files.len(), 2);
        assert_eq!(commits[0].files[0].path, PathBuf::from("new_name.rs"));
        assert_eq!(commits[0].files[1].path, PathBuf::from("src/new.rs"));
    }

    #[test]
    fn test_parse_author_field() {
        // bzr can use "author:" instead of "committer:"
        let log = r"------------------------------------------------------------
revno: 1
author: David <david@example.com>
timestamp: Fri 2024-01-05 08:00:00 +0000
message:
  Test
modified:
  test.rs
";
        let parser = BazaarParser::new();
        let commits = parser.parse_str(log).unwrap();

        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].author, "David");
    }

    #[test]
    fn test_can_parse_verbose() {
        let parser = BazaarParser::new();

        // With separator
        assert!(parser
            .can_parse("------------------------------------------------------------\nrevno: 1\n"));

        // Without separator
        assert!(parser.can_parse("revno: 1\ncommitter: Test\n"));

        // With bzr-specific markers
        assert!(parser.can_parse("something\nbranch nick: trunk\n"));
        assert!(parser.can_parse("something\ntimestamp: Mon 2024-01-01\n"));
    }

    #[test]
    fn test_cannot_parse_other_formats() {
        let parser = BazaarParser::new();

        // Git format
        assert!(!parser.can_parse("commit abc123\nAuthor: Test\n"));

        // Custom format
        assert!(!parser.can_parse("1234567890|John|A|file.txt\n"));

        // Random text
        assert!(!parser.can_parse("This is not a bzr log\n"));
    }

    #[test]
    fn test_extract_author_name() {
        assert_eq!(extract_author_name("John Doe"), "John Doe");
        assert_eq!(
            extract_author_name("John Doe <john@example.com>"),
            "John Doe"
        );
        assert_eq!(
            extract_author_name("<john@example.com>"),
            "john@example.com"
        );
        assert_eq!(extract_author_name("  Alice  "), "Alice");
    }

    #[test]
    fn test_parse_bzr_date() {
        // YYYY-MM-DD HH:MM:SS format
        let ts = parse_bzr_date("2024-01-01 12:00:00 +0000").unwrap();
        // Jan 1, 2024 at 12:00:00 UTC
        // Days from 1970 to 2024 = 19724 days (including leap years)
        // Plus 12 hours = 43200 seconds
        assert!(ts > 0);

        // With day name
        let ts2 = parse_bzr_date("Mon 2024-01-01 12:00:00 +0000").unwrap();
        assert_eq!(ts, ts2);
    }

    #[test]
    fn test_parse_bzr_file_path() {
        // Regular path
        assert_eq!(parse_bzr_file_path("  src/main.rs"), "src/main.rs");

        // Rename
        assert_eq!(parse_bzr_file_path("old.rs => new.rs"), "new.rs");
        assert_eq!(
            parse_bzr_file_path("  src/old.rs => src/new.rs  "),
            "src/new.rs"
        );
    }

    #[test]
    fn test_is_date_format() {
        assert!(is_date_format("2024-01-01"));
        assert!(is_date_format("1970-01-01"));
        assert!(!is_date_format("2024-13-01")); // Invalid month
        assert!(!is_date_format("2024-01-32")); // Invalid day
        assert!(!is_date_format("1234567890")); // Unix timestamp
        assert!(!is_date_format("not-a-date"));
    }

    #[test]
    fn test_is_leap_year() {
        assert!(!is_leap_year(2023));
        assert!(is_leap_year(2024));
        assert!(!is_leap_year(1900));
        assert!(is_leap_year(2000));
    }

    #[test]
    fn test_days_since_unix_epoch() {
        // Jan 1, 1970 = 0 days
        assert_eq!(days_since_unix_epoch(1970, 1, 1), Some(0));
        // Jan 2, 1970 = 1 day
        assert_eq!(days_since_unix_epoch(1970, 1, 2), Some(1));
        // Before epoch should return None
        assert_eq!(days_since_unix_epoch(1969, 1, 1), None);
    }

    #[test]
    fn test_days_since_unix_epoch_invalid_month() {
        // Month 0 is invalid
        assert_eq!(days_since_unix_epoch(2024, 0, 15), None);
        // Month 13 is invalid
        assert_eq!(days_since_unix_epoch(2024, 13, 15), None);
    }

    #[test]
    fn test_days_since_unix_epoch_invalid_day() {
        // Day 0 is invalid
        assert_eq!(days_since_unix_epoch(2024, 6, 0), None);
        // Day 32 is invalid
        assert_eq!(days_since_unix_epoch(2024, 6, 32), None);
    }

    #[test]
    fn test_empty_commits_skipped() {
        // Commit with no files should be skipped by default
        let log = r"------------------------------------------------------------
revno: 1
committer: Test
timestamp: Mon 2024-01-01 12:00:00 +0000
message:
  Empty commit
";
        let parser = BazaarParser::new();
        let commits = parser.parse_str(log).unwrap();

        // Empty commits are skipped
        assert_eq!(commits.len(), 0);
    }

    #[test]
    fn test_time_range_filter() {
        let log = r"------------------------------------------------------------
revno: 1
committer: Alice
timestamp: Mon 2024-01-01 12:00:00 +0000
message:
  Old commit
modified:
  old.rs

------------------------------------------------------------
revno: 2
committer: Bob
timestamp: Wed 2025-01-01 12:00:00 +0000
message:
  New commit
modified:
  new.rs
";
        // Only get commits from 2025 onwards
        let start = i64::from(days_since_unix_epoch(2025, 1, 1).unwrap()) * 86400;
        let options = ParseOptions::default().with_time_range(start, 0);
        let parser = BazaarParser::with_options(options);
        let commits = parser.parse_str(log).unwrap();

        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].author, "Bob");
    }

    #[test]
    fn test_max_commits_limit() {
        let log = r"------------------------------------------------------------
revno: 1
committer: A
timestamp: Mon 2024-01-01 00:00:00 +0000
modified:
  a.rs

------------------------------------------------------------
revno: 2
committer: B
timestamp: Tue 2024-01-02 00:00:00 +0000
modified:
  b.rs

------------------------------------------------------------
revno: 3
committer: C
timestamp: Wed 2024-01-03 00:00:00 +0000
modified:
  c.rs
";
        let options = ParseOptions::default().with_max_commits(2);
        let parser = BazaarParser::with_options(options);
        let commits = parser.parse_str(log).unwrap();

        assert_eq!(commits.len(), 2);
    }
}
