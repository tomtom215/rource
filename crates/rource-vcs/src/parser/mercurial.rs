//! Mercurial (hg) log parser.
//!
//! This parser handles Mercurial log output in a template format:
//!
//! ```text
//! timestamp|author|action|file
//! ```
//!
//! Or the verbose hg log format with file status:
//!
//! ```text
//! changeset:   1:abc123
//! user:        John Doe <john@example.com>
//! date:        Thu Jan 01 00:00:00 2024 +0000
//! files:       src/main.rs src/lib.rs
//! description:
//! First commit
//! ```
//!
//! To generate compatible output, use:
//!
//! ```bash
//! hg log --template "{date|hgdate}|{author|person}|A|{files}\n"
//! ```
//!
//! Or with file status using the custom template:
//!
//! ```bash
//! hg log -v --template "changeset:{rev}\nuser:{author}\ndate:{date|rfc822date}\n{file_adds % 'A|{file}\n'}{file_mods % 'M|{file}\n'}{file_dels % 'D|{file}\n'}\n"
//! ```

use crate::commit::{Commit, FileAction, FileChange};
use crate::error::{ParseError, ParseResult};
use crate::parser::{ParseOptions, Parser};
use std::collections::HashMap;
use std::path::PathBuf;

/// Parser for Mercurial log output.
#[derive(Debug, Clone)]
pub struct MercurialParser {
    options: ParseOptions,
}

impl MercurialParser {
    /// Creates a new Mercurial parser with default options.
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

    /// Parses verbose hg log format.
    fn parse_verbose(&self, input: &str) -> Vec<Commit> {
        let mut commits = Vec::new();
        let mut current_changeset: Option<String> = None;
        let mut current_author: Option<String> = None;
        let mut current_date: Option<i64> = None;
        let mut current_files: Vec<FileChange> = Vec::new();

        for line in input.lines() {
            let line = line.trim();

            if line.starts_with("changeset:") {
                // Save previous commit if exists
                if let (Some(author), Some(timestamp)) = (&current_author, current_date) {
                    if !current_files.is_empty() && self.options.timestamp_in_range(timestamp) {
                        let hash = current_changeset.take().unwrap_or_default();
                        let files = std::mem::take(&mut current_files);
                        commits
                            .push(Commit::new(hash, timestamp, author.clone()).with_files(files));

                        if self.options.limit_reached(commits.len()) {
                            break;
                        }
                    }
                }

                // Start new changeset
                current_changeset = Some(
                    line.trim_start_matches("changeset:")
                        .trim()
                        .split(':')
                        .next_back()
                        .unwrap_or("")
                        .to_string(),
                );
                current_author = None;
                current_date = None;
                current_files.clear();
            } else if line.starts_with("user:") {
                let user = line.trim_start_matches("user:").trim();
                // Extract name from "Name <email>" format
                current_author = Some(extract_author_name(user).to_string());
            } else if line.starts_with("date:") {
                let date_str = line.trim_start_matches("date:").trim();
                current_date = parse_hg_date(date_str);
            } else if line.starts_with("files:") {
                let files_str = line.trim_start_matches("files:").trim();
                for file in files_str.split_whitespace() {
                    current_files.push(FileChange {
                        path: PathBuf::from(file),
                        action: FileAction::Modify, // Default action for simple files list
                    });
                }
            }
        }

        // Don't forget the last commit
        if let (Some(author), Some(timestamp)) = (&current_author, current_date) {
            if !current_files.is_empty() && self.options.timestamp_in_range(timestamp) {
                let hash = current_changeset.unwrap_or_default();
                commits
                    .push(Commit::new(hash, timestamp, author.clone()).with_files(current_files));
            }
        }

        commits
    }

    /// Parses template format: timestamp|author|action|file
    fn parse_template(&self, input: &str) -> ParseResult<Vec<Commit>> {
        let mut commits: HashMap<(i64, String), Vec<FileChange>> = HashMap::new();
        let mut order: Vec<(i64, String)> = Vec::new();

        for (line_num, line) in input.lines().enumerate() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }

            let parts: Vec<&str> = line.split('|').collect();
            if parts.len() < 4 {
                if self.options.skip_invalid_lines {
                    continue;
                }
                return Err(ParseError::InvalidLine {
                    line_number: line_num + 1,
                    line: line.to_string(),
                    expected: "timestamp|author|action|filepath",
                });
            }

            // Parse timestamp - hgdate format is "unix_timestamp timezone_offset"
            let timestamp = parts[0]
                .split_whitespace()
                .next()
                .unwrap_or("")
                .parse::<i64>()
                .map_err(|_| ParseError::InvalidTimestamp {
                    line_number: line_num + 1,
                    value: parts[0].to_string(),
                })?;

            if !self.options.timestamp_in_range(timestamp) {
                continue;
            }

            let author = extract_author_name(parts[1].trim()).to_string();
            let action = FileAction::from_char(parts[2].trim().chars().next().unwrap_or('M'))
                .unwrap_or(FileAction::Modify);
            let file_path = PathBuf::from(parts[3].trim());

            let key = (timestamp, author.clone());
            if !commits.contains_key(&key) {
                order.push(key.clone());
            }
            commits.entry(key).or_default().push(FileChange {
                path: file_path,
                action,
            });

            if self.options.limit_reached(order.len()) {
                break;
            }
        }

        // Convert to commits
        let result: Vec<Commit> = order
            .into_iter()
            .filter_map(|(timestamp, author)| {
                commits
                    .remove(&(timestamp, author.clone()))
                    .map(|files| Commit::new(String::new(), timestamp, author).with_files(files))
            })
            .collect();

        Ok(result)
    }
}

impl Default for MercurialParser {
    fn default() -> Self {
        Self::new()
    }
}

impl Parser for MercurialParser {
    fn name(&self) -> &'static str {
        "mercurial"
    }

    fn parse_str(&self, input: &str) -> ParseResult<Vec<Commit>> {
        // Detect format
        if input.trim_start().starts_with("changeset:") {
            Ok(self.parse_verbose(input))
        } else {
            self.parse_template(input)
        }
    }

    fn can_parse(&self, input: &str) -> bool {
        let first_line = input.lines().next().unwrap_or("").trim();

        // Check for verbose format
        if first_line.starts_with("changeset:") {
            return true;
        }

        // Check for template format with hgdate (timestamp|author|action|file)
        // Mercurial hgdate format includes timezone offset: "timestamp offset"
        // This distinguishes it from Custom format which uses plain timestamps
        let parts: Vec<&str> = first_line.split('|').collect();
        if parts.len() >= 4 {
            let timestamp_field = parts[0].trim();
            // hgdate format has a space: "1234567890 -18000"
            // Custom format has no space: "1234567890"
            let whitespace_parts: Vec<&str> = timestamp_field.split_whitespace().collect();
            if whitespace_parts.len() >= 2 {
                // Must have at least two parts (timestamp and offset)
                if whitespace_parts[0].parse::<i64>().is_ok() {
                    return true;
                }
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

/// Parses a date string from hg log output.
///
/// Handles formats:
/// - Unix timestamp: "1234567890"
/// - hgdate format: "1234567890 -18000"
/// - Verbose format: "Thu Jan 01 00:00:00 2024 +0000"
/// - RFC 822 format: "Thu, 01 Jan 2024 00:00:00 +0000"
fn parse_hg_date(date_str: &str) -> Option<i64> {
    let date_str = date_str.trim();

    // Try hgdate format first (timestamp offset)
    if let Some(first_part) = date_str.split_whitespace().next() {
        if let Ok(ts) = first_part.parse::<i64>() {
            return Some(ts);
        }
    }

    // Try to parse verbose/RFC 822 date format manually
    // Format: "Thu Jan 01 00:00:00 2024 +0000" or "Thu, 01 Jan 2024 00:00:00 +0000"
    parse_verbose_date(date_str)
}

/// Parses verbose date format without regex.
///
/// Handles:
/// - "Thu Jan 01 00:00:00 2024 +0000" (hg log verbose)
/// - "Thu, 01 Jan 2024 00:00:00 +0000" (RFC 822)
fn parse_verbose_date(date_str: &str) -> Option<i64> {
    // Remove day name prefix (Mon, Tue, etc.)
    let date_str = skip_day_name(date_str);

    // Split into parts
    let parts: Vec<&str> = date_str.split_whitespace().collect();
    if parts.len() < 4 {
        return None;
    }

    // Try to detect format by checking if first part is month or day
    let (day, month_str, year, time_str) = if is_month(parts[0]) {
        // Format: "Jan 01 00:00:00 2024 +0000"
        if parts.len() < 4 {
            return None;
        }
        let day: u32 = parts[1].parse().ok()?;
        let month_str = parts[0];
        let time_str = parts[2];
        let year: i32 = parts[3].parse().ok()?;
        (day, month_str, year, time_str)
    } else if parts.len() >= 4 && is_month(parts[1]) {
        // Format: "01 Jan 2024 00:00:00 +0000"
        let day: u32 = parts[0].parse().ok()?;
        let month_str = parts[1];
        let year: i32 = parts[2].parse().ok()?;
        let time_str = parts[3];
        (day, month_str, year, time_str)
    } else {
        return None;
    };

    // Parse time (HH:MM:SS)
    let time_parts: Vec<&str> = time_str.split(':').collect();
    if time_parts.len() < 3 {
        return None;
    }
    let hour: u32 = time_parts[0].parse().ok()?;
    let min: u32 = time_parts[1].parse().ok()?;
    let sec: u32 = time_parts[2].parse().ok()?;

    // Parse month
    let month = parse_month(month_str)?;

    // Calculate timestamp
    let days_since_epoch = days_since_unix_epoch(year, month, day)?;
    let timestamp = i64::from(days_since_epoch) * 86400
        + i64::from(hour) * 3600
        + i64::from(min) * 60
        + i64::from(sec);

    Some(timestamp)
}

/// Skips the day name prefix from a date string.
fn skip_day_name(s: &str) -> &str {
    let s = s.trim();
    // Check for day names followed by comma or space
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
fn days_since_unix_epoch(year: i32, month: u32, day: u32) -> Option<u32> {
    // Days per month (non-leap year)
    const DAYS_PER_MONTH: [u32; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];

    if year < 1970 {
        return None;
    }

    let mut days: u32 = 0;

    // Add days for complete years
    for y in 1970..year {
        days += if is_leap_year(y) { 366 } else { 365 };
    }

    // Add days for complete months in current year
    for m in 1..month {
        days += DAYS_PER_MONTH[m as usize - 1];
        if m == 2 && is_leap_year(year) {
            days += 1;
        }
    }

    // Add remaining days
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
    fn test_mercurial_parser_new() {
        let parser = MercurialParser::new();
        assert_eq!(parser.name(), "mercurial");
    }

    #[test]
    fn test_parse_template_format() {
        let log = "1704067200|Alice|A|src/main.rs\n1704067300|Bob|M|src/lib.rs\n";
        let parser = MercurialParser::new();
        let commits = parser.parse_str(log).unwrap();

        assert_eq!(commits.len(), 2);
        assert_eq!(commits[0].author, "Alice");
        assert_eq!(commits[0].files.len(), 1);
        assert_eq!(commits[0].files[0].action, FileAction::Create);
    }

    #[test]
    fn test_parse_template_hgdate_format() {
        // hgdate format includes timezone offset
        let log = "1704067200 -18000|Alice|A|src/main.rs\n";
        let parser = MercurialParser::new();
        let commits = parser.parse_str(log).unwrap();

        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].timestamp, 1_704_067_200);
    }

    #[test]
    fn test_parse_verbose_format() {
        let log = r#"changeset:   0:abc123
user:        Alice <alice@example.com>
date:        Mon Jan 01 12:00:00 2024 +0000
files:       src/main.rs

changeset:   1:def456
user:        Bob
date:        Tue Jan 02 12:00:00 2024 +0000
files:       src/lib.rs src/utils.rs
"#;
        let parser = MercurialParser::new();
        let commits = parser.parse_str(log).unwrap();

        assert_eq!(commits.len(), 2);
        assert_eq!(commits[0].author, "Alice");
        assert_eq!(commits[0].files.len(), 1);
        assert_eq!(commits[1].author, "Bob");
        assert_eq!(commits[1].files.len(), 2);
    }

    #[test]
    fn test_can_parse_template() {
        let parser = MercurialParser::new();
        // Plain timestamp without offset is detected as Custom format, not Mercurial
        assert!(!parser.can_parse("1704067200|Alice|A|src/main.rs"));
        // hgdate format with timezone offset is detected as Mercurial
        assert!(parser.can_parse("1704067200 -18000|Alice|A|src/main.rs"));
    }

    #[test]
    fn test_can_parse_verbose() {
        let parser = MercurialParser::new();
        assert!(parser.can_parse("changeset:   0:abc123\n"));
    }

    #[test]
    fn test_cannot_parse_invalid() {
        let parser = MercurialParser::new();
        assert!(!parser.can_parse("commit abc123\n"));
        assert!(!parser.can_parse("random text\n"));
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
    fn test_parse_hg_date() {
        // Unix timestamp
        assert_eq!(parse_hg_date("1704067200"), Some(1_704_067_200));

        // hgdate format
        assert_eq!(parse_hg_date("1704067200 -18000"), Some(1_704_067_200));

        // Invalid
        assert_eq!(parse_hg_date("not a date"), None);
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
    fn test_grouped_commits() {
        // Multiple files with same timestamp should be grouped
        let log = r#"1704067200|Alice|A|src/main.rs
1704067200|Alice|A|src/lib.rs
1704067200|Alice|M|Cargo.toml
"#;
        let parser = MercurialParser::new();
        let commits = parser.parse_str(log).unwrap();

        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].files.len(), 3);
    }
}
