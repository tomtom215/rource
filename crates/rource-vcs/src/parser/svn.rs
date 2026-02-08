// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! SVN XML log format parser.
//!
//! This parser handles output from `svn log --xml` which produces:
//!
//! ```xml
//! <?xml version="1.0" encoding="UTF-8"?>
//! <log>
//! <logentry revision="1234">
//! <author>username</author>
//! <date>2023-01-15T14:30:00.000000Z</date>
//! <paths>
//! <path action="M">/trunk/src/file.rs</path>
//! <path action="A">/trunk/src/new.rs</path>
//! </paths>
//! <msg>Commit message</msg>
//! </logentry>
//! </log>
//! ```
//!
//! This is a lightweight parser that doesn't require external XML libraries.

use crate::commit::{Commit, FileAction, FileChange};
use crate::error::{ParseError, ParseResult};
use crate::parser::{ParseOptions, Parser};

/// Parser for SVN XML log output.
///
/// This parser handles the `svn log --xml -v` format.
#[derive(Debug, Clone)]
pub struct SvnParser {
    options: ParseOptions,
}

impl SvnParser {
    /// Creates a new SVN XML parser with default options.
    #[must_use]
    pub fn new() -> Self {
        Self::with_options(ParseOptions::default())
    }

    /// Creates a parser with the specified options.
    #[must_use]
    pub fn with_options(options: ParseOptions) -> Self {
        Self { options }
    }

    /// Extracts text content between XML tags.
    fn extract_tag_content<'a>(xml: &'a str, tag: &str) -> Option<&'a str> {
        let open_tag = format!("<{tag}>");
        let close_tag = format!("</{tag}>");

        let start = xml.find(&open_tag)?;
        let content_start = start + open_tag.len();
        let end = xml[content_start..].find(&close_tag)?;

        Some(&xml[content_start..content_start + end])
    }

    /// Extracts an attribute value from an XML tag.
    fn extract_attribute<'a>(xml: &'a str, attr: &str) -> Option<&'a str> {
        let pattern = format!("{attr}=\"");
        let start = xml.find(&pattern)?;
        let value_start = start + pattern.len();
        let end = xml[value_start..].find('"')?;
        Some(&xml[value_start..value_start + end])
    }

    /// Parses an ISO 8601 date string to Unix timestamp.
    ///
    /// SVN uses format like: 2023-01-15T14:30:00.000000Z
    fn parse_svn_date(date_str: &str, line_number: usize) -> ParseResult<i64> {
        let date_str = date_str.trim();

        // Split at 'T' to get date and time parts
        let mut parts = date_str.split('T');
        let date_part = parts.next().ok_or_else(|| ParseError::InvalidTimestamp {
            line_number,
            value: date_str.to_string(),
        })?;
        let time_part = parts.next().ok_or_else(|| ParseError::InvalidTimestamp {
            line_number,
            value: date_str.to_string(),
        })?;

        let mut date_parts = date_part.split('-');
        let year: i64 = date_parts
            .next()
            .ok_or_else(|| ParseError::InvalidTimestamp {
                line_number,
                value: date_str.to_string(),
            })?
            .parse()
            .map_err(|_| ParseError::InvalidTimestamp {
                line_number,
                value: date_str.to_string(),
            })?;

        // Validate year is in reasonable range to prevent integer overflow
        // in days_since_epoch calculations (years_since * 365 can overflow i64
        // for years beyond ~2.5e16, and no valid SVN commit has year > 9999)
        if !(0..=9999).contains(&year) {
            return Err(ParseError::InvalidTimestamp {
                line_number,
                value: date_str.to_string(),
            });
        }

        let month: i64 = date_parts
            .next()
            .ok_or_else(|| ParseError::InvalidTimestamp {
                line_number,
                value: date_str.to_string(),
            })?
            .parse()
            .map_err(|_| ParseError::InvalidTimestamp {
                line_number,
                value: date_str.to_string(),
            })?;

        // Validate month is in valid range (1-12)
        if !(1..=12).contains(&month) {
            return Err(ParseError::InvalidTimestamp {
                line_number,
                value: date_str.to_string(),
            });
        }

        let day: i64 = date_parts
            .next()
            .ok_or_else(|| ParseError::InvalidTimestamp {
                line_number,
                value: date_str.to_string(),
            })?
            .parse()
            .map_err(|_| ParseError::InvalidTimestamp {
                line_number,
                value: date_str.to_string(),
            })?;

        // Validate day is in valid range (1-31)
        if !(1..=31).contains(&day) {
            return Err(ParseError::InvalidTimestamp {
                line_number,
                value: date_str.to_string(),
            });
        }

        // Parse time (ignore fractional seconds and timezone for simplicity)
        let time_str = time_part.split('.').next().unwrap_or(time_part);
        let time_str = time_str.trim_end_matches('Z');
        let mut time_parts = time_str.split(':');

        let (hour, minute, second) = {
            let h: i64 = time_parts.next().and_then(|s| s.parse().ok()).unwrap_or(0);
            let m: i64 = time_parts.next().and_then(|s| s.parse().ok()).unwrap_or(0);
            let s: i64 = time_parts.next().and_then(|s| s.parse().ok()).unwrap_or(0);
            (h, m, s)
        };

        // Validate time components to prevent arithmetic overflow in timestamp
        // calculation. Without this, values like hour=2562047788015216 cause
        // hour * 3600 to overflow i64 (discovered by libFuzzer).
        if !(0..=23).contains(&hour) || !(0..=59).contains(&minute) || !(0..=59).contains(&second) {
            return Err(ParseError::InvalidTimestamp {
                line_number,
                value: date_str.to_string(),
            });
        }

        // Simple Unix timestamp calculation
        // All components are now range-validated, so overflow is impossible:
        //   days_since_epoch: year in 0..=9999 → max |days| ≈ 2,932,896
        //   days * 86400: max ≈ 253,402,214,400 (fits i64)
        //   hour * 3600: max = 82,800; minute * 60: max = 3,540; second: max = 59
        let days_since_epoch = Self::days_since_epoch(year, month, day);
        let timestamp = days_since_epoch * 86400 + hour * 3600 + minute * 60 + second;

        Ok(timestamp)
    }

    /// Days before each month (cumulative, non-leap year).
    const DAYS_BEFORE_MONTH: [i64; 12] = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334];

    /// Calculates days since Unix epoch (1970-01-01).
    fn days_since_epoch(year: i64, month: i64, day: i64) -> i64 {
        // Simple days since epoch calculation
        // This is an approximation that works well for timestamps from ~1970 to ~2100

        // Days from years since 1970
        let years_since = year - 1970;
        let leap_years = (year - 1969) / 4 - (year - 1901) / 100 + (year - 1601) / 400;

        let mut days = years_since * 365 + leap_years;
        days += Self::DAYS_BEFORE_MONTH[(month - 1) as usize];
        days += day - 1;

        // Add extra day for leap year if past February
        if month > 2 && Self::is_leap_year(year) {
            days += 1;
        }

        days
    }

    /// Checks if a year is a leap year.
    fn is_leap_year(year: i64) -> bool {
        (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
    }

    /// Parses a single logentry block.
    fn parse_logentry(&self, revision: &str, content: &str) -> ParseResult<Option<Commit>> {
        // Extract author
        let author = Self::extract_tag_content(content, "author")
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .unwrap_or("unknown")
            .to_string();

        // Extract date
        let date_str = Self::extract_tag_content(content, "date").map_or("", str::trim);

        if date_str.is_empty() {
            return Ok(None);
        }

        let timestamp = Self::parse_svn_date(date_str, 0)?;

        // Check time range filter
        if !self.options.timestamp_in_range(timestamp) {
            return Ok(None);
        }

        // Extract file changes
        let files = self.parse_paths(content);

        // Skip empty commits if configured
        if files.is_empty() && self.options.skip_empty_commits {
            return Ok(None);
        }

        let commit = Commit::new(revision.to_string(), timestamp, author).with_files(files);

        Ok(Some(commit))
    }

    /// Parses path elements from the content.
    #[allow(clippy::unused_self)]
    fn parse_paths(&self, content: &str) -> Vec<FileChange> {
        let mut files = Vec::new();

        // Find each <path> element
        let mut search_start = 0;
        while let Some(path_start) = content[search_start..].find("<path") {
            let abs_start = search_start + path_start;

            // Find the closing >
            let Some(tag_end) = content[abs_start..].find('>') else {
                break;
            };
            let tag_end_abs = abs_start + tag_end;

            // Find the closing </path>
            let Some(close_start) = content[tag_end_abs..].find("</path>") else {
                break;
            };
            let close_abs = tag_end_abs + close_start;

            // Extract the tag attributes and content
            let tag = &content[abs_start..=tag_end_abs];
            let path_content = &content[tag_end_abs + 1..close_abs];

            // Extract action attribute
            let action = Self::extract_attribute(tag, "action")
                .and_then(|a| a.chars().next())
                .map_or(FileAction::Modify, |c| match c {
                    'A' => FileAction::Create,
                    'D' => FileAction::Delete,
                    _ => FileAction::Modify,
                });

            // Clean path
            let path = Self::strip_svn_prefix(path_content.trim());
            if !path.is_empty() {
                files.push(FileChange::new(path, action));
            }

            search_start = close_abs + 7; // Move past </path>
        }

        files
    }

    /// Strips common SVN path prefixes like /trunk/, /branches/xxx/.
    fn strip_svn_prefix(path: &str) -> &str {
        let path = path.trim_start_matches('/');

        // Strip trunk/
        if let Some(rest) = path.strip_prefix("trunk/") {
            return rest;
        }

        // Strip branches/xxx/
        if let Some(rest) = path.strip_prefix("branches/") {
            if let Some(idx) = rest.find('/') {
                return &rest[idx + 1..];
            }
        }

        // Strip tags/xxx/
        if let Some(rest) = path.strip_prefix("tags/") {
            if let Some(idx) = rest.find('/') {
                return &rest[idx + 1..];
            }
        }

        path
    }

    /// Extracts logentry blocks from the XML.
    #[allow(clippy::unused_self)]
    fn extract_log_entries<'a>(&self, input: &'a str) -> Vec<(&'a str, &'a str)> {
        let mut entries = Vec::new();
        let mut search_start = 0;

        while let Some(entry_start) = input[search_start..].find("<logentry") {
            let abs_start = search_start + entry_start;

            // Find closing </logentry> first to bound our search
            let Some(close_start) = input[abs_start..].find("</logentry>") else {
                break;
            };
            let close_abs = abs_start + close_start;

            // Find the closing '>' of the opening tag - must be before </logentry>
            let tag_search_region = &input[abs_start..close_abs];
            let Some(tag_end) = tag_search_region.find('>') else {
                // Malformed: no '>' in opening tag before closing tag
                search_start = close_abs + 11;
                continue;
            };

            // Validate tag_end is reasonable (not just finding '>' in content)
            let tag_content = &input[abs_start..abs_start + tag_end];

            // Skip if tag contains null bytes or other invalid characters
            if tag_content.bytes().any(|b| b == 0) {
                search_start = close_abs + 11;
                continue;
            }

            let revision = Self::extract_attribute(tag_content, "revision").unwrap_or("0");

            let content_start = abs_start + tag_end + 1;
            let content_end = close_abs;

            // Safety check: ensure valid slice bounds
            if content_start > content_end || content_end > input.len() {
                search_start = close_abs + 11;
                continue;
            }

            let content = &input[content_start..content_end];
            entries.push((revision, content));

            search_start = close_abs + 11; // Move past </logentry>
        }

        entries
    }
}

impl Default for SvnParser {
    fn default() -> Self {
        Self::new()
    }
}

/// Maximum input size the SVN parser will accept (64 MiB).
///
/// This prevents resource exhaustion from pathologically large inputs
/// that could cause quadratic scanning time in the tag-finding loops.
const MAX_SVN_INPUT_SIZE: usize = 64 * 1024 * 1024;

impl Parser for SvnParser {
    fn name(&self) -> &'static str {
        "svn"
    }

    fn parse_str(&self, input: &str) -> ParseResult<Vec<Commit>> {
        // Reject excessively large inputs to prevent resource exhaustion.
        if input.len() > MAX_SVN_INPUT_SIZE {
            return Err(ParseError::EmptyLog);
        }

        let mut commits = Vec::new();

        for (revision, content) in self.extract_log_entries(input) {
            if let Some(commit) = self.parse_logentry(revision, content)? {
                commits.push(commit);

                if self.options.limit_reached(commits.len()) {
                    break;
                }
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
        // Look for SVN XML log signature
        let input = input.trim();

        // Must start with XML declaration or <log> tag
        if !input.starts_with("<?xml") && !input.starts_with("<log") {
            return false;
        }

        // Must contain logentry elements
        input.contains("<logentry") && input.contains("revision=")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE_SVN_LOG: &str = r#"<?xml version="1.0" encoding="UTF-8"?>
<log>
<logentry revision="123">
<author>johndoe</author>
<date>2023-06-15T10:30:00.000000Z</date>
<paths>
<path action="M">/trunk/src/main.rs</path>
<path action="A">/trunk/src/lib.rs</path>
</paths>
<msg>Initial implementation</msg>
</logentry>
<logentry revision="124">
<author>janesmith</author>
<date>2023-06-16T14:45:30.123456Z</date>
<paths>
<path action="M">/trunk/src/main.rs</path>
<path action="D">/trunk/old/deprecated.txt</path>
</paths>
<msg>Cleanup old files</msg>
</logentry>
</log>"#;

    #[test]
    fn test_parse_svn_log() {
        let parser = SvnParser::new();
        let commits = parser.parse_str(SAMPLE_SVN_LOG).unwrap();

        assert_eq!(commits.len(), 2);

        // First commit (sorted by timestamp)
        assert_eq!(commits[0].hash, "123");
        assert_eq!(commits[0].author, "johndoe");
        assert_eq!(commits[0].files.len(), 2);

        // Second commit
        assert_eq!(commits[1].hash, "124");
        assert_eq!(commits[1].author, "janesmith");
        assert_eq!(commits[1].files.len(), 2);
    }

    #[test]
    fn test_file_actions() {
        let parser = SvnParser::new();
        let commits = parser.parse_str(SAMPLE_SVN_LOG).unwrap();

        // Check file actions in first commit
        let files = &commits[0].files;
        assert!(files.iter().any(|f| f.action == FileAction::Modify));
        assert!(files.iter().any(|f| f.action == FileAction::Create));

        // Check file actions in second commit
        let files = &commits[1].files;
        assert!(files.iter().any(|f| f.action == FileAction::Modify));
        assert!(files.iter().any(|f| f.action == FileAction::Delete));
    }

    #[test]
    fn test_strip_svn_prefix() {
        assert_eq!(
            SvnParser::strip_svn_prefix("/trunk/src/main.rs"),
            "src/main.rs"
        );
        assert_eq!(
            SvnParser::strip_svn_prefix("/branches/feature/src/main.rs"),
            "src/main.rs"
        );
        assert_eq!(
            SvnParser::strip_svn_prefix("/tags/v1.0/src/main.rs"),
            "src/main.rs"
        );
        assert_eq!(SvnParser::strip_svn_prefix("src/main.rs"), "src/main.rs");
    }

    #[test]
    fn test_parse_svn_date() {
        // 2023-06-15T10:30:00.000000Z
        let timestamp = SvnParser::parse_svn_date("2023-06-15T10:30:00.000000Z", 1).unwrap();
        assert!(timestamp > 0);

        // Should be around 2023 (after 2020 = 1577836800)
        assert!(timestamp > 1_577_836_800);
    }

    #[test]
    fn test_parse_svn_date_invalid() {
        assert!(SvnParser::parse_svn_date("invalid", 1).is_err());
        assert!(SvnParser::parse_svn_date("", 1).is_err());
    }

    #[test]
    fn test_parse_svn_date_invalid_month() {
        // Month 0 is invalid
        assert!(SvnParser::parse_svn_date("2023-00-15T10:30:00.000000Z", 1).is_err());
        // Month 13 is invalid
        assert!(SvnParser::parse_svn_date("2023-13-15T10:30:00.000000Z", 1).is_err());
        // Negative month (parsed as invalid)
        assert!(SvnParser::parse_svn_date("2023--1-15T10:30:00.000000Z", 1).is_err());
    }

    #[test]
    fn test_parse_svn_date_invalid_day() {
        // Day 0 is invalid
        assert!(SvnParser::parse_svn_date("2023-06-00T10:30:00.000000Z", 1).is_err());
        // Day 32 is invalid
        assert!(SvnParser::parse_svn_date("2023-06-32T10:30:00.000000Z", 1).is_err());
    }

    #[test]
    fn test_can_parse() {
        let parser = SvnParser::new();

        assert!(parser.can_parse(SAMPLE_SVN_LOG));
        assert!(parser
            .can_parse(r#"<?xml version="1.0"?><log><logentry revision="1"></logentry></log>"#));
        assert!(parser.can_parse(r#"<log><logentry revision="1"></logentry></log>"#));

        assert!(!parser.can_parse("commit abc123\nAuthor: Test\n"));
        assert!(!parser.can_parse("1234567890|John|A|file.txt"));
        assert!(!parser.can_parse("<html></html>"));
    }

    #[test]
    fn test_parser_name() {
        let parser = SvnParser::new();
        assert_eq!(parser.name(), "svn");
    }

    #[test]
    fn test_empty_log() {
        let parser = SvnParser::new();

        assert!(matches!(
            parser.parse_str(r#"<?xml version="1.0"?><log></log>"#),
            Err(ParseError::EmptyLog)
        ));
    }

    #[test]
    fn test_max_commits() {
        let log = r#"<?xml version="1.0"?>
<log>
<logentry revision="1">
<author>test</author>
<date>2023-01-01T00:00:00Z</date>
<paths><path action="A">/trunk/a.txt</path></paths>
</logentry>
<logentry revision="2">
<author>test</author>
<date>2023-01-02T00:00:00Z</date>
<paths><path action="A">/trunk/b.txt</path></paths>
</logentry>
<logentry revision="3">
<author>test</author>
<date>2023-01-03T00:00:00Z</date>
<paths><path action="A">/trunk/c.txt</path></paths>
</logentry>
</log>"#;

        let parser = SvnParser::with_options(ParseOptions::default().with_max_commits(2));
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 2);
    }

    #[test]
    fn test_empty_commit() {
        let log = r#"<?xml version="1.0"?>
<log>
<logentry revision="1">
<author>test</author>
<date>2023-01-01T00:00:00Z</date>
<paths></paths>
</logentry>
<logentry revision="2">
<author>test</author>
<date>2023-01-02T00:00:00Z</date>
<paths><path action="A">/trunk/file.txt</path></paths>
</logentry>
</log>"#;

        // Default: skip empty commits
        let parser = SvnParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);

        // Include empty commits
        let parser = SvnParser::with_options(ParseOptions {
            skip_empty_commits: false,
            ..Default::default()
        });
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 2);
    }

    #[test]
    fn test_no_author() {
        let log = r#"<?xml version="1.0"?>
<log>
<logentry revision="1">
<date>2023-01-01T00:00:00Z</date>
<paths><path action="A">/trunk/file.txt</path></paths>
</logentry>
</log>"#;

        let parser = SvnParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits[0].author, "unknown");
    }

    #[test]
    fn test_extract_tag_content() {
        let xml = "<author>johndoe</author>";
        assert_eq!(
            SvnParser::extract_tag_content(xml, "author"),
            Some("johndoe")
        );

        let xml = "<msg>Hello world</msg>";
        assert_eq!(
            SvnParser::extract_tag_content(xml, "msg"),
            Some("Hello world")
        );

        let xml = "<author></author>";
        assert_eq!(SvnParser::extract_tag_content(xml, "author"), Some(""));

        assert!(SvnParser::extract_tag_content(xml, "notfound").is_none());
    }

    #[test]
    fn test_extract_attribute() {
        let tag = r#"<path action="M">"#;
        assert_eq!(SvnParser::extract_attribute(tag, "action"), Some("M"));

        let tag = r#"<logentry revision="123">"#;
        assert_eq!(SvnParser::extract_attribute(tag, "revision"), Some("123"));

        assert!(SvnParser::extract_attribute(tag, "notfound").is_none());
    }

    #[test]
    fn test_days_since_epoch() {
        // 1970-01-01 should be 0
        assert_eq!(SvnParser::days_since_epoch(1970, 1, 1), 0);

        // 2000-01-01 should be positive
        let days_2000 = SvnParser::days_since_epoch(2000, 1, 1);
        assert!(days_2000 > 0);
        // Approximately 30 years * 365 days = 10950, with leap years ~10957
        assert!(days_2000 > 10000 && days_2000 < 12000);
    }

    // Regression tests for fuzzer-discovered issues

    #[test]
    fn test_malformed_logentry_with_null_bytes() {
        // Fuzzer crash input: <logentry=\0\0\0\0\0\0\0\0\0\0\0</logentry>
        // This caused a panic due to invalid slice bounds
        let parser = SvnParser::new();
        let malformed = "<logentry=\0\0\0\0\0\0\0\0\0\0\0</logentry>";

        // Should not panic, just return error or empty
        let result = parser.parse_str(malformed);
        assert!(result.is_err());
    }

    #[test]
    fn test_malformed_logentry_no_closing_bracket() {
        // <logentry without > before </logentry>
        let parser = SvnParser::new();
        let malformed = "<logentry revision=\"1\"</logentry>";

        // Should not panic
        let result = parser.parse_str(malformed);
        assert!(result.is_err());
    }

    #[test]
    fn test_malformed_logentry_reversed_brackets() {
        // Content end before content start scenario
        let parser = SvnParser::new();
        let malformed = "<logentry</logentry>";

        let result = parser.parse_str(malformed);
        assert!(result.is_err());
    }

    #[test]
    fn test_arbitrary_binary_in_log() {
        // Ensure parser handles arbitrary binary data gracefully
        let parser = SvnParser::new();
        let binary = "<log>\x00\x01\x02\x03</log>";

        let result = parser.parse_str(binary);
        assert!(result.is_err());
    }

    // ========================================================================
    // PHASE 2: Expert+ Edge Case Tests
    // ========================================================================

    #[test]
    fn test_svn_parse_basic_phase2() {
        // Simple test to verify basic parsing works
        let parser = SvnParser::new();
        let commits = parser.parse_str(SAMPLE_SVN_LOG).unwrap();
        assert_eq!(commits.len(), 2);
        assert_eq!(commits[0].author, "johndoe");
    }

    #[test]
    fn test_svn_action_create_in_sample() {
        // Verify that 'A' action parses to Create in sample log
        let parser = SvnParser::new();
        let commits = parser.parse_str(SAMPLE_SVN_LOG).unwrap();
        // Second file in first commit has action="A"
        assert!(commits[0]
            .files
            .iter()
            .any(|f| f.action == FileAction::Create));
    }

    #[test]
    fn test_svn_parse_properties_change() {
        // Property changes still count as modifications
        let log = r#"<?xml version="1.0"?>
<log>
<logentry revision="50">
<author>propchanger</author>
<date>2024-01-01T00:00:00.000000Z</date>
<paths>
<path action="M">/trunk/src/lib.rs</path>
</paths>
<msg>Update svn:ignore</msg>
</logentry>
</log>"#;

        let parser = SvnParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].files[0].action, FileAction::Modify);
    }

    #[test]
    fn test_svn_parse_unicode_author_phase2() {
        let log = r#"<?xml version="1.0" encoding="UTF-8"?>
<log>
<logentry revision="1">
<author>田中太郎</author>
<date>2024-01-01T00:00:00.000000Z</date>
<paths>
<path action="A">/trunk/file.txt</path>
</paths>
</logentry>
</log>"#;

        let parser = SvnParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits[0].author, "田中太郎");
    }

    #[test]
    fn test_svn_parse_empty_author_phase2() {
        let log = r#"<?xml version="1.0"?>
<log>
<logentry revision="1">
<author></author>
<date>2024-01-01T00:00:00.000000Z</date>
<paths>
<path action="A">/trunk/file.txt</path>
</paths>
</logentry>
</log>"#;

        let parser = SvnParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits[0].author, "unknown");
    }

    #[test]
    fn test_svn_is_leap_year() {
        // Verify leap year calculation
        assert!(SvnParser::is_leap_year(2000)); // Divisible by 400
        assert!(!SvnParser::is_leap_year(1900)); // Divisible by 100 but not 400
        assert!(SvnParser::is_leap_year(2024)); // Divisible by 4
        assert!(!SvnParser::is_leap_year(2023)); // Not divisible by 4
    }

    #[test]
    fn test_svn_parse_very_long_revision() {
        let log = r#"<?xml version="1.0"?>
<log>
<logentry revision="999999999">
<author>test</author>
<date>2024-01-01T00:00:00.000000Z</date>
<paths>
<path action="A">/trunk/file.txt</path>
</paths>
</logentry>
</log>"#;

        let parser = SvnParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits[0].hash, "999999999");
    }

    #[test]
    fn test_svn_parse_multiple_files() {
        // Test parsing multiple files in one commit
        let log = r#"<?xml version="1.0"?>
<log>
<logentry revision="1">
<author>multi</author>
<date>2024-01-01T00:00:00.000000Z</date>
<paths>
<path action="A">/trunk/file1.txt</path>
<path action="M">/trunk/file2.txt</path>
<path action="D">/trunk/file3.txt</path>
</paths>
</logentry>
</log>"#;

        let parser = SvnParser::new();
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits[0].files.len(), 3);
    }

    #[test]
    fn test_svn_strip_trunk_prefix() {
        assert_eq!(
            SvnParser::strip_svn_prefix("/trunk/src/main.rs"),
            "src/main.rs"
        );
        assert_eq!(
            SvnParser::strip_svn_prefix("trunk/src/main.rs"),
            "src/main.rs"
        );
    }

    #[test]
    fn test_svn_strip_branches_prefix() {
        assert_eq!(
            SvnParser::strip_svn_prefix("/branches/feature/src/main.rs"),
            "src/main.rs"
        );
    }

    #[test]
    fn test_svn_strip_tags_prefix() {
        assert_eq!(
            SvnParser::strip_svn_prefix("/tags/v1.0/src/main.rs"),
            "src/main.rs"
        );
    }

    #[test]
    fn test_svn_no_prefix_strip() {
        assert_eq!(SvnParser::strip_svn_prefix("src/main.rs"), "src/main.rs");
    }

    // ========================================================================
    // Regression tests for fuzzer-discovered crashes
    // ========================================================================

    #[test]
    fn test_fuzz_regression_large_year_overflow() {
        // Regression test for CI fuzzing crash (libFuzzer: deadly signal).
        // Dates with extremely large year values (e.g., 441111) caused integer
        // overflow in days_since_epoch() where `years_since * 365` overflows i64
        // in debug/fuzz builds. The fix validates year is in range 0..=9999.
        let parser = SvnParser::new();

        // Year 441111 - the approximate pattern from the fuzz corpus
        let log = r#"<?xml version="1.0"?>
<log>
<logentry revision="1">
<author>test</author>
<date>441111-02-03T04:05:06.000000Z</date>
<paths><path action="A">/trunk/file.txt</path></paths>
</logentry>
</log>"#;
        let result = parser.parse_str(log);
        assert!(result.is_err(), "year 441111 should be rejected");

        // Year far beyond i64 overflow threshold (~2.5e16)
        let log_huge = r#"<?xml version="1.0"?>
<log>
<logentry revision="1">
<author>test</author>
<date>99999999999999999-01-01T00:00:00.000000Z</date>
<paths><path action="A">/trunk/file.txt</path></paths>
</logentry>
</log>"#;
        let result = parser.parse_str(log_huge);
        assert!(result.is_err(), "huge year should be rejected");
    }

    #[test]
    fn test_fuzz_regression_negative_year() {
        // Negative years should also be rejected to prevent overflow
        let parser = SvnParser::new();
        let log = r#"<?xml version="1.0"?>
<log>
<logentry revision="1">
<author>test</author>
<date>-9999999-01-01T00:00:00.000000Z</date>
<paths><path action="A">/trunk/file.txt</path></paths>
</logentry>
</log>"#;
        let result = parser.parse_str(log);
        assert!(result.is_err(), "negative year should be rejected");
    }

    #[test]
    fn test_fuzz_regression_year_boundary_valid() {
        // Year 9999 should still be accepted (maximum valid year)
        let parser = SvnParser::new();
        let log = r#"<?xml version="1.0"?>
<log>
<logentry revision="1">
<author>test</author>
<date>9999-12-31T23:59:59.000000Z</date>
<paths><path action="A">/trunk/file.txt</path></paths>
</logentry>
</log>"#;
        let result = parser.parse_str(log);
        assert!(result.is_ok(), "year 9999 should be accepted");
    }

    #[test]
    fn test_fuzz_regression_year_boundary_invalid() {
        // Year 10000 should be rejected (just past boundary)
        let parser = SvnParser::new();
        let log = r#"<?xml version="1.0"?>
<log>
<logentry revision="1">
<author>test</author>
<date>10000-01-01T00:00:00.000000Z</date>
<paths><path action="A">/trunk/file.txt</path></paths>
</logentry>
</log>"#;
        let result = parser.parse_str(log);
        assert!(result.is_err(), "year 10000 should be rejected");
    }

    #[test]
    fn test_fuzz_regression_malformed_date_with_garbage() {
        // Approximation of the actual fuzz corpus that caused the crash:
        // Malformed XML with garbage bytes and embedded date-like patterns
        let parser = SvnParser::new();
        let malformed = "<log><logentry revision=\"1\">\
            <author>x</author>\
            <date>441111-2-3-\x004T1:11:1\x00</date>\
            <paths><path action=\"A\">/trunk/f</path></paths>\
            </logentry></log>";
        let result = parser.parse_str(malformed);
        // Should not panic - error is acceptable
        assert!(result.is_err());
    }

    // =========================================================================
    // Mutation Testing: Kill missed mutants
    // =========================================================================

    /// Kill mutant: `days_since_epoch` arithmetic
    /// Verify exact day counts against known Unix timestamps.
    #[test]
    fn test_svn_days_since_epoch_exact() {
        // 1970-01-01 = 0
        assert_eq!(SvnParser::days_since_epoch(1970, 1, 1), 0);
        // 1970-01-02 = 1
        assert_eq!(SvnParser::days_since_epoch(1970, 1, 2), 1);
        // 1970-02-01 = 31
        assert_eq!(SvnParser::days_since_epoch(1970, 2, 1), 31);
        // 1970-03-01 = 59
        assert_eq!(SvnParser::days_since_epoch(1970, 3, 1), 59);
        // 1971-01-01 = 365
        assert_eq!(SvnParser::days_since_epoch(1971, 1, 1), 365);
        // 1972-01-01 = 730
        assert_eq!(SvnParser::days_since_epoch(1972, 1, 1), 730);
        // 1972-03-01 = 790 (leap year: Feb has 29 days, month>2 adds 1)
        assert_eq!(SvnParser::days_since_epoch(1972, 3, 1), 790);
        // 2024-01-01 = 19723 (known from Unix timestamp 1704067200/86400)
        assert_eq!(SvnParser::days_since_epoch(2024, 1, 1), 19723);
    }

    /// Kill mutant: `days_since_epoch` `leap_years` formula arithmetic
    /// The formula: (year-1969)/4 - (year-1901)/100 + (year-1601)/400
    #[test]
    fn test_svn_days_since_epoch_leap_formula() {
        // 2000-03-01: Leap year (divisible by 400)
        // 2000-01-01 = days
        let d2000 = SvnParser::days_since_epoch(2000, 1, 1);
        let d2001 = SvnParser::days_since_epoch(2001, 1, 1);
        // 2000 is leap → 366 days gap
        assert_eq!(d2001 - d2000, 366);

        // 1900-03-01: NOT leap (divisible by 100 but not 400)
        let d1900 = SvnParser::days_since_epoch(1900, 1, 1);
        let d1901 = SvnParser::days_since_epoch(1901, 1, 1);
        // 1900 is not leap → 365 days gap
        assert_eq!(d1901 - d1900, 365);
    }

    /// Kill mutant: `parse_svn_date` arithmetic (*→+, *→/, +→-, +→*)
    /// Verify exact timestamp for a known date with specific time.
    #[test]
    fn test_svn_parse_date_time_arithmetic() {
        // 1970-01-01T01:02:03.000000Z → 0 days + 1*3600 + 2*60 + 3 = 3723
        let ts = SvnParser::parse_svn_date("1970-01-01T01:02:03.000000Z", 1).unwrap();
        assert_eq!(ts, 3723);

        // 1970-01-02T00:00:00.000000Z → 1 day * 86400 = 86400
        let ts = SvnParser::parse_svn_date("1970-01-02T00:00:00.000000Z", 1).unwrap();
        assert_eq!(ts, 86400);

        // 1970-01-01T10:00:00.000000Z → 10*3600 = 36000
        let ts = SvnParser::parse_svn_date("1970-01-01T10:00:00.000000Z", 1).unwrap();
        assert_eq!(ts, 36000);
    }

    /// Kill mutant: `with_options` → Default
    #[test]
    fn test_svn_with_options_preserved() {
        let opts = ParseOptions::default().with_max_commits(1);
        let parser = SvnParser::with_options(opts);
        let log = r#"<?xml version="1.0"?>
<log>
<logentry revision="1">
<author>alice</author>
<date>2024-01-01T00:00:00.000000Z</date>
<paths><path action="A">/trunk/a.rs</path></paths>
</logentry>
<logentry revision="2">
<author>bob</author>
<date>2024-01-02T00:00:00.000000Z</date>
<paths><path action="M">/trunk/b.rs</path></paths>
</logentry>
</log>"#;
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(commits.len(), 1, "with_max_commits(1) should limit to 1");
    }

    /// Kill mutant: `can_parse` &&→|| on logentry + revision check
    #[test]
    fn test_svn_can_parse_partial_match() {
        let parser = SvnParser::new();
        // Has <logentry but no revision=
        assert!(!parser.can_parse("<?xml version=\"1.0\"?><log><logentry></logentry></log>"));
        // Has revision= but no <logentry
        assert!(!parser.can_parse("<?xml version=\"1.0\"?><log>revision=\"1\"</log>"));
        // Neither starts with <?xml nor <log
        assert!(!parser.can_parse("<data><logentry revision=\"1\"></logentry></data>"));
        // Valid
        assert!(parser
            .can_parse("<?xml version=\"1.0\"?><log><logentry revision=\"1\"></logentry></log>"));
    }

    /// Kill mutant: `extract_log_entries` `content_start` > `content_end` check
    #[test]
    fn test_svn_extract_log_entries_bounds() {
        let parser = SvnParser::new();
        // Malformed: closing tag immediately after opening
        let result = parser
            .parse_str("<?xml version=\"1.0\"?><log><logentry revision=\"1\"></logentry></log>");
        // Should either parse empty or error, not panic
        assert!(result.is_err() || result.unwrap().is_empty());
    }

    /// Kill mutant: `parse_svn_date` month/day validation boundaries
    #[test]
    fn test_svn_parse_date_invalid_month_day() {
        // Month 0
        assert!(SvnParser::parse_svn_date("2024-00-15T00:00:00.000000Z", 1).is_err());
        // Month 13
        assert!(SvnParser::parse_svn_date("2024-13-15T00:00:00.000000Z", 1).is_err());
        // Day 0
        assert!(SvnParser::parse_svn_date("2024-06-00T00:00:00.000000Z", 1).is_err());
        // Day 32
        assert!(SvnParser::parse_svn_date("2024-06-32T00:00:00.000000Z", 1).is_err());
    }

    // =========================================================================
    // Regression tests for fuzzer crash: time component overflow
    // =========================================================================

    #[test]
    fn test_fuzz_regression_hour_overflow() {
        // Regression: libFuzzer deadly signal (crash-717304ab4d85f8753ce4ae81b446ba84e508a88b).
        // Garbage input where the time portion of a date parses as a large i64,
        // causing `hour * 3600` to overflow with overflow-checks enabled.
        // The fix validates h/m/s are in valid ranges before arithmetic.
        assert!(
            SvnParser::parse_svn_date("2024-01-01T2562047788015216:00:00.000000Z", 1).is_err(),
            "huge hour should be rejected (would overflow hour * 3600)"
        );
        assert!(
            SvnParser::parse_svn_date("2024-01-01T24:00:00.000000Z", 1).is_err(),
            "hour 24 should be rejected"
        );
        assert!(
            SvnParser::parse_svn_date("2024-01-01T00:60:00.000000Z", 1).is_err(),
            "minute 60 should be rejected"
        );
        assert!(
            SvnParser::parse_svn_date("2024-01-01T00:00:60.000000Z", 1).is_err(),
            "second 60 should be rejected"
        );
        // Negative time values (parsed from garbage)
        assert!(
            SvnParser::parse_svn_date("2024-01-01T-1:00:00.000000Z", 1).is_err(),
            "negative hour should be rejected"
        );
    }

    #[test]
    fn test_fuzz_regression_valid_time_boundaries() {
        // Boundary values that should still be accepted
        assert!(
            SvnParser::parse_svn_date("2024-01-01T23:59:59.000000Z", 1).is_ok(),
            "23:59:59 should be accepted"
        );
        assert!(
            SvnParser::parse_svn_date("2024-01-01T00:00:00.000000Z", 1).is_ok(),
            "00:00:00 should be accepted"
        );
    }

    #[test]
    fn test_fuzz_regression_crash_717304ab_pattern() {
        // Approximation of the actual crash artifact pattern:
        // Multiple malformed logentry blocks with garbage date content where
        // the time portion could parse as a huge i64.
        let parser = SvnParser::new();
        let malformed = concat!(
            "<logentry-82<\x07>\x13kdate>\x07k",
            "<date-82<\x07>\x13kdate>\x07k",
            "<date>22-2-2-5en\x01",
            "T000000000000000000000000000000000000000000",
            "............0000000000000000000",
            "</date>",
            "<logentry></logentry>",
            "<logent</logentry>",
        );
        // Must not panic regardless of parse result
        let _ = parser.parse_str(malformed);
    }

    /// Kill mutant: `parse_paths` `search_start` advancement
    /// Multiple path elements must all be parsed.
    #[test]
    fn test_svn_parse_paths_multiple() {
        let parser = SvnParser::new();
        let log = r#"<?xml version="1.0"?>
<log>
<logentry revision="1">
<author>multi</author>
<date>2024-01-01T00:00:00.000000Z</date>
<paths>
<path action="A">/trunk/file1.rs</path>
<path action="M">/trunk/file2.rs</path>
<path action="D">/trunk/file3.rs</path>
<path action="A">/trunk/file4.rs</path>
<path action="M">/trunk/file5.rs</path>
</paths>
</logentry>
</log>"#;
        let commits = parser.parse_str(log).unwrap();
        assert_eq!(
            commits[0].files.len(),
            5,
            "All 5 path elements should be parsed"
        );
    }
}
