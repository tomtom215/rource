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
        let parts: Vec<&str> = date_str.split('T').collect();
        if parts.len() != 2 {
            return Err(ParseError::InvalidTimestamp {
                line_number,
                value: date_str.to_string(),
            });
        }

        let date_parts: Vec<&str> = parts[0].split('-').collect();
        if date_parts.len() != 3 {
            return Err(ParseError::InvalidTimestamp {
                line_number,
                value: date_str.to_string(),
            });
        }

        let year: i64 = date_parts[0].parse().map_err(|_| ParseError::InvalidTimestamp {
            line_number,
            value: date_str.to_string(),
        })?;

        let month: i64 = date_parts[1].parse().map_err(|_| ParseError::InvalidTimestamp {
            line_number,
            value: date_str.to_string(),
        })?;

        let day: i64 = date_parts[2].parse().map_err(|_| ParseError::InvalidTimestamp {
            line_number,
            value: date_str.to_string(),
        })?;

        // Parse time (ignore fractional seconds and timezone for simplicity)
        let time_str = parts[1].split('.').next().unwrap_or(parts[1]);
        let time_str = time_str.trim_end_matches('Z');
        let time_parts: Vec<&str> = time_str.split(':').collect();

        let (hour, minute, second) = if time_parts.len() >= 3 {
            let h: i64 = time_parts[0].parse().unwrap_or(0);
            let m: i64 = time_parts[1].parse().unwrap_or(0);
            let s: i64 = time_parts[2].parse().unwrap_or(0);
            (h, m, s)
        } else {
            (0, 0, 0)
        };

        // Simple Unix timestamp calculation
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
        let date_str = Self::extract_tag_content(content, "date")
            .map_or("", str::trim);

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

            // Find revision attribute
            let Some(tag_end) = input[abs_start..].find('>') else {
                break;
            };
            let tag_content = &input[abs_start..abs_start + tag_end];
            let revision = Self::extract_attribute(tag_content, "revision").unwrap_or("0");

            // Find closing </logentry>
            let Some(close_start) = input[abs_start..].find("</logentry>") else {
                break;
            };
            let content_start = abs_start + tag_end + 1;
            let content_end = abs_start + close_start;

            let content = &input[content_start..content_end];
            entries.push((revision, content));

            search_start = abs_start + close_start + 11; // Move past </logentry>
        }

        entries
    }
}

impl Default for SvnParser {
    fn default() -> Self {
        Self::new()
    }
}

impl Parser for SvnParser {
    fn name(&self) -> &'static str {
        "svn"
    }

    fn parse_str(&self, input: &str) -> ParseResult<Vec<Commit>> {
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
        assert_eq!(SvnParser::strip_svn_prefix("/trunk/src/main.rs"), "src/main.rs");
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
    fn test_can_parse() {
        let parser = SvnParser::new();

        assert!(parser.can_parse(SAMPLE_SVN_LOG));
        assert!(parser.can_parse(r#"<?xml version="1.0"?><log><logentry revision="1"></logentry></log>"#));
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
        assert_eq!(SvnParser::extract_tag_content(xml, "author"), Some("johndoe"));

        let xml = "<msg>Hello world</msg>";
        assert_eq!(SvnParser::extract_tag_content(xml, "msg"), Some("Hello world"));

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
}
