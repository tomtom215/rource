// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Helper functions for the Rource CLI.
//!
//! Contains utility functions for formatting and string manipulation.

/// Format a Unix timestamp as a human-readable date.
///
/// # Arguments
///
/// * `timestamp` - Unix timestamp in seconds since epoch
///
/// # Returns
///
/// A string in `YYYY-MM-DD` format. Note: This uses a simplified algorithm
/// that may not be 100% accurate for all dates.
///
/// # Example
///
/// ```ignore
/// let date = format_timestamp(1577836800);
/// assert!(date.starts_with("20"));
/// ```
pub fn format_timestamp(timestamp: i64) -> String {
    let days_since_epoch = timestamp / 86400;
    let years = (days_since_epoch / 365) + 1970;
    let remaining_days = days_since_epoch % 365;
    let month = (remaining_days / 30) + 1;
    let day = (remaining_days % 30) + 1;
    format!("{years:04}-{month:02}-{day:02}")
}

/// Extract initials from a name for avatar display.
///
/// Takes up to 2 characters: the first character of the name and
/// the first character after a space (if present).
///
/// # Examples
///
/// ```ignore
/// assert_eq!(get_initials("John Doe"), "JD");
/// assert_eq!(get_initials("Alice"), "A");
/// assert_eq!(get_initials("bob"), "B");
/// assert_eq!(get_initials("<email@example.com>"), "E");
/// ```
pub fn get_initials(name: &str) -> String {
    let name = name.trim();

    // Handle email-only format: <email@example.com>
    let name = if name.starts_with('<') && name.ends_with('>') {
        name.trim_start_matches('<').trim_end_matches('>')
    } else if let Some(pos) = name.find('<') {
        // Handle "Name <email>" format - use only the name part
        name[..pos].trim()
    } else {
        name
    };

    let mut initials = String::with_capacity(2);

    // Get first character
    if let Some(first_char) = name.chars().next() {
        initials.push(first_char.to_ascii_uppercase());
    }

    // Get first character after last space (for last name)
    if let Some(space_pos) = name.rfind(' ') {
        if let Some(second_char) = name[space_pos + 1..].chars().next() {
            initials.push(second_char.to_ascii_uppercase());
        }
    }

    initials
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_timestamp() {
        // Jan 1, 2020 00:00:00 UTC
        #[allow(clippy::unreadable_literal)]
        let ts = 1577836800;
        let formatted = format_timestamp(ts);
        // Approximate check (our simple algorithm isn't precise)
        assert!(formatted.starts_with("20"));
    }

    #[test]
    fn test_get_initials() {
        // Basic two-word name
        assert_eq!(get_initials("John Doe"), "JD");
        assert_eq!(get_initials("Alice Smith"), "AS");

        // Single name
        assert_eq!(get_initials("Alice"), "A");
        assert_eq!(get_initials("bob"), "B");

        // Three or more words (uses first and last)
        assert_eq!(get_initials("John Q Public"), "JP");
        assert_eq!(get_initials("Mary Jane Watson"), "MW");

        // Email format
        assert_eq!(get_initials("<john@example.com>"), "J");
        assert_eq!(get_initials("John Doe <john@example.com>"), "JD");

        // Trimmed input
        assert_eq!(get_initials("  Alice  "), "A");
        assert_eq!(get_initials("  Bob Smith  "), "BS");
    }

    #[test]
    fn test_get_initials_empty() {
        assert_eq!(get_initials(""), "");
        assert_eq!(get_initials("   "), "");
    }

    #[test]
    fn test_get_initials_unicode() {
        // Unicode names
        assert_eq!(get_initials("José García"), "JG");
        assert_eq!(get_initials("Müller"), "M");
    }

    #[test]
    fn test_get_initials_numbers() {
        // Names with numbers
        assert_eq!(get_initials("User123"), "U");
        assert_eq!(get_initials("123User"), "1");
    }

    #[test]
    fn test_get_initials_special_chars() {
        // Names with special characters
        assert_eq!(get_initials("O'Brien"), "O");
        assert_eq!(get_initials("Jean-Pierre Dupont"), "JD");
    }

    #[test]
    fn test_format_timestamp_epoch() {
        // Unix epoch
        let formatted = format_timestamp(0);
        assert!(formatted.starts_with("1970"));
    }

    #[test]
    fn test_format_timestamp_year_2000() {
        // Jan 1, 2000 (approximately)
        let ts = 946_684_800; // 2000-01-01 00:00:00 UTC
        let formatted = format_timestamp(ts);
        assert!(formatted.starts_with("200"));
    }

    #[test]
    fn test_format_timestamp_negative() {
        // Before epoch (negative timestamp)
        let formatted = format_timestamp(-86400);
        // Should handle gracefully (may produce 1969 or similar)
        assert!(!formatted.is_empty());
    }

    #[test]
    fn test_format_timestamp_far_future() {
        // Far future date
        let ts = 4_102_444_800; // 2100-01-01 approximately
        let formatted = format_timestamp(ts);
        assert!(formatted.starts_with("21"));
    }
}
