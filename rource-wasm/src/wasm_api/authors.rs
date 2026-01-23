// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Author information and color APIs.
//!
//! This module provides methods to query author/contributor data:
//! - List of all authors with commit counts
//! - Author color lookup by name

use std::fmt::Write as FmtWrite;

use wasm_bindgen::prelude::*;

use rource_core::scene::User;
use rource_math::Color;

use crate::Rource;

// ============================================================================
// Helper Functions (testable without Rource instance)
// ============================================================================

/// Escapes a string for use in JSON.
///
/// Escapes backslashes and double quotes.
///
/// # Arguments
/// * `s` - The string to escape
///
/// # Returns
/// JSON-safe escaped string.
#[inline]
#[must_use]
pub fn escape_json_string(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

/// Formats a Color as a hex string.
///
/// # Arguments
/// * `color` - The color to format
///
/// # Returns
/// Hex color string like "#e94560".
#[inline]
#[must_use]
pub fn color_to_hex(color: &Color) -> String {
    let r = (color.r * 255.0) as u8;
    let g = (color.g * 255.0) as u8;
    let b = (color.b * 255.0) as u8;
    format!("#{r:02x}{g:02x}{b:02x}")
}

/// Formats a single author entry as a JSON object.
///
/// # Arguments
/// * `name` - Author name
/// * `color` - Author color
/// * `commits` - Number of commits
///
/// # Returns
/// JSON object string.
#[must_use]
pub fn format_author_json(name: &str, color: &Color, commits: usize) -> String {
    let escaped_name = escape_json_string(name);
    let hex_color = color_to_hex(color);
    format!(r#"{{"name":"{escaped_name}","color":"{hex_color}","commits":{commits}}}"#)
}

// ============================================================================
// Author Information API
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Returns author data as a JSON string array.
    ///
    /// Iterates over all commits to get complete author statistics,
    /// not just users currently visible in the scene.
    ///
    /// # Returns
    /// JSON array of author objects:
    /// ```json
    /// [
    ///   {"name": "Alice", "color": "#e94560", "commits": 42},
    ///   {"name": "Bob", "color": "#58a6ff", "commits": 17}
    /// ]
    /// ```
    ///
    /// Authors are sorted by commit count (descending).
    #[wasm_bindgen(js_name = getAuthors)]
    pub fn get_authors(&self) -> String {
        use std::collections::HashMap;

        // Count commits per author from ALL commits
        let mut author_counts: HashMap<&str, usize> = HashMap::new();
        for commit in &self.commits {
            *author_counts.entry(commit.author.as_str()).or_insert(0) += 1;
        }

        // Build authors list with colors derived from names
        let mut authors: Vec<(&str, Color, usize)> = author_counts
            .into_iter()
            .map(|(name, count)| {
                let color = User::color_from_name(name);
                (name, color, count)
            })
            .collect();

        // Sort by commit count descending
        authors.sort_by(|a, b| b.2.cmp(&a.2));

        // Build JSON array
        let mut json = String::from("[");
        for (i, (name, color, commits)) in authors.iter().enumerate() {
            if i > 0 {
                json.push(',');
            }
            let r = (color.r * 255.0) as u8;
            let g = (color.g * 255.0) as u8;
            let b = (color.b * 255.0) as u8;
            // Escape special characters in names for valid JSON
            let escaped_name = name.replace('\\', "\\\\").replace('"', "\\\"");
            // Note: We build the hex color separately to avoid format_args escaping issues
            let hex_color = format!("#{r:02x}{g:02x}{b:02x}");
            let _ = FmtWrite::write_fmt(
                &mut json,
                format_args!(
                    r#"{{"name":"{escaped_name}","color":"{hex_color}","commits":{commits}}}"#
                ),
            );
        }
        json.push(']');
        json
    }

    /// Returns the color for a given author name as a hex string.
    ///
    /// Colors are deterministically generated from the author name,
    /// so the same name always produces the same color.
    ///
    /// # Returns
    /// Hex color string like "#e94560"
    #[wasm_bindgen(js_name = getAuthorColor)]
    pub fn get_author_color(&self, name: &str) -> String {
        let color = User::color_from_name(name);
        format!(
            "#{:02x}{:02x}{:02x}",
            (color.r * 255.0) as u8,
            (color.g * 255.0) as u8,
            (color.b * 255.0) as u8
        )
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // JSON Escaping Tests
    // ========================================================================

    #[test]
    fn test_escape_json_string_no_escape_needed() {
        assert_eq!(escape_json_string("Alice"), "Alice");
        assert_eq!(escape_json_string("John Doe"), "John Doe");
        assert_eq!(escape_json_string("user123"), "user123");
    }

    #[test]
    fn test_escape_json_string_quotes() {
        assert_eq!(escape_json_string(r#"Say "hello""#), r#"Say \"hello\""#);
        // Two quotes becomes two escaped quotes
        assert_eq!(escape_json_string(r#""""#), r#"\"\""#);
    }

    #[test]
    fn test_escape_json_string_backslashes() {
        assert_eq!(escape_json_string(r"path\to\file"), r"path\\to\\file");
        assert_eq!(escape_json_string(r"\\server\share"), r"\\\\server\\share");
    }

    #[test]
    fn test_escape_json_string_combined() {
        assert_eq!(
            escape_json_string(r#"He said "Hello\" to me"#),
            r#"He said \"Hello\\\" to me"#
        );
    }

    #[test]
    fn test_escape_json_string_empty() {
        assert_eq!(escape_json_string(""), "");
    }

    // ========================================================================
    // Color to Hex Tests
    // ========================================================================

    #[test]
    fn test_color_to_hex_red() {
        let red = Color::new(1.0, 0.0, 0.0, 1.0);
        assert_eq!(color_to_hex(&red), "#ff0000");
    }

    #[test]
    fn test_color_to_hex_green() {
        let green = Color::new(0.0, 1.0, 0.0, 1.0);
        assert_eq!(color_to_hex(&green), "#00ff00");
    }

    #[test]
    fn test_color_to_hex_blue() {
        let blue = Color::new(0.0, 0.0, 1.0, 1.0);
        assert_eq!(color_to_hex(&blue), "#0000ff");
    }

    #[test]
    fn test_color_to_hex_white() {
        let white = Color::new(1.0, 1.0, 1.0, 1.0);
        assert_eq!(color_to_hex(&white), "#ffffff");
    }

    #[test]
    fn test_color_to_hex_black() {
        let black = Color::new(0.0, 0.0, 0.0, 1.0);
        assert_eq!(color_to_hex(&black), "#000000");
    }

    #[test]
    fn test_color_to_hex_mixed() {
        // 128/255 = 0.502 approximately
        let gray = Color::new(0.5, 0.5, 0.5, 1.0);
        let hex = color_to_hex(&gray);
        // Should be close to #7f7f7f (127)
        assert!(hex.starts_with("#"));
        assert_eq!(hex.len(), 7);
    }

    // ========================================================================
    // Author JSON Formatting Tests
    // ========================================================================

    #[test]
    fn test_format_author_json_simple() {
        let color = Color::new(1.0, 0.0, 0.0, 1.0);
        let json = format_author_json("Alice", &color, 42);
        assert_eq!(json, r##"{"name":"Alice","color":"#ff0000","commits":42}"##);
    }

    #[test]
    fn test_format_author_json_with_spaces() {
        let color = Color::new(0.0, 1.0, 0.0, 1.0);
        let json = format_author_json("John Doe", &color, 17);
        assert_eq!(json, r##"{"name":"John Doe","color":"#00ff00","commits":17}"##);
    }

    #[test]
    fn test_format_author_json_with_special_chars() {
        let color = Color::new(0.0, 0.0, 1.0, 1.0);
        let json = format_author_json(r#"User "Nickname""#, &color, 5);
        assert_eq!(
            json,
            r##"{"name":"User \"Nickname\"","color":"#0000ff","commits":5}"##
        );
    }

    #[test]
    fn test_format_author_json_zero_commits() {
        let color = Color::new(0.5, 0.5, 0.5, 1.0);
        let json = format_author_json("Nobody", &color, 0);
        assert!(json.contains(r#""commits":0"#));
    }

    #[test]
    fn test_format_author_json_large_commit_count() {
        let color = Color::new(1.0, 1.0, 0.0, 1.0);
        let json = format_author_json("Prolific Author", &color, 999999);
        assert!(json.contains(r#""commits":999999"#));
    }

    // ========================================================================
    // User Color Determinism Tests
    // ========================================================================

    #[test]
    fn test_user_color_deterministic() {
        // Same name should always produce same color
        let color1 = User::color_from_name("Alice");
        let color2 = User::color_from_name("Alice");
        assert!((color1.r - color2.r).abs() < 0.001);
        assert!((color1.g - color2.g).abs() < 0.001);
        assert!((color1.b - color2.b).abs() < 0.001);
    }

    #[test]
    fn test_user_color_different_names() {
        // Different names should (usually) produce different colors
        let alice = User::color_from_name("Alice");
        let bob = User::color_from_name("Bob");
        // At least one component should differ
        let differs = (alice.r - bob.r).abs() > 0.01
            || (alice.g - bob.g).abs() > 0.01
            || (alice.b - bob.b).abs() > 0.01;
        assert!(differs, "Different names should produce different colors");
    }
}
