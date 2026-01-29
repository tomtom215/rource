// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Hover detection and entity info for tooltips.
//!
//! This module provides methods for detecting which entity is under the mouse
//! cursor and returning information suitable for tooltip display.

use wasm_bindgen::prelude::*;

use rource_math::Vec2;

use crate::interaction::{hit_test_directory, hit_test_file, hit_test_user, ENTITY_HIT_RADIUS};
use crate::Rource;

// ============================================================================
// Hover Detection
// ============================================================================

/// Information about an entity under the cursor.
///
/// Note: This struct is kept for backward compatibility and tests.
/// Production code uses `build_hover_json` for zero-allocation.
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct HoverInfo {
    /// Entity type: "file", "user", or "directory".
    pub entity_type: String,
    /// Entity name (filename, username, or directory name).
    pub name: String,
    /// Full path for files/directories, empty for users.
    pub path: String,
    /// File extension (files only), empty otherwise.
    pub extension: String,
    /// Hex color string (e.g., "#FF5500").
    pub color: String,
    /// Entity radius in world units.
    pub radius: f32,
}

impl HoverInfo {
    /// Converts to JSON string for JavaScript consumption.
    /// Uses pre-sized buffer to minimize allocation overhead.
    #[allow(dead_code)]
    pub fn to_json(&self) -> String {
        use std::fmt::Write;
        // Estimate capacity: fixed JSON overhead (~70 bytes) + field lengths
        let capacity = 70
            + self.entity_type.len()
            + self.name.len()
            + self.path.len()
            + self.extension.len()
            + self.color.len()
            + 10;
        let mut json = String::with_capacity(capacity);
        let _ = write!(
            json,
            r#"{{"entityType":"{}","name":"{}","path":"{}","extension":"{}","color":"{}","radius":{}}}"#,
            escape_json(&self.entity_type),
            escape_json(&self.name),
            escape_json(&self.path),
            escape_json(&self.extension),
            escape_json(&self.color),
            self.radius
        );
        json
    }
}

/// Escapes a string for safe JSON inclusion (allocating version).
/// Single-pass implementation to avoid multiple intermediate String allocations.
///
/// Note: This function is kept for backward compatibility and tests.
/// Production code uses `escape_json_into` for zero-allocation.
#[allow(dead_code)]
fn escape_json(s: &str) -> String {
    // Fast path: if no escaping needed, return as-is (no allocation beyond to_string)
    if !needs_json_escaping(s) {
        return s.to_string();
    }

    // Slow path: build escaped string in single pass
    let mut result = String::with_capacity(s.len() + 8);
    escape_json_into(s, &mut result);
    result
}

/// Checks if a string needs JSON escaping.
#[inline]
fn needs_json_escaping(s: &str) -> bool {
    s.bytes()
        .any(|b| b == b'\\' || b == b'"' || b == b'\n' || b == b'\r' || b == b'\t')
}

/// Escapes a string for safe JSON inclusion into an existing buffer.
///
/// Zero-allocation version: writes directly to the provided buffer.
/// Fast path: if no escaping needed, uses `push_str` directly.
#[inline]
fn escape_json_into(s: &str, out: &mut String) {
    if !needs_json_escaping(s) {
        out.push_str(s);
        return;
    }

    // Slow path: escape character by character
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(c),
        }
    }
}

/// Converts a Color to a hex string.
/// Uses pre-sized buffer to minimize allocation overhead.
///
/// Note: This function is kept for backward compatibility and tests.
/// Production code uses `write_color_hex_into` for zero-allocation.
#[allow(dead_code)]
fn color_to_hex(color: rource_math::Color) -> String {
    use std::fmt::Write;
    // Pre-allocate exact size: "#RRGGBB" = 7 bytes
    let mut result = String::with_capacity(7);
    let _ = write!(
        result,
        "#{:02X}{:02X}{:02X}",
        (color.r * 255.0) as u8,
        (color.g * 255.0) as u8,
        (color.b * 255.0) as u8
    );
    result
}

/// Writes a color as hex directly into a buffer (zero-allocation).
#[inline]
fn write_color_hex_into(color: rource_math::Color, out: &mut String) {
    use std::fmt::Write;
    let _ = write!(
        out,
        "#{:02X}{:02X}{:02X}",
        (color.r * 255.0) as u8,
        (color.g * 255.0) as u8,
        (color.b * 255.0) as u8
    );
}

/// Builds hover JSON directly without intermediate allocations.
///
/// This is the zero-allocation version that writes all fields directly
/// to a single pre-sized buffer, avoiding the `HoverInfo` struct and
/// multiple intermediate `String` allocations.
///
/// # Arguments
///
/// * `entity_type` - "file", "user", or "directory"
/// * `name` - Entity name
/// * `path` - File/directory path (empty for users)
/// * `extension` - File extension (empty for non-files)
/// * `color` - Entity color
/// * `radius` - Entity radius
///
/// # Returns
///
/// JSON string ready for JavaScript consumption.
fn build_hover_json(
    entity_type: &str,
    name: &str,
    path: &str,
    extension: &str,
    color: rource_math::Color,
    radius: f32,
) -> String {
    use std::fmt::Write;

    // Estimate capacity: fixed JSON overhead (~80 bytes) + field lengths + escaping margin
    let capacity = 100 + entity_type.len() + name.len() + path.len() + extension.len();
    let mut json = String::with_capacity(capacity);

    // Build JSON in single pass
    json.push_str(r#"{"entityType":""#);
    escape_json_into(entity_type, &mut json);
    json.push_str(r#"","name":""#);
    escape_json_into(name, &mut json);
    json.push_str(r#"","path":""#);
    escape_json_into(path, &mut json);
    json.push_str(r#"","extension":""#);
    escape_json_into(extension, &mut json);
    json.push_str(r#"","color":""#);
    write_color_hex_into(color, &mut json);
    json.push_str(r#"","radius":"#);
    let _ = write!(json, "{radius}}}");

    json
}

#[wasm_bindgen]
impl Rource {
    /// Gets information about the entity at the given screen coordinates.
    ///
    /// Returns a JSON string with entity information if an entity is found,
    /// or null if no entity is under the cursor.
    ///
    /// # Arguments
    ///
    /// * `x` - Screen X coordinate (canvas-relative)
    /// * `y` - Screen Y coordinate (canvas-relative)
    ///
    /// # Returns
    ///
    /// JSON string with format:
    /// ```json
    /// {
    ///   "entityType": "file" | "user" | "directory",
    ///   "name": "filename.rs",
    ///   "path": "src/lib.rs",
    ///   "extension": "rs",
    ///   "color": "#FF5500",
    ///   "radius": 5.0
    /// }
    /// ```
    /// Or `null` if no entity is under the cursor.
    #[wasm_bindgen(js_name = getEntityAtCursor)]
    pub fn get_entity_at_cursor(&self, x: f32, y: f32) -> Option<String> {
        use crate::interaction::DragTarget;

        let screen_pos = Vec2::new(x, y);
        let world_pos = self.camera.screen_to_world(screen_pos);
        let hit_radius = ENTITY_HIT_RADIUS / self.camera.zoom();

        // Check users first (highest visual priority)
        if let Some(DragTarget::User(user_id)) = hit_test_user(&self.scene, world_pos, hit_radius) {
            if let Some(user) = self.scene.get_user(user_id) {
                // Build JSON directly without intermediate allocations
                return Some(build_hover_json(
                    "user",
                    user.name(),
                    "",
                    "",
                    user.color(),
                    user.radius(),
                ));
            }
        }

        // Check files
        if let Some(DragTarget::File(file_id)) = hit_test_file(&self.scene, world_pos, hit_radius) {
            if let Some(file) = self.scene.get_file(file_id) {
                // Build JSON directly without intermediate allocations
                let path_str = file.path().to_string_lossy();
                return Some(build_hover_json(
                    "file",
                    file.name(),
                    &path_str,
                    file.extension().unwrap_or(""),
                    file.color(),
                    file.radius(),
                ));
            }
        }

        // Check directories
        if let Some(DragTarget::Directory(dir_id)) =
            hit_test_directory(&self.scene, world_pos, hit_radius)
        {
            if let Some(dir) = self.scene.directories().get(dir_id) {
                // Directories use a static color (brownish tone like tree bark)
                let dir_color = rource_math::Color::new(0.6, 0.45, 0.3, 1.0);
                let path_str = dir.path().to_string_lossy();
                // Build JSON directly without intermediate allocations
                return Some(build_hover_json(
                    "directory",
                    dir.name(),
                    &path_str,
                    "",
                    dir_color,
                    dir.radius(),
                ));
            }
        }

        None
    }

    /// Gets the current mouse position in screen coordinates.
    ///
    /// Returns an array `[x, y]` of the last known mouse position.
    #[wasm_bindgen(js_name = getMousePosition)]
    pub fn get_mouse_position(&self) -> Vec<f32> {
        vec![self.mouse_x, self.mouse_y]
    }

    /// Gets the current mouse position in world coordinates.
    ///
    /// Returns an array `[x, y]` of the mouse position in world space.
    #[wasm_bindgen(js_name = getMouseWorldPosition)]
    pub fn get_mouse_world_position(&self) -> Vec<f32> {
        let screen_pos = Vec2::new(self.mouse_x, self.mouse_y);
        let world_pos = self.camera.screen_to_world(screen_pos);
        vec![world_pos.x, world_pos.y]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_escape_json_basic() {
        assert_eq!(escape_json("hello"), "hello");
        assert_eq!(escape_json("hello\"world"), "hello\\\"world");
        assert_eq!(escape_json("path\\file"), "path\\\\file");
    }

    #[test]
    fn test_escape_json_special_chars() {
        assert_eq!(escape_json("line\nbreak"), "line\\nbreak");
        assert_eq!(escape_json("tab\there"), "tab\\there");
    }

    #[test]
    fn test_color_to_hex() {
        let white = rource_math::Color::new(1.0, 1.0, 1.0, 1.0);
        assert_eq!(color_to_hex(white), "#FFFFFF");

        let red = rource_math::Color::new(1.0, 0.0, 0.0, 1.0);
        assert_eq!(color_to_hex(red), "#FF0000");

        let custom = rource_math::Color::new(0.5, 0.25, 0.75, 1.0);
        assert_eq!(color_to_hex(custom), "#7F3FBF");
    }

    #[test]
    fn test_hover_info_to_json() {
        let info = HoverInfo {
            entity_type: "file".to_string(),
            name: "test.rs".to_string(),
            path: "src/test.rs".to_string(),
            extension: "rs".to_string(),
            color: "#FF5500".to_string(),
            radius: 5.0,
        };
        let json = info.to_json();
        assert!(json.contains(r#""entityType":"file""#));
        assert!(json.contains(r#""name":"test.rs""#));
        assert!(json.contains(r#""path":"src/test.rs""#));
    }

    #[test]
    fn test_hover_info_escapes_special_chars() {
        let info = HoverInfo {
            entity_type: "file".to_string(),
            name: "file\"with\"quotes.rs".to_string(),
            path: "path\\with\\backslashes".to_string(),
            extension: "rs".to_string(),
            color: "#000000".to_string(),
            radius: 1.0,
        };
        let json = info.to_json();
        assert!(json.contains('\\')); // Contains escaped quotes/backslashes
    }

    // ========================================================================
    // Additional Escape JSON Tests
    // ========================================================================

    #[test]
    fn test_escape_json_newlines() {
        assert_eq!(escape_json("line\nbreak"), "line\\nbreak");
        assert_eq!(escape_json("line\r\nbreak"), "line\\r\\nbreak");
    }

    #[test]
    fn test_escape_json_tabs() {
        assert_eq!(escape_json("col1\tcol2"), "col1\\tcol2");
    }

    #[test]
    fn test_escape_json_mixed_special_chars() {
        assert_eq!(
            escape_json("quote\"newline\ntab\t"),
            "quote\\\"newline\\ntab\\t"
        );
    }

    #[test]
    fn test_escape_json_empty() {
        assert_eq!(escape_json(""), "");
    }

    #[test]
    fn test_escape_json_unicode_preserved() {
        assert_eq!(escape_json("日本語テスト"), "日本語テスト");
        assert_eq!(escape_json("emoji 🎉"), "emoji 🎉");
    }

    // ========================================================================
    // Additional Color to Hex Tests
    // ========================================================================

    #[test]
    fn test_color_to_hex_primary_colors() {
        let cyan = rource_math::Color::new(0.0, 1.0, 1.0, 1.0);
        assert_eq!(color_to_hex(cyan), "#00FFFF");

        let magenta = rource_math::Color::new(1.0, 0.0, 1.0, 1.0);
        assert_eq!(color_to_hex(magenta), "#FF00FF");

        let yellow = rource_math::Color::new(1.0, 1.0, 0.0, 1.0);
        assert_eq!(color_to_hex(yellow), "#FFFF00");
    }

    #[test]
    fn test_color_to_hex_ignores_alpha() {
        let semi_transparent = rource_math::Color::new(1.0, 0.0, 0.0, 0.5);
        assert_eq!(color_to_hex(semi_transparent), "#FF0000");

        let fully_transparent = rource_math::Color::new(0.0, 1.0, 0.0, 0.0);
        assert_eq!(color_to_hex(fully_transparent), "#00FF00");
    }

    // ========================================================================
    // Build Hover JSON Tests
    // ========================================================================

    #[test]
    fn test_build_hover_json_file() {
        let color = rource_math::Color::new(1.0, 0.5, 0.0, 1.0);
        let json = build_hover_json("file", "main.rs", "src/main.rs", "rs", color, 5.0);

        assert!(json.contains(r#""entityType":"file""#));
        assert!(json.contains(r#""name":"main.rs""#));
        assert!(json.contains(r#""path":"src/main.rs""#));
        assert!(json.contains(r#""extension":"rs""#));
        assert!(json.contains(r#""radius":5"#));
        assert!(json.contains(r##""color":"#FF7F00""##));
    }

    #[test]
    fn test_build_hover_json_user() {
        let color = rource_math::Color::new(0.0, 0.5, 1.0, 1.0);
        let json = build_hover_json("user", "Alice", "", "", color, 10.0);

        assert!(json.contains(r#""entityType":"user""#));
        assert!(json.contains(r#""name":"Alice""#));
        assert!(json.contains(r#""path":"""#));
        assert!(json.contains(r#""extension":"""#));
    }

    #[test]
    fn test_build_hover_json_directory() {
        let color = rource_math::Color::new(0.6, 0.45, 0.3, 1.0);
        let json = build_hover_json("directory", "src", "project/src", "", color, 15.0);

        assert!(json.contains(r#""entityType":"directory""#));
        assert!(json.contains(r#""name":"src""#));
        assert!(json.contains(r#""path":"project/src""#));
    }

    #[test]
    fn test_build_hover_json_escapes_special_chars() {
        let color = rource_math::Color::new(1.0, 1.0, 1.0, 1.0);
        let json = build_hover_json(
            "file",
            "file\"with\"quotes.txt",
            "path\\with\\backslashes",
            "txt",
            color,
            3.0,
        );

        // Should have escaped quotes and backslashes
        assert!(json.contains(r#"\"with\""#));
        assert!(json.contains(r"path\\with\\backslashes"));
    }

    #[test]
    fn test_build_hover_json_unicode_names() {
        let color = rource_math::Color::new(0.5, 0.5, 0.5, 1.0);
        let json = build_hover_json(
            "file",
            "日本語.txt",
            "フォルダ/日本語.txt",
            "txt",
            color,
            4.0,
        );

        assert!(json.contains("日本語.txt"));
        assert!(json.contains("フォルダ/日本語.txt"));
    }

    // ========================================================================
    // Write Color Hex Into Tests
    // ========================================================================

    #[test]
    fn test_write_color_hex_into_zero_allocation() {
        let color = rource_math::Color::new(1.0, 0.0, 0.0, 1.0);
        let mut buffer = String::with_capacity(7);
        write_color_hex_into(color, &mut buffer);
        assert_eq!(buffer, "#FF0000");
    }

    #[test]
    fn test_write_color_hex_into_appends() {
        let color = rource_math::Color::new(0.0, 1.0, 0.0, 1.0);
        let mut buffer = String::from("prefix:");
        write_color_hex_into(color, &mut buffer);
        assert_eq!(buffer, "prefix:#00FF00");
    }

    // ========================================================================
    // Needs JSON Escaping Tests
    // ========================================================================

    #[test]
    fn test_needs_json_escaping_detects_all_special() {
        assert!(needs_json_escaping("has\\backslash"));
        assert!(needs_json_escaping("has\"quote"));
        assert!(needs_json_escaping("has\nnewline"));
        assert!(needs_json_escaping("has\rcarriage"));
        assert!(needs_json_escaping("has\ttab"));
    }

    #[test]
    fn test_needs_json_escaping_normal_strings() {
        assert!(!needs_json_escaping("normal string"));
        assert!(!needs_json_escaping("with numbers 123"));
        assert!(!needs_json_escaping("unicode 日本語"));
        assert!(!needs_json_escaping(""));
    }
}
