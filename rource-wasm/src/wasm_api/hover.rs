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
    pub fn to_json(&self) -> String {
        format!(
            r#"{{"entityType":"{}","name":"{}","path":"{}","extension":"{}","color":"{}","radius":{}}}"#,
            escape_json(&self.entity_type),
            escape_json(&self.name),
            escape_json(&self.path),
            escape_json(&self.extension),
            escape_json(&self.color),
            self.radius
        )
    }
}

/// Escapes a string for safe JSON inclusion.
fn escape_json(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

/// Converts a Color to a hex string.
fn color_to_hex(color: rource_math::Color) -> String {
    format!(
        "#{:02X}{:02X}{:02X}",
        (color.r * 255.0) as u8,
        (color.g * 255.0) as u8,
        (color.b * 255.0) as u8
    )
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
                let info = HoverInfo {
                    entity_type: "user".to_string(),
                    name: user.name().to_string(),
                    path: String::new(),
                    extension: String::new(),
                    color: color_to_hex(user.color()),
                    radius: user.radius(),
                };
                return Some(info.to_json());
            }
        }

        // Check files
        if let Some(DragTarget::File(file_id)) = hit_test_file(&self.scene, world_pos, hit_radius) {
            if let Some(file) = self.scene.get_file(file_id) {
                let info = HoverInfo {
                    entity_type: "file".to_string(),
                    name: file.name().to_string(),
                    path: file.path().to_string_lossy().to_string(),
                    extension: file.extension().unwrap_or("").to_string(),
                    color: color_to_hex(file.color()),
                    radius: file.radius(),
                };
                return Some(info.to_json());
            }
        }

        // Check directories
        if let Some(DragTarget::Directory(dir_id)) =
            hit_test_directory(&self.scene, world_pos, hit_radius)
        {
            if let Some(dir) = self.scene.directories().get(dir_id) {
                // Directories use a static color (brownish tone like tree bark)
                let dir_color = rource_math::Color::new(0.6, 0.45, 0.3, 1.0);
                let info = HoverInfo {
                    entity_type: "directory".to_string(),
                    name: dir.name().to_string(),
                    path: dir.path().to_string_lossy().to_string(),
                    extension: String::new(),
                    color: color_to_hex(dir_color),
                    radius: dir.radius(),
                };
                return Some(info.to_json());
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
}
