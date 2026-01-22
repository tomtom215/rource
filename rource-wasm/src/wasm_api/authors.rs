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
