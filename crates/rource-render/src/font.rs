// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Font rendering using fontdue.
//!
//! This module provides font loading, glyph rasterization, and caching
//! for efficient text rendering.

use rustc_hash::FxHashMap as HashMap;

use fontdue::{Font, FontSettings, Metrics};

use crate::FontId;

/// Maximum number of fonts that can be loaded.
const MAX_FONTS: usize = 16;

/// A cached glyph with its rasterized bitmap.
#[derive(Debug, Clone)]
pub struct CachedGlyph {
    /// Glyph metrics.
    pub metrics: Metrics,

    /// Rasterized bitmap data (alpha values).
    pub bitmap: Vec<u8>,
}

/// Cache for rasterized glyphs.
#[derive(Debug)]
struct GlyphCache {
    /// Cached glyphs keyed by (char, size in tenths of a pixel).
    glyphs: HashMap<(char, u32), CachedGlyph>,
}

impl GlyphCache {
    fn new() -> Self {
        Self {
            glyphs: HashMap::default(),
        }
    }

    /// Gets a cached glyph or rasterizes it if not cached.
    fn get_or_insert(&mut self, font: &Font, ch: char, size: f32) -> &CachedGlyph {
        // Use size in tenths of pixels as key to allow some variation
        let size_key = (size * 10.0) as u32;
        let key = (ch, size_key);

        self.glyphs.entry(key).or_insert_with(|| {
            let (metrics, bitmap) = font.rasterize(ch, size);
            CachedGlyph { metrics, bitmap }
        })
    }

    fn clear(&mut self) {
        self.glyphs.clear();
    }
}

/// Font cache managing loaded fonts and glyph caching.
#[derive(Debug)]
pub struct FontCache {
    /// Loaded fonts.
    fonts: Vec<Option<Font>>,

    /// Glyph cache per font.
    caches: Vec<GlyphCache>,

    /// Next font ID to assign.
    next_id: u32,
}

impl FontCache {
    /// Creates a new empty font cache.
    pub fn new() -> Self {
        let mut fonts = Vec::with_capacity(MAX_FONTS);
        let mut caches = Vec::with_capacity(MAX_FONTS);

        for _ in 0..MAX_FONTS {
            fonts.push(None);
            caches.push(GlyphCache::new());
        }

        Self {
            fonts,
            caches,
            next_id: 0,
        }
    }

    /// Loads a font from raw data.
    ///
    /// Returns `None` if the font data is invalid or max fonts exceeded.
    pub fn load(&mut self, data: &[u8]) -> Option<FontId> {
        if self.next_id as usize >= MAX_FONTS {
            return None;
        }

        let settings = FontSettings::default();
        let font = Font::from_bytes(data, settings).ok()?;

        let id = self.next_id;
        self.fonts[id as usize] = Some(font);
        self.next_id += 1;

        Some(FontId::new(id))
    }

    /// Gets a loaded font by ID.
    #[inline]
    pub fn get(&self, id: FontId) -> Option<&Font> {
        self.fonts.get(id.raw() as usize)?.as_ref()
    }

    /// Rasterizes a glyph, using cache if available.
    pub fn rasterize(&mut self, font_id: FontId, ch: char, size: f32) -> Option<&CachedGlyph> {
        let idx = font_id.raw() as usize;
        let font = self.fonts.get(idx)?.as_ref()?;

        // We need to temporarily move the font out to satisfy the borrow checker
        // This is safe because we're not modifying the fonts Vec
        let cache = self.caches.get_mut(idx)?;
        Some(cache.get_or_insert(font, ch, size))
    }

    /// Measures the width of a text string.
    pub fn measure_text(&mut self, font_id: FontId, text: &str, size: f32) -> Option<f32> {
        let font = self.get(font_id)?;

        let mut width = 0.0;
        for ch in text.chars() {
            let (metrics, _) = font.rasterize(ch, size);
            width += metrics.advance_width;
        }

        Some(width)
    }

    /// Gets the line height for a font at a given size.
    pub fn line_height(&self, font_id: FontId, size: f32) -> Option<f32> {
        let font = self.get(font_id)?;
        let metrics = font.horizontal_line_metrics(size)?;
        Some(metrics.new_line_size)
    }

    /// Clears the glyph cache for a specific font.
    pub fn clear_cache(&mut self, font_id: FontId) {
        if let Some(cache) = self.caches.get_mut(font_id.raw() as usize) {
            cache.clear();
        }
    }

    /// Clears all glyph caches.
    pub fn clear_all_caches(&mut self) {
        for cache in &mut self.caches {
            cache.clear();
        }
    }

    /// Returns the number of loaded fonts.
    pub fn font_count(&self) -> usize {
        self.fonts.iter().filter(|f| f.is_some()).count()
    }
}

impl Default for FontCache {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Simple embedded font for testing - using a basic subset
    // This is a minimal valid TrueType font header (not functional, just for structure)
    // In real usage, you'd load an actual font file

    #[test]
    fn test_font_cache_new() {
        let cache = FontCache::new();
        assert_eq!(cache.font_count(), 0);
    }

    #[test]
    fn test_font_cache_default() {
        let cache = FontCache::default();
        assert_eq!(cache.font_count(), 0);
    }

    #[test]
    fn test_font_cache_load_invalid() {
        let mut cache = FontCache::new();
        let result = cache.load(&[0, 1, 2, 3]); // Invalid font data
        assert!(result.is_none());
    }

    #[test]
    fn test_font_cache_get_missing() {
        let cache = FontCache::new();
        assert!(cache.get(FontId::new(0)).is_none());
    }

    #[test]
    fn test_font_cache_clear_cache() {
        let mut cache = FontCache::new();
        // Should not panic even with no fonts loaded
        cache.clear_cache(FontId::new(0));
        cache.clear_all_caches();
    }

    #[test]
    fn test_glyph_cache_new() {
        let cache = GlyphCache::new();
        assert!(cache.glyphs.is_empty());
    }

    /// Test to analyze actual font metrics for Roboto Mono.
    /// This helps validate the width estimation heuristic.
    #[test]
    fn test_roboto_mono_character_widths() {
        use crate::default_font;

        let mut cache = FontCache::new();
        let font_id = cache
            .load(default_font::ROBOTO_MONO)
            .expect("Failed to load Roboto Mono");
        let font = cache.get(font_id).expect("Font not found");

        let size = 12.0;

        // Measure various ASCII characters
        let ascii_chars = ['a', 'M', 'W', 'i', 'l', 'm', 'w', '0', '9', '.', '_', '-'];
        let mut ascii_widths = Vec::new();
        for ch in ascii_chars {
            let (metrics, _) = font.rasterize(ch, size);
            ascii_widths.push((ch, metrics.advance_width));
        }

        // Print for analysis (run with --nocapture to see)
        println!("\n=== Roboto Mono Character Width Analysis (size={size}) ===");
        println!("ASCII characters:");
        for (ch, width) in &ascii_widths {
            println!("  '{ch}': advance_width = {width:.2}");
        }

        // Verify monospace property: all ASCII should have same width
        let first_width = ascii_widths[0].1;
        for (ch, width) in &ascii_widths {
            let diff = (width - first_width).abs();
            assert!(
                diff < 0.1,
                "Monospace violation: '{ch}' has width {width:.2}, expected {first_width:.2}"
            );
        }

        // Calculate the actual factor: advance_width / font_size
        let actual_factor = first_width / size;
        println!("\nActual monospace factor: {actual_factor:.4}");
        println!("Current heuristic factor: 0.75");
        println!("Factor difference: {:.4}", (actual_factor - 0.75).abs());

        // Test multi-byte UTF-8 strings
        println!("\n=== UTF-8 Width Analysis ===");
        let test_strings = [
            ("hello", "ASCII only"),
            ("héllo", "ASCII + accent (é = 2 bytes)"),
            ("你好", "Chinese (2 chars, 6 bytes)"),
            ("🚀", "Emoji (1 char, 4 bytes)"),
        ];

        for (s, desc) in test_strings {
            let byte_len = s.len();
            let char_count = s.chars().count();
            let actual_width = cache.measure_text(font_id, s, size).unwrap_or(0.0);
            let estimate_old = byte_len as f32 * size * 0.75; // OLD: bytes × 0.75
            let estimate_new = char_count as f32 * size * 0.62; // NEW: chars × 0.62

            println!("{desc}:");
            println!("  String: \"{s}\"");
            println!("  Bytes: {byte_len}, Chars: {char_count}");
            println!("  Actual width: {actual_width:.2}");
            println!(
                "  OLD (bytes × 0.75): {estimate_old:.2} (error: {:.1}%)",
                ((estimate_old - actual_width) / actual_width * 100.0).abs()
            );
            println!(
                "  NEW (chars × 0.62): {estimate_new:.2} (error: {:.1}%)",
                ((estimate_new - actual_width) / actual_width * 100.0).abs()
            );
        }
    }

    /// Test realistic file and user name scenarios.
    /// These are the actual strings that appear in Git repositories.
    #[test]
    fn test_realistic_label_scenarios() {
        use crate::default_font;

        let mut cache = FontCache::new();
        let font_id = cache
            .load(default_font::ROBOTO_MONO)
            .expect("Failed to load Roboto Mono");

        let size = 12.0;

        // Realistic file names from Git repositories
        let file_names = [
            "main.rs",
            "README.md",
            "Cargo.toml",
            "src/lib.rs",
            "tests/integration_test.rs",
            "über_config.json",   // German umlaut
            "日本語ファイル.txt", // Japanese
            "файл.rs",            // Russian
            "αβγδ.rs",            // Greek
        ];

        // Realistic user names from Git commits
        let user_names = [
            "Alice",
            "Bob",
            "John Doe",
            "María García", // Spanish
            "田中太郎",     // Japanese
            "Müller",       // German
            "Иван Петров",  // Russian
            "Αλέξανδρος",   // Greek
        ];

        println!("\n=== Realistic File Names ===");
        let mut total_error_old = 0.0f32;
        let mut total_error_new = 0.0f32;
        let mut count = 0;

        for name in file_names {
            let actual = cache.measure_text(font_id, name, size).unwrap_or(0.0);
            let est_old = name.len() as f32 * size * 0.75; // OLD
            let est_new = name.chars().count() as f32 * size * 0.62; // NEW (Phase 68)
            let err_old = ((est_old - actual) / actual * 100.0).abs();
            let err_new = ((est_new - actual) / actual * 100.0).abs();
            total_error_old += err_old;
            total_error_new += err_new;
            count += 1;

            println!(
                "{name:30} actual={actual:6.1} OLD={est_old:6.1}({err_old:5.1}%) NEW={est_new:6.1}({err_new:5.1}%)"
            );
        }

        println!("\n=== Realistic User Names ===");
        for name in user_names {
            let actual = cache.measure_text(font_id, name, size).unwrap_or(0.0);
            let est_old = name.len() as f32 * size * 0.75; // OLD
            let est_new = name.chars().count() as f32 * size * 0.62; // NEW (Phase 68)
            let err_old = ((est_old - actual) / actual * 100.0).abs();
            let err_new = ((est_new - actual) / actual * 100.0).abs();
            total_error_old += err_old;
            total_error_new += err_new;
            count += 1;

            println!(
                "{name:30} actual={actual:6.1} OLD={est_old:6.1}({err_old:5.1}%) NEW={est_new:6.1}({err_new:5.1}%)"
            );
        }

        let avg_error_old = total_error_old / count as f32;
        let avg_error_new = total_error_new / count as f32;
        println!("\n=== Summary ===");
        println!("OLD (bytes × 0.75): average error = {avg_error_old:.1}%");
        println!("NEW (chars × 0.62): average error = {avg_error_new:.1}%");
        println!(
            "Improvement: {:.1}× more accurate",
            avg_error_old / avg_error_new
        );
    }
}
