//! Font rendering using fontdue.
//!
//! This module provides font loading, glyph rasterization, and caching
//! for efficient text rendering.

use std::collections::HashMap;

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
            glyphs: HashMap::new(),
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
}
