// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! WebGL2 texture management and font atlas.
//!
//! This module provides texture loading, font glyph caching in texture atlases,
//! and efficient texture switching for batched rendering.
//!
//! ## Texture Atlas Defragmentation
//!
//! The font atlas uses row-based packing which can lead to fragmentation over time,
//! especially in long-running sessions with many unique glyphs. The atlas tracks
//! fragmentation statistics and can be defragmented to reclaim wasted space.
//!
//! Key metrics:
//! - **Used area**: Total pixels occupied by actual glyph data
//! - **Allocated area**: Total pixels in allocated regions (includes padding)
//! - **Fragmentation ratio**: 1 - (used / allocated), higher = more fragmented
//!
//! When fragmentation exceeds 50%, call `defragment()` to compact the atlas.

use rustc_hash::FxHashMap as HashMap;

use web_sys::{WebGl2RenderingContext, WebGlTexture};

use crate::TextureId;

/// Maximum atlas size (2048x2048 is widely supported).
const MAX_ATLAS_SIZE: u32 = 2048;

/// Initial atlas size.
const INITIAL_ATLAS_SIZE: u32 = 512;

/// Fragmentation threshold above which defragmentation is recommended.
const DEFRAG_THRESHOLD: f32 = 0.5;

/// A region in the font atlas.
#[derive(Debug, Clone, Copy)]
pub struct AtlasRegion {
    /// X position in atlas (pixels).
    pub x: u32,
    /// Y position in atlas (pixels).
    pub y: u32,
    /// Width in pixels.
    pub width: u32,
    /// Height in pixels.
    pub height: u32,
    /// Atlas size when region was created (for UV calculation).
    pub atlas_size: u32,
}

impl AtlasRegion {
    /// Returns UV coordinates for this region.
    pub fn uv_bounds(&self) -> (f32, f32, f32, f32) {
        let size = self.atlas_size as f32;
        (
            self.x as f32 / size,
            self.y as f32 / size,
            (self.x + self.width) as f32 / size,
            (self.y + self.height) as f32 / size,
        )
    }
}

/// A simple row-based texture packer for the font atlas.
#[derive(Debug)]
struct RowPacker {
    /// Current row Y position.
    current_row_y: u32,
    /// Current row height.
    current_row_height: u32,
    /// Current X position in current row.
    current_x: u32,
    /// Atlas size.
    atlas_size: u32,
}

impl RowPacker {
    fn new(atlas_size: u32) -> Self {
        Self {
            current_row_y: 0,
            current_row_height: 0,
            current_x: 0,
            atlas_size,
        }
    }

    /// Attempts to allocate a region for a glyph.
    /// Returns None if the atlas is full.
    fn allocate(&mut self, width: u32, height: u32) -> Option<AtlasRegion> {
        // Add 1 pixel padding to avoid bleeding
        let padded_width = width + 1;
        let padded_height = height + 1;

        // Check if glyph fits in current row
        if self.current_x + padded_width <= self.atlas_size {
            // Check if we need to start a new row
            if padded_height > self.current_row_height {
                // Check if the new height fits
                if self.current_row_y + padded_height > self.atlas_size {
                    return None; // Atlas is full
                }
                self.current_row_height = padded_height;
            }

            let region = AtlasRegion {
                x: self.current_x,
                y: self.current_row_y,
                width,
                height,
                atlas_size: self.atlas_size,
            };

            self.current_x += padded_width;
            return Some(region);
        }

        // Start new row
        self.current_row_y += self.current_row_height;
        self.current_row_height = padded_height;
        self.current_x = 0;

        // Check if new row fits
        if self.current_row_y + padded_height > self.atlas_size {
            return None; // Atlas is full
        }

        let region = AtlasRegion {
            x: 0,
            y: self.current_row_y,
            width,
            height,
            atlas_size: self.atlas_size,
        };

        self.current_x = padded_width;
        Some(region)
    }

    fn resize(&mut self, new_size: u32) {
        self.atlas_size = new_size;
    }
}

/// Key for cached glyphs in the font atlas.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GlyphKey {
    /// Character.
    pub ch: char,
    /// Font size in tenths of pixels.
    pub size_tenths: u32,
}

/// Statistics about font atlas usage.
#[derive(Debug, Clone, Copy, Default)]
pub struct AtlasStats {
    /// Total number of glyphs in the atlas.
    pub glyph_count: u32,
    /// Total pixels used by glyph data (width * height sum).
    pub used_pixels: u64,
    /// Total pixels allocated (including padding).
    pub allocated_pixels: u64,
    /// Current atlas size (width = height).
    pub atlas_size: u32,
    /// Fragmentation ratio (0.0 = no fragmentation, 1.0 = fully fragmented).
    pub fragmentation: f32,
}

impl AtlasStats {
    /// Returns whether defragmentation is recommended.
    pub fn needs_defragmentation(&self) -> bool {
        self.fragmentation > DEFRAG_THRESHOLD && self.glyph_count > 0
    }
}

/// A font texture atlas for efficient text rendering.
#[derive(Debug)]
pub struct FontAtlas {
    /// WebGL texture.
    texture: Option<WebGlTexture>,
    /// Current atlas size.
    size: u32,
    /// CPU-side atlas data (single channel alpha).
    data: Vec<u8>,
    /// Row packer for allocation.
    packer: RowPacker,
    /// Cached glyph regions.
    glyphs: HashMap<GlyphKey, AtlasRegion>,
    /// Cached glyph bitmap data for defragmentation.
    glyph_bitmaps: HashMap<GlyphKey, Vec<u8>>,
    /// Whether atlas needs upload.
    dirty: bool,
    /// Whether atlas was resized.
    resized: bool,
    /// Total pixels used by glyph data.
    used_pixels: u64,
    /// Total pixels allocated (including padding).
    allocated_pixels: u64,
}

impl FontAtlas {
    /// Creates a new font atlas.
    pub fn new() -> Self {
        let size = INITIAL_ATLAS_SIZE;
        Self {
            texture: None,
            size,
            data: vec![0u8; (size * size) as usize],
            packer: RowPacker::new(size),
            glyphs: HashMap::default(),
            glyph_bitmaps: HashMap::default(),
            dirty: false,
            resized: false,
            used_pixels: 0,
            allocated_pixels: 0,
        }
    }

    /// Ensures the WebGL texture is created.
    pub fn ensure_texture(&mut self, gl: &WebGl2RenderingContext) {
        if self.texture.is_none() {
            self.texture = gl.create_texture();
            self.resized = true; // Force initial upload
        }
    }

    /// Gets a cached glyph region.
    pub fn get_glyph(&self, key: GlyphKey) -> Option<&AtlasRegion> {
        self.glyphs.get(&key)
    }

    /// Adds a glyph to the atlas.
    /// Returns the region where the glyph was placed, or None if atlas is full.
    pub fn add_glyph(
        &mut self,
        key: GlyphKey,
        width: u32,
        height: u32,
        bitmap: &[u8],
    ) -> Option<AtlasRegion> {
        // Try to allocate
        let mut region = self.packer.allocate(width, height);

        // If failed, try defragmentation first (if worthwhile), then resize
        if region.is_none() {
            // Try defragmentation if fragmented
            if self.stats().needs_defragmentation() {
                self.defragment_internal();
                region = self.packer.allocate(width, height);
            }

            // If still no space and we can resize, do it
            if region.is_none() && self.size < MAX_ATLAS_SIZE {
                self.resize(self.size * 2);
                region = self.packer.allocate(width, height);
            }
        }

        let region = region?;

        // Copy glyph bitmap to atlas
        for y in 0..height {
            for x in 0..width {
                let src_idx = (y * width + x) as usize;
                let dst_idx = ((region.y + y) * self.size + region.x + x) as usize;
                self.data[dst_idx] = bitmap.get(src_idx).copied().unwrap_or(0);
            }
        }

        // Track statistics
        let glyph_pixels = u64::from(width) * u64::from(height);
        let allocated_pixels = u64::from(width + 1) * u64::from(height + 1); // +1 for padding
        self.used_pixels += glyph_pixels;
        self.allocated_pixels += allocated_pixels;

        // Store bitmap for potential defragmentation
        self.glyph_bitmaps.insert(key, bitmap.to_vec());

        self.glyphs.insert(key, region);
        self.dirty = true;

        Some(region)
    }

    /// Resizes the atlas to a larger size.
    fn resize(&mut self, new_size: u32) {
        if new_size <= self.size || new_size > MAX_ATLAS_SIZE {
            return;
        }

        // Create new data buffer
        let mut new_data = vec![0u8; (new_size * new_size) as usize];

        // Copy old data
        for y in 0..self.size {
            for x in 0..self.size {
                let old_idx = (y * self.size + x) as usize;
                let new_idx = (y * new_size + x) as usize;
                new_data[new_idx] = self.data[old_idx];
            }
        }

        self.data = new_data;
        self.size = new_size;
        self.packer.resize(new_size);

        // Update UV coordinates for existing glyphs
        for region in self.glyphs.values_mut() {
            region.atlas_size = new_size;
        }

        self.resized = true;
        self.dirty = true;
    }

    /// Uploads atlas to GPU if needed.
    pub fn upload(&mut self, gl: &WebGl2RenderingContext) {
        if !self.dirty && !self.resized {
            return;
        }

        self.ensure_texture(gl);

        if let Some(texture) = &self.texture {
            gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, Some(texture));

            if self.resized {
                // Full texture reallocation
                gl.tex_image_2d_with_i32_and_i32_and_i32_and_format_and_type_and_opt_u8_array(
                    WebGl2RenderingContext::TEXTURE_2D,
                    0,
                    WebGl2RenderingContext::R8 as i32,
                    self.size as i32,
                    self.size as i32,
                    0,
                    WebGl2RenderingContext::RED,
                    WebGl2RenderingContext::UNSIGNED_BYTE,
                    Some(&self.data),
                )
                .ok();

                // Set texture parameters
                gl.tex_parameteri(
                    WebGl2RenderingContext::TEXTURE_2D,
                    WebGl2RenderingContext::TEXTURE_MIN_FILTER,
                    WebGl2RenderingContext::LINEAR as i32,
                );
                gl.tex_parameteri(
                    WebGl2RenderingContext::TEXTURE_2D,
                    WebGl2RenderingContext::TEXTURE_MAG_FILTER,
                    WebGl2RenderingContext::LINEAR as i32,
                );
                gl.tex_parameteri(
                    WebGl2RenderingContext::TEXTURE_2D,
                    WebGl2RenderingContext::TEXTURE_WRAP_S,
                    WebGl2RenderingContext::CLAMP_TO_EDGE as i32,
                );
                gl.tex_parameteri(
                    WebGl2RenderingContext::TEXTURE_2D,
                    WebGl2RenderingContext::TEXTURE_WRAP_T,
                    WebGl2RenderingContext::CLAMP_TO_EDGE as i32,
                );

                self.resized = false;
            } else {
                // Just update data
                gl.tex_sub_image_2d_with_i32_and_i32_and_u32_and_type_and_opt_u8_array(
                    WebGl2RenderingContext::TEXTURE_2D,
                    0,
                    0,
                    0,
                    self.size as i32,
                    self.size as i32,
                    WebGl2RenderingContext::RED,
                    WebGl2RenderingContext::UNSIGNED_BYTE,
                    Some(&self.data),
                )
                .ok();
            }

            gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, None);
        }

        self.dirty = false;
    }

    /// Binds the atlas texture to a texture unit.
    pub fn bind(&self, gl: &WebGl2RenderingContext, unit: u32) {
        if let Some(texture) = &self.texture {
            gl.active_texture(WebGl2RenderingContext::TEXTURE0 + unit);
            gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, Some(texture));
        }
    }

    /// Returns the current atlas size.
    pub fn size(&self) -> u32 {
        self.size
    }

    /// Returns statistics about atlas usage.
    pub fn stats(&self) -> AtlasStats {
        let fragmentation = if self.allocated_pixels > 0 {
            1.0 - (self.used_pixels as f32 / self.allocated_pixels as f32)
        } else {
            0.0
        };

        AtlasStats {
            glyph_count: self.glyphs.len() as u32,
            used_pixels: self.used_pixels,
            allocated_pixels: self.allocated_pixels,
            atlas_size: self.size,
            fragmentation,
        }
    }

    /// Returns whether defragmentation is recommended.
    ///
    /// Defragmentation is recommended when more than 50% of allocated space
    /// is wasted due to row-based packing inefficiency.
    pub fn needs_defragmentation(&self) -> bool {
        self.stats().needs_defragmentation()
    }

    /// Defragments the atlas by repacking all glyphs.
    ///
    /// This method:
    /// 1. Sorts glyphs by height (tallest first) for better row packing
    /// 2. Clears the atlas data and packer
    /// 3. Re-inserts all glyphs in optimal order
    /// 4. Updates all region positions
    ///
    /// # Returns
    ///
    /// `true` if defragmentation was performed, `false` if not needed or
    /// if there are no bitmaps stored (glyphs added before defrag support).
    pub fn defragment(&mut self) -> bool {
        if !self.needs_defragmentation() {
            return false;
        }
        self.defragment_internal();
        true
    }

    /// Internal defragmentation implementation.
    fn defragment_internal(&mut self) {
        if self.glyph_bitmaps.is_empty() {
            return;
        }

        // Collect all glyphs with their bitmaps, sorted by height (tallest first)
        let mut glyph_entries: Vec<_> = self
            .glyphs
            .iter()
            .filter_map(|(key, region)| {
                self.glyph_bitmaps
                    .get(key)
                    .map(|bitmap| (*key, region.width, region.height, bitmap.clone()))
            })
            .collect();

        // Sort by height descending, then width descending for better packing
        glyph_entries.sort_unstable_by(|a, b| b.2.cmp(&a.2).then_with(|| b.1.cmp(&a.1)));

        // Clear atlas data and reset packer
        self.data.fill(0);
        self.packer = RowPacker::new(self.size);
        self.glyphs.clear();
        self.used_pixels = 0;
        self.allocated_pixels = 0;

        // Re-insert all glyphs in optimal order
        for (key, width, height, bitmap) in glyph_entries {
            if let Some(region) = self.packer.allocate(width, height) {
                // Copy bitmap to new position
                for y in 0..height {
                    for x in 0..width {
                        let src_idx = (y * width + x) as usize;
                        let dst_idx = ((region.y + y) * self.size + region.x + x) as usize;
                        self.data[dst_idx] = bitmap.get(src_idx).copied().unwrap_or(0);
                    }
                }

                // Update statistics
                self.used_pixels += u64::from(width) * u64::from(height);
                self.allocated_pixels += u64::from(width + 1) * u64::from(height + 1);

                self.glyphs.insert(key, region);
            }
            // If allocation fails, the glyph is dropped (shouldn't happen after defrag)
        }

        self.dirty = true;
        self.resized = true; // Force full texture upload
    }

    /// Clears the atlas (for context recovery).
    pub fn clear(&mut self) {
        self.glyphs.clear();
        self.glyph_bitmaps.clear();
        self.packer = RowPacker::new(self.size);
        self.data.fill(0);
        self.used_pixels = 0;
        self.allocated_pixels = 0;
        self.dirty = true;
    }

    /// Releases WebGL resources.
    pub fn destroy(&mut self, gl: &WebGl2RenderingContext) {
        if let Some(texture) = self.texture.take() {
            gl.delete_texture(Some(&texture));
        }
    }
}

impl Default for FontAtlas {
    fn default() -> Self {
        Self::new()
    }
}

/// Manages user-loaded textures.
#[derive(Debug)]
pub struct TextureManager {
    /// Loaded textures by ID.
    textures: HashMap<TextureId, WebGlTexture>,
    /// Texture dimensions by ID.
    dimensions: HashMap<TextureId, (u32, u32)>,
    /// Next texture ID.
    next_id: u32,
}

impl TextureManager {
    /// Creates a new texture manager.
    pub fn new() -> Self {
        Self {
            textures: HashMap::default(),
            dimensions: HashMap::default(),
            next_id: 1,
        }
    }

    /// Loads a texture from RGBA8 data.
    pub fn load(
        &mut self,
        gl: &WebGl2RenderingContext,
        width: u32,
        height: u32,
        data: &[u8],
    ) -> TextureId {
        let texture = gl.create_texture();
        let id = TextureId::new(self.next_id);
        self.next_id += 1;

        if let Some(tex) = texture {
            gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, Some(&tex));

            gl.tex_image_2d_with_i32_and_i32_and_i32_and_format_and_type_and_opt_u8_array(
                WebGl2RenderingContext::TEXTURE_2D,
                0,
                WebGl2RenderingContext::RGBA as i32,
                width as i32,
                height as i32,
                0,
                WebGl2RenderingContext::RGBA,
                WebGl2RenderingContext::UNSIGNED_BYTE,
                Some(data),
            )
            .ok();

            gl.tex_parameteri(
                WebGl2RenderingContext::TEXTURE_2D,
                WebGl2RenderingContext::TEXTURE_MIN_FILTER,
                WebGl2RenderingContext::LINEAR as i32,
            );
            gl.tex_parameteri(
                WebGl2RenderingContext::TEXTURE_2D,
                WebGl2RenderingContext::TEXTURE_MAG_FILTER,
                WebGl2RenderingContext::LINEAR as i32,
            );
            gl.tex_parameteri(
                WebGl2RenderingContext::TEXTURE_2D,
                WebGl2RenderingContext::TEXTURE_WRAP_S,
                WebGl2RenderingContext::CLAMP_TO_EDGE as i32,
            );
            gl.tex_parameteri(
                WebGl2RenderingContext::TEXTURE_2D,
                WebGl2RenderingContext::TEXTURE_WRAP_T,
                WebGl2RenderingContext::CLAMP_TO_EDGE as i32,
            );

            gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, None);

            self.textures.insert(id, tex);
            self.dimensions.insert(id, (width, height));
        }

        id
    }

    /// Unloads a texture.
    pub fn unload(&mut self, gl: &WebGl2RenderingContext, id: TextureId) {
        if let Some(tex) = self.textures.remove(&id) {
            gl.delete_texture(Some(&tex));
        }
        self.dimensions.remove(&id);
    }

    /// Binds a texture to a texture unit.
    #[allow(clippy::option_if_let_else)] // if-let is clearer for GL operations with side effects
    pub fn bind(&self, gl: &WebGl2RenderingContext, id: TextureId, unit: u32) -> bool {
        if let Some(tex) = self.textures.get(&id) {
            gl.active_texture(WebGl2RenderingContext::TEXTURE0 + unit);
            gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D, Some(tex));
            true
        } else {
            false
        }
    }

    /// Gets texture dimensions.
    pub fn dimensions(&self, id: TextureId) -> Option<(u32, u32)> {
        self.dimensions.get(&id).copied()
    }

    /// Releases all WebGL resources.
    pub fn destroy(&mut self, gl: &WebGl2RenderingContext) {
        for tex in self.textures.values() {
            gl.delete_texture(Some(tex));
        }
        self.textures.clear();
        self.dimensions.clear();
    }
}

impl Default for TextureManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atlas_region_uv_bounds() {
        let region = AtlasRegion {
            x: 100,
            y: 200,
            width: 50,
            height: 30,
            atlas_size: 512,
        };

        let (u_min, v_min, u_max, v_max) = region.uv_bounds();
        assert!((u_min - 100.0 / 512.0).abs() < 0.001);
        assert!((v_min - 200.0 / 512.0).abs() < 0.001);
        assert!((u_max - 150.0 / 512.0).abs() < 0.001);
        assert!((v_max - 230.0 / 512.0).abs() < 0.001);
    }

    #[test]
    fn test_font_atlas_new() {
        let atlas = FontAtlas::new();
        assert_eq!(atlas.size(), INITIAL_ATLAS_SIZE);
        assert!(atlas.glyphs.is_empty());
    }

    #[test]
    fn test_font_atlas_add_glyph() {
        let mut atlas = FontAtlas::new();

        let key = GlyphKey {
            ch: 'A',
            size_tenths: 160,
        };
        let bitmap = vec![255u8; 10 * 12];

        let region = atlas.add_glyph(key, 10, 12, &bitmap);
        assert!(region.is_some());
        assert!(atlas.dirty);

        // Should be cached now
        assert!(atlas.get_glyph(key).is_some());
    }

    #[test]
    fn test_font_atlas_multiple_glyphs() {
        let mut atlas = FontAtlas::new();

        for ch in 'A'..='Z' {
            let key = GlyphKey {
                ch,
                size_tenths: 160,
            };
            let bitmap = vec![128u8; 10 * 12];

            let region = atlas.add_glyph(key, 10, 12, &bitmap);
            assert!(region.is_some());
        }

        assert_eq!(atlas.glyphs.len(), 26);
    }

    #[test]
    fn test_texture_manager_new() {
        let manager = TextureManager::new();
        assert!(manager.textures.is_empty());
        assert_eq!(manager.next_id, 1);
    }

    #[test]
    fn test_glyph_key_hash() {
        use std::collections::HashSet;

        let mut set = HashSet::new();
        set.insert(GlyphKey {
            ch: 'A',
            size_tenths: 160,
        });
        set.insert(GlyphKey {
            ch: 'B',
            size_tenths: 160,
        });
        set.insert(GlyphKey {
            ch: 'A',
            size_tenths: 200,
        });

        assert_eq!(set.len(), 3);
    }

    #[test]
    fn test_atlas_stats_empty() {
        let atlas = FontAtlas::new();
        let stats = atlas.stats();

        assert_eq!(stats.glyph_count, 0);
        assert_eq!(stats.used_pixels, 0);
        assert_eq!(stats.allocated_pixels, 0);
        assert_eq!(stats.atlas_size, INITIAL_ATLAS_SIZE);
        assert!((stats.fragmentation - 0.0).abs() < 0.001);
        assert!(!stats.needs_defragmentation());
    }

    #[test]
    fn test_atlas_stats_with_glyphs() {
        let mut atlas = FontAtlas::new();

        // Add a glyph
        let key = GlyphKey {
            ch: 'X',
            size_tenths: 160,
        };
        let bitmap = vec![255u8; 10 * 12];
        atlas.add_glyph(key, 10, 12, &bitmap);

        let stats = atlas.stats();
        assert_eq!(stats.glyph_count, 1);
        assert_eq!(stats.used_pixels, 10 * 12);
        // Allocated includes padding: (10+1) * (12+1) = 143
        assert_eq!(stats.allocated_pixels, 11 * 13);
    }

    #[test]
    fn test_atlas_defragmentation_not_needed() {
        let mut atlas = FontAtlas::new();

        // Add a few glyphs with good packing
        for ch in 'A'..='D' {
            let key = GlyphKey {
                ch,
                size_tenths: 160,
            };
            let bitmap = vec![128u8; 10 * 12];
            atlas.add_glyph(key, 10, 12, &bitmap);
        }

        // With uniform sizes, fragmentation should be low
        assert!(!atlas.needs_defragmentation());
        assert!(!atlas.defragment()); // Should return false
    }

    #[test]
    fn test_atlas_clear_resets_stats() {
        let mut atlas = FontAtlas::new();

        // Add some glyphs
        for ch in 'A'..='Z' {
            let key = GlyphKey {
                ch,
                size_tenths: 160,
            };
            let bitmap = vec![128u8; 10 * 12];
            atlas.add_glyph(key, 10, 12, &bitmap);
        }

        let stats_before = atlas.stats();
        assert!(stats_before.glyph_count > 0);
        assert!(stats_before.used_pixels > 0);

        atlas.clear();

        let stats_after = atlas.stats();
        assert_eq!(stats_after.glyph_count, 0);
        assert_eq!(stats_after.used_pixels, 0);
        assert_eq!(stats_after.allocated_pixels, 0);
    }

    #[test]
    fn test_atlas_stats_defrag_threshold() {
        // Verify the defrag threshold constant
        let stats = AtlasStats {
            glyph_count: 10,
            used_pixels: 100,
            allocated_pixels: 250, // 60% fragmentation (100/250 = 40% used)
            atlas_size: 512,
            fragmentation: 0.6,
        };
        assert!(stats.needs_defragmentation());

        let stats = AtlasStats {
            glyph_count: 10,
            used_pixels: 100,
            allocated_pixels: 150, // 33% fragmentation
            atlas_size: 512,
            fragmentation: 0.33,
        };
        assert!(!stats.needs_defragmentation());
    }

    #[test]
    fn test_atlas_stores_bitmaps() {
        let mut atlas = FontAtlas::new();

        let key = GlyphKey {
            ch: 'A',
            size_tenths: 160,
        };
        let bitmap = vec![255u8; 10 * 12];
        atlas.add_glyph(key, 10, 12, &bitmap);

        // Bitmap should be stored for defragmentation
        assert!(atlas.glyph_bitmaps.contains_key(&key));
        assert_eq!(atlas.glyph_bitmaps.get(&key).unwrap().len(), 10 * 12);
    }
}
