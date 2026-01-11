//! WebGL2 texture management and font atlas.
//!
//! This module provides texture loading, font glyph caching in texture atlases,
//! and efficient texture switching for batched rendering.

use std::collections::HashMap;

use web_sys::{WebGl2RenderingContext, WebGlTexture};

use crate::TextureId;

/// Maximum atlas size (2048x2048 is widely supported).
const MAX_ATLAS_SIZE: u32 = 2048;

/// Initial atlas size.
const INITIAL_ATLAS_SIZE: u32 = 512;

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
    /// Whether atlas needs upload.
    dirty: bool,
    /// Whether atlas was resized.
    resized: bool,
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
            glyphs: HashMap::new(),
            dirty: false,
            resized: false,
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

        // If failed, try to resize atlas
        if region.is_none() && self.size < MAX_ATLAS_SIZE {
            self.resize(self.size * 2);
            region = self.packer.allocate(width, height);
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

    /// Clears the atlas (for context recovery).
    pub fn clear(&mut self) {
        self.glyphs.clear();
        self.packer = RowPacker::new(self.size);
        self.data.fill(0);
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
            textures: HashMap::new(),
            dimensions: HashMap::new(),
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
}
