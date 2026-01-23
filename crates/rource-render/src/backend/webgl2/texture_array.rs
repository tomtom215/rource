//! WebGL2 texture array for efficient file icon batching.
//!
//! This module provides GPU texture array support for WebGL2, allowing multiple
//! file icons to be stored in a single texture and rendered with a single draw call.
//!
//! ## Architecture
//!
//! WebGL2 supports `TEXTURE_2D_ARRAY` via the ES 3.0 specification. Each layer
//! in the array represents a different file extension icon. The shader samples
//! from the appropriate layer using the instance's layer index.
//!
//! ## Performance
//!
//! - Single bind group for all icons
//! - Single draw call per frame for all file icons
//! - No texture switching overhead

use std::collections::HashMap;

use web_sys::{WebGl2RenderingContext, WebGlTexture};

/// Maximum number of layers in the texture array.
pub const MAX_TEXTURE_ARRAY_LAYERS: u32 = 256;

/// Default icon size in pixels (32x32).
pub const DEFAULT_ICON_SIZE: u32 = 32;

/// Statistics about texture array usage.
#[derive(Debug, Clone, Copy, Default)]
pub struct TextureArrayStats {
    /// Width of each layer in pixels.
    pub width: u32,
    /// Height of each layer in pixels.
    pub height: u32,
    /// Number of allocated layers.
    pub layer_count: u32,
    /// Maximum number of layers.
    pub max_layers: u32,
    /// Total memory used in bytes.
    pub memory_bytes: u64,
}

/// A 2D texture array for storing file icons.
///
/// Each layer in the array stores a 32x32 RGBA icon for a file extension.
/// Extensions are mapped to layer indices for efficient lookup.
#[derive(Debug)]
pub struct TextureArray {
    /// WebGL texture handle.
    texture: Option<WebGlTexture>,
    /// Width of each layer.
    width: u32,
    /// Height of each layer.
    height: u32,
    /// Maximum number of layers.
    max_layers: u32,
    /// Current number of allocated layers.
    layer_count: u32,
    /// Extension to layer index mapping.
    extension_map: HashMap<String, u32>,
    /// Whether the texture has been created.
    initialized: bool,
}

impl TextureArray {
    /// Creates a new texture array.
    ///
    /// # Arguments
    ///
    /// * `gl` - WebGL2 rendering context
    /// * `width` - Width of each layer in pixels
    /// * `height` - Height of each layer in pixels
    /// * `max_layers` - Maximum number of layers
    pub fn new(
        gl: &WebGl2RenderingContext,
        width: u32,
        height: u32,
        max_layers: u32,
    ) -> Option<Self> {
        let texture = gl.create_texture()?;

        // Bind and configure the texture array
        gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D_ARRAY, Some(&texture));

        // Pre-allocate storage for the texture array
        // This allows us to update individual layers later via tex_sub_image_3d
        gl.tex_storage_3d(
            WebGl2RenderingContext::TEXTURE_2D_ARRAY,
            1, // mip levels
            WebGl2RenderingContext::RGBA8,
            width as i32,
            height as i32,
            max_layers as i32,
        );

        // Check for WebGL errors
        if gl.get_error() != WebGl2RenderingContext::NO_ERROR {
            gl.delete_texture(Some(&texture));
            return None;
        }

        // Set texture parameters
        gl.tex_parameteri(
            WebGl2RenderingContext::TEXTURE_2D_ARRAY,
            WebGl2RenderingContext::TEXTURE_MIN_FILTER,
            WebGl2RenderingContext::LINEAR as i32,
        );
        gl.tex_parameteri(
            WebGl2RenderingContext::TEXTURE_2D_ARRAY,
            WebGl2RenderingContext::TEXTURE_MAG_FILTER,
            WebGl2RenderingContext::LINEAR as i32,
        );
        gl.tex_parameteri(
            WebGl2RenderingContext::TEXTURE_2D_ARRAY,
            WebGl2RenderingContext::TEXTURE_WRAP_S,
            WebGl2RenderingContext::CLAMP_TO_EDGE as i32,
        );
        gl.tex_parameteri(
            WebGl2RenderingContext::TEXTURE_2D_ARRAY,
            WebGl2RenderingContext::TEXTURE_WRAP_T,
            WebGl2RenderingContext::CLAMP_TO_EDGE as i32,
        );

        gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D_ARRAY, None);

        Some(Self {
            texture: Some(texture),
            width,
            height,
            max_layers,
            layer_count: 0,
            extension_map: HashMap::new(),
            initialized: true,
        })
    }

    /// Adds a new layer with RGBA data.
    ///
    /// # Arguments
    ///
    /// * `gl` - WebGL2 rendering context
    /// * `data` - RGBA8 pixel data (must be width * height * 4 bytes)
    ///
    /// # Returns
    ///
    /// The layer index if successful, `None` if the array is full.
    pub fn add_layer(&mut self, gl: &WebGl2RenderingContext, data: &[u8]) -> Option<u32> {
        if self.layer_count >= self.max_layers {
            return None;
        }

        let expected_size = (self.width * self.height * 4) as usize;
        if data.len() != expected_size {
            return None;
        }

        let texture = self.texture.as_ref()?;
        let layer = self.layer_count;

        gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D_ARRAY, Some(texture));

        // Upload the layer data using tex_sub_image_3d
        if gl
            .tex_sub_image_3d_with_opt_u8_array(
                WebGl2RenderingContext::TEXTURE_2D_ARRAY,
                0,                    // mip level
                0,                    // x offset
                0,                    // y offset
                layer as i32,         // z offset (layer)
                self.width as i32,    // width
                self.height as i32,   // height
                1,                    // depth (1 layer)
                WebGl2RenderingContext::RGBA,
                WebGl2RenderingContext::UNSIGNED_BYTE,
                Some(data),
            )
            .is_err()
        {
            gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D_ARRAY, None);
            return None;
        }

        gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D_ARRAY, None);

        self.layer_count += 1;
        Some(layer)
    }

    /// Registers an extension with icon data.
    ///
    /// # Arguments
    ///
    /// * `gl` - WebGL2 rendering context
    /// * `extension` - File extension (e.g., "rs", "js")
    /// * `data` - RGBA8 icon data
    ///
    /// # Returns
    ///
    /// The layer index if successful, `None` if registration failed.
    pub fn register_extension(
        &mut self,
        gl: &WebGl2RenderingContext,
        extension: &str,
        data: &[u8],
    ) -> Option<u32> {
        // Check if already registered
        if let Some(&layer) = self.extension_map.get(extension) {
            return Some(layer);
        }

        // Add the layer
        let layer = self.add_layer(gl, data)?;

        // Store the mapping
        self.extension_map.insert(extension.to_lowercase(), layer);

        Some(layer)
    }

    /// Gets the layer index for an extension.
    ///
    /// # Arguments
    ///
    /// * `extension` - File extension (case-insensitive)
    ///
    /// # Returns
    ///
    /// The layer index if found, `None` otherwise.
    #[inline]
    pub fn get_layer(&self, extension: &str) -> Option<u32> {
        self.extension_map.get(&extension.to_lowercase()).copied()
    }

    /// Returns whether an extension is registered.
    #[inline]
    pub fn has_extension(&self, extension: &str) -> bool {
        self.extension_map.contains_key(&extension.to_lowercase())
    }

    /// Returns the number of allocated layers.
    #[inline]
    pub fn layer_count(&self) -> u32 {
        self.layer_count
    }

    /// Returns the maximum number of layers.
    #[inline]
    pub fn max_layers(&self) -> u32 {
        self.max_layers
    }

    /// Returns whether the texture array is initialized.
    #[inline]
    pub fn is_initialized(&self) -> bool {
        self.initialized && self.texture.is_some()
    }

    /// Returns statistics about texture array usage.
    pub fn stats(&self) -> TextureArrayStats {
        TextureArrayStats {
            width: self.width,
            height: self.height,
            layer_count: self.layer_count,
            max_layers: self.max_layers,
            memory_bytes: u64::from(self.width) * u64::from(self.height) * 4 * u64::from(self.layer_count),
        }
    }

    /// Binds the texture array to a texture unit.
    ///
    /// # Arguments
    ///
    /// * `gl` - WebGL2 rendering context
    /// * `unit` - Texture unit (0, 1, 2, etc.)
    pub fn bind(&self, gl: &WebGl2RenderingContext, unit: u32) {
        if let Some(texture) = &self.texture {
            gl.active_texture(WebGl2RenderingContext::TEXTURE0 + unit);
            gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D_ARRAY, Some(texture));
        }
    }

    /// Unbinds the texture array.
    pub fn unbind(&self, gl: &WebGl2RenderingContext) {
        gl.bind_texture(WebGl2RenderingContext::TEXTURE_2D_ARRAY, None);
    }

    /// Releases WebGL resources.
    pub fn destroy(&mut self, gl: &WebGl2RenderingContext) {
        if let Some(texture) = self.texture.take() {
            gl.delete_texture(Some(&texture));
        }
        self.extension_map.clear();
        self.layer_count = 0;
        self.initialized = false;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_texture_array_stats_default() {
        let stats = TextureArrayStats::default();
        assert_eq!(stats.width, 0);
        assert_eq!(stats.height, 0);
        assert_eq!(stats.layer_count, 0);
        assert_eq!(stats.max_layers, 0);
        assert_eq!(stats.memory_bytes, 0);
    }

    #[test]
    fn test_texture_array_stats_memory_calculation() {
        let stats = TextureArrayStats {
            width: 32,
            height: 32,
            layer_count: 10,
            max_layers: 64,
            memory_bytes: 32 * 32 * 4 * 10,
        };
        assert_eq!(stats.memory_bytes, 40960); // 32 * 32 * 4 * 10
    }
}
