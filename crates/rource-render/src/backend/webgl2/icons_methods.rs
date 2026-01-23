//! File icon methods for the WebGL2 renderer.
//!
//! This module contains methods for managing file extension icons using
//! the texture array infrastructure. WebGL2 supports `TEXTURE_2D_ARRAY`
//! via the ES 3.0 specification.

use super::{texture_array::TextureArray, WebGl2Renderer};
use crate::backend::icons::{common_extensions, generate_default_icon, generate_icon, ICON_SIZE};
use rource_math::Color;

impl WebGl2Renderer {
    /// Initializes the file icon texture array.
    ///
    /// This pre-registers icons for common file extensions. Call this once
    /// during initialization if you want to use file icon rendering.
    ///
    /// # Returns
    ///
    /// `true` if initialization succeeded, `false` otherwise.
    pub fn init_file_icons(&mut self) -> bool {
        if self.context_lost {
            return false;
        }

        // Create texture array
        let Some(mut array) = TextureArray::new(
            &self.gl,
            ICON_SIZE as u32,
            ICON_SIZE as u32,
            64, // Max 64 file types
        ) else {
            return false;
        };

        // Register common file extensions
        for (ext, color) in common_extensions() {
            let icon_data = generate_icon(color);
            array.register_extension(&self.gl, ext, &icon_data);
        }

        // Register default icon for unknown extensions
        let default_icon = generate_default_icon();
        array.register_extension(&self.gl, "_default", &default_icon);

        self.file_icon_array = Some(array);
        true
    }

    /// Returns the icon layer index for a file extension.
    ///
    /// If the extension is not registered, returns the default icon layer.
    /// If file icons are not initialized, returns `None`.
    ///
    /// # Arguments
    ///
    /// * `extension` - File extension (e.g., "rs", "js", "py")
    pub fn get_file_icon_layer(&self, extension: &str) -> Option<u32> {
        let array = self.file_icon_array.as_ref()?;

        // Try to find the extension
        if let Some(layer) = array.get_layer(extension) {
            return Some(layer);
        }

        // Fall back to default
        array.get_layer("_default")
    }

    /// Registers a custom icon for a file extension.
    ///
    /// If the extension is already registered, this does nothing.
    /// If file icons are not initialized, returns `false`.
    ///
    /// # Arguments
    ///
    /// * `extension` - File extension (e.g., "custom")
    /// * `color` - Color for the icon
    ///
    /// # Returns
    ///
    /// `true` if the icon was registered, `false` otherwise.
    pub fn register_file_icon(&mut self, extension: &str, color: Color) -> bool {
        if self.context_lost {
            return false;
        }

        let Some(array) = self.file_icon_array.as_mut() else {
            return false;
        };

        // Check if already registered
        if array.has_extension(extension) {
            return true;
        }

        // Generate and register icon
        let icon_data = generate_icon(color);
        array
            .register_extension(&self.gl, extension, &icon_data)
            .is_some()
    }

    /// Returns whether file icons are initialized.
    #[inline]
    pub fn has_file_icons(&self) -> bool {
        self.file_icon_array.is_some()
    }

    /// Returns the number of registered file icon types.
    pub fn file_icon_count(&self) -> u32 {
        self.file_icon_array
            .as_ref()
            .map_or(0, TextureArray::layer_count)
    }

    /// Binds the file icon texture array to a texture unit.
    ///
    /// # Arguments
    ///
    /// * `unit` - Texture unit (0, 1, 2, etc.)
    ///
    /// # Returns
    ///
    /// `true` if the texture was bound, `false` if icons are not initialized.
    pub fn bind_file_icons(&self, unit: u32) -> bool {
        self.file_icon_array.as_ref().is_some_and(|array| {
            array.bind(&self.gl, unit);
            true
        })
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_icon_size_constant() {
        // Verify ICON_SIZE is accessible and correct
        assert_eq!(super::ICON_SIZE, 32);
    }
}
