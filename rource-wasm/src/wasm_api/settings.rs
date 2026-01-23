//! Visual settings control.
//!
//! This module provides methods to configure visual appearance:
//! - Bloom effect toggle
//! - Background color
//! - Label visibility and font size
//! - File icons (wgpu only)

use wasm_bindgen::prelude::*;

use rource_math::Color;

use crate::Rource;

// ============================================================================
// Visual Settings
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Sets whether to show bloom effect.
    ///
    /// Bloom creates a glow around bright elements.
    #[wasm_bindgen(js_name = setBloom)]
    pub fn set_bloom(&mut self, enabled: bool) {
        self.settings.display.bloom_enabled = enabled;
    }

    /// Sets the background color (hex string like "#000000" or "000000").
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setBackgroundColor("#1a1a2e");
    /// ```
    #[wasm_bindgen(js_name = setBackgroundColor)]
    pub fn set_background_color(&mut self, hex: &str) {
        let hex = hex.trim_start_matches('#');
        if hex.len() == 6 {
            if let Ok(val) = u32::from_str_radix(hex, 16) {
                self.settings.display.background_color = Color::from_hex(val);
            }
        }
    }

    /// Sets whether to show labels (user names, file names, directory names).
    #[wasm_bindgen(js_name = setShowLabels)]
    pub fn set_show_labels(&mut self, show: bool) {
        self.show_labels = show;
    }

    /// Gets whether labels are being shown.
    #[wasm_bindgen(js_name = getShowLabels)]
    pub fn get_show_labels(&self) -> bool {
        self.show_labels
    }

    /// Sets the font size for labels.
    ///
    /// Range: [4.0, 200.0]
    #[wasm_bindgen(js_name = setFontSize)]
    pub fn set_font_size(&mut self, size: f32) {
        self.settings.display.font_size = size.clamp(4.0, 200.0);
    }

    /// Gets the current font size for labels.
    #[wasm_bindgen(js_name = getFontSize)]
    pub fn get_font_size(&self) -> f32 {
        self.settings.display.font_size
    }

    // ========================================================================
    // File Icons (wgpu only)
    // ========================================================================

    /// Initializes the file icon system.
    ///
    /// This pre-generates icons for common file extensions (rs, js, py, etc.)
    /// and stores them in a GPU texture array for efficient batched rendering.
    ///
    /// **Note**: Only has an effect when using the wgpu backend.
    ///
    /// # Returns
    ///
    /// `true` if initialization succeeded, `false` otherwise.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// if (rource.isWgpu()) {
    ///     const success = rource.initFileIcons();
    ///     console.log('File icons initialized:', success);
    /// }
    /// ```
    #[wasm_bindgen(js_name = initFileIcons)]
    pub fn init_file_icons(&mut self) -> bool {
        #[cfg(target_arch = "wasm32")]
        if let Some(wgpu_renderer) = self.backend.as_wgpu_mut() {
            return wgpu_renderer.init_file_icons();
        }
        false
    }

    /// Returns whether file icons are initialized.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// if (rource.hasFileIcons()) {
    ///     console.log('File icons ready');
    /// }
    /// ```
    #[wasm_bindgen(js_name = hasFileIcons)]
    pub fn has_file_icons(&self) -> bool {
        #[cfg(target_arch = "wasm32")]
        if let Some(wgpu_renderer) = self.backend.as_wgpu() {
            return wgpu_renderer.has_file_icons();
        }
        false
    }

    /// Returns the number of registered file icon types.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// const count = rource.getFileIconCount();
    /// console.log(`${count} file types registered`);
    /// ```
    #[wasm_bindgen(js_name = getFileIconCount)]
    pub fn get_file_icon_count(&self) -> u32 {
        #[cfg(target_arch = "wasm32")]
        if let Some(wgpu_renderer) = self.backend.as_wgpu() {
            return wgpu_renderer.file_icon_count();
        }
        0
    }

    /// Registers a custom icon color for a file extension.
    ///
    /// If the extension is already registered, this does nothing.
    /// If file icons are not initialized, returns `false`.
    ///
    /// # Arguments
    ///
    /// * `extension` - File extension without dot (e.g., "custom", "myext")
    /// * `hex_color` - Color as hex string (e.g., "#FF5500" or "FF5500")
    ///
    /// # Returns
    ///
    /// `true` if the icon was registered, `false` otherwise.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// // Register a custom file extension with orange color
    /// rource.registerFileIcon("myext", "#FF5500");
    /// ```
    #[wasm_bindgen(js_name = registerFileIcon)]
    pub fn register_file_icon(&mut self, extension: &str, hex_color: &str) -> bool {
        let hex = hex_color.trim_start_matches('#');
        let color = if hex.len() == 6 {
            if let Ok(val) = u32::from_str_radix(hex, 16) {
                Color::from_hex(val)
            } else {
                return false;
            }
        } else {
            return false;
        };

        #[cfg(target_arch = "wasm32")]
        if let Some(wgpu_renderer) = self.backend.as_wgpu_mut() {
            return wgpu_renderer.register_file_icon(extension, color);
        }
        false
    }
}
