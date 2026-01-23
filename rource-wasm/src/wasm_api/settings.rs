// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Visual settings control.
//!
//! This module provides methods to configure visual appearance:
//! - Bloom effect toggle
//! - Background color
//! - Label visibility and font size
//! - Watermark configuration
//! - File icons (all backends)
//! - Vsync mode (wgpu only)

use wasm_bindgen::prelude::*;

use rource_core::config::{WatermarkPosition, WatermarkSettings};
use rource_math::Color;

use crate::Rource;

#[cfg(target_arch = "wasm32")]
use rource_render::backend::wgpu::VsyncMode;

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
    // Watermark
    // ========================================================================

    /// Enables the Rource brand watermark preset.
    ///
    /// This shows "Rource" with "© Tom F" in the bottom-right corner
    /// with subtle opacity for non-intrusive branding.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.enableRourceWatermark();
    /// ```
    #[wasm_bindgen(js_name = enableRourceWatermark)]
    pub fn enable_rource_watermark(&mut self) {
        self.settings.overlay.watermark = WatermarkSettings::rource_brand();
    }

    /// Disables the watermark.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.disableWatermark();
    /// ```
    #[wasm_bindgen(js_name = disableWatermark)]
    pub fn disable_watermark(&mut self) {
        self.settings.overlay.watermark.enabled = false;
    }

    /// Returns whether the watermark is enabled.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// if (rource.isWatermarkEnabled()) {
    ///     console.log('Watermark is visible');
    /// }
    /// ```
    #[wasm_bindgen(js_name = isWatermarkEnabled)]
    pub fn is_watermark_enabled(&self) -> bool {
        self.settings.overlay.watermark.enabled
    }

    /// Sets whether the watermark is enabled.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setWatermarkEnabled(true);
    /// ```
    #[wasm_bindgen(js_name = setWatermarkEnabled)]
    pub fn set_watermark_enabled(&mut self, enabled: bool) {
        self.settings.overlay.watermark.enabled = enabled;
    }

    /// Sets the primary watermark text.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setWatermarkText("My Project");
    /// ```
    #[wasm_bindgen(js_name = setWatermarkText)]
    pub fn set_watermark_text(&mut self, text: &str) {
        self.settings.overlay.watermark.text = text.to_string();
    }

    /// Sets the secondary watermark text (displayed below the primary text).
    ///
    /// Pass an empty string to clear the subtext.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setWatermarkSubtext("© 2026 My Company");
    /// ```
    #[wasm_bindgen(js_name = setWatermarkSubtext)]
    pub fn set_watermark_subtext(&mut self, text: &str) {
        if text.is_empty() {
            self.settings.overlay.watermark.subtext = None;
        } else {
            self.settings.overlay.watermark.subtext = Some(text.to_string());
        }
    }

    /// Sets the watermark position.
    ///
    /// Valid positions:
    /// - "top-left" or "tl"
    /// - "top-right" or "tr"
    /// - "bottom-left" or "bl"
    /// - "bottom-right" or "br" (default)
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setWatermarkPosition("bottom-left");
    /// ```
    #[wasm_bindgen(js_name = setWatermarkPosition)]
    pub fn set_watermark_position(&mut self, position: &str) {
        if let Some(pos) = WatermarkPosition::from_str(position) {
            self.settings.overlay.watermark.position = pos;
        }
    }

    /// Sets the watermark opacity (0.0 = invisible, 1.0 = fully opaque).
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setWatermarkOpacity(0.5);
    /// ```
    #[wasm_bindgen(js_name = setWatermarkOpacity)]
    pub fn set_watermark_opacity(&mut self, opacity: f32) {
        self.settings.overlay.watermark.opacity = opacity.clamp(0.0, 1.0);
    }

    /// Gets the current watermark opacity.
    #[wasm_bindgen(js_name = getWatermarkOpacity)]
    pub fn get_watermark_opacity(&self) -> f32 {
        self.settings.overlay.watermark.opacity
    }

    /// Sets the watermark font size.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setWatermarkFontSize(16);
    /// ```
    #[wasm_bindgen(js_name = setWatermarkFontSize)]
    pub fn set_watermark_font_size(&mut self, size: f32) {
        self.settings.overlay.watermark.font_size = size.clamp(4.0, 100.0);
    }

    /// Sets the watermark text color (hex string like "#FFFFFF" or "FFFFFF").
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setWatermarkColor("#FFFFFF");
    /// ```
    #[wasm_bindgen(js_name = setWatermarkColor)]
    pub fn set_watermark_color(&mut self, hex: &str) {
        let hex = hex.trim_start_matches('#');
        if hex.len() == 6 {
            if let Ok(val) = u32::from_str_radix(hex, 16) {
                self.settings.overlay.watermark.color = Color::from_hex(val);
            }
        }
    }

    /// Sets the watermark margin from the screen edge in pixels.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setWatermarkMargin(20);
    /// ```
    #[wasm_bindgen(js_name = setWatermarkMargin)]
    pub fn set_watermark_margin(&mut self, margin: f32) {
        self.settings.overlay.watermark.margin = margin.max(0.0);
    }

    /// Sets a custom watermark with both primary and secondary text.
    ///
    /// This is a convenience method that enables the watermark and sets both text values.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setCustomWatermark("My Project", "© 2026 My Company");
    /// ```
    #[wasm_bindgen(js_name = setCustomWatermark)]
    pub fn set_custom_watermark(&mut self, text: &str, subtext: &str) {
        self.settings.overlay.watermark.enabled = true;
        self.settings.overlay.watermark.text = text.to_string();
        if subtext.is_empty() {
            self.settings.overlay.watermark.subtext = None;
        } else {
            self.settings.overlay.watermark.subtext = Some(subtext.to_string());
        }
    }

    // ========================================================================
    // File Icons (all backends)
    // ========================================================================

    /// Initializes the file icon system.
    ///
    /// This pre-generates icons for common file extensions (rs, js, py, etc.)
    /// and stores them for efficient rendering:
    /// - **wgpu**: Uses GPU texture arrays for batched rendering
    /// - **WebGL2**: Uses GPU texture arrays (WebGL2 supports `TEXTURE_2D_ARRAY`)
    /// - **Software**: Uses CPU textures
    ///
    /// # Returns
    ///
    /// `true` if initialization succeeded, `false` otherwise.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// const success = rource.initFileIcons();
    /// console.log('File icons initialized:', success);
    /// ```
    #[wasm_bindgen(js_name = initFileIcons)]
    pub fn init_file_icons(&mut self) -> bool {
        // Try wgpu first
        #[cfg(target_arch = "wasm32")]
        if let Some(wgpu_renderer) = self.backend.as_wgpu_mut() {
            return wgpu_renderer.init_file_icons();
        }

        // Try WebGL2
        if let Some(webgl2_renderer) = self.backend.as_webgl2_mut() {
            return webgl2_renderer.init_file_icons();
        }

        // Try Software
        if let Some(software_renderer) = self.backend.as_software_mut() {
            return software_renderer.init_file_icons();
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
        // Try wgpu first
        #[cfg(target_arch = "wasm32")]
        if let Some(wgpu_renderer) = self.backend.as_wgpu() {
            return wgpu_renderer.has_file_icons();
        }

        // Try WebGL2
        if let Some(webgl2_renderer) = self.backend.as_webgl2() {
            return webgl2_renderer.has_file_icons();
        }

        // Try Software
        if let Some(software_renderer) = self.backend.as_software() {
            return software_renderer.has_file_icons();
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
        // Try wgpu first
        #[cfg(target_arch = "wasm32")]
        if let Some(wgpu_renderer) = self.backend.as_wgpu() {
            return wgpu_renderer.file_icon_count();
        }

        // Try WebGL2
        if let Some(webgl2_renderer) = self.backend.as_webgl2() {
            return webgl2_renderer.file_icon_count();
        }

        // Try Software
        if let Some(software_renderer) = self.backend.as_software() {
            return software_renderer.file_icon_count();
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

        // Try wgpu first
        #[cfg(target_arch = "wasm32")]
        if let Some(wgpu_renderer) = self.backend.as_wgpu_mut() {
            return wgpu_renderer.register_file_icon(extension, color);
        }

        // Try WebGL2
        if let Some(webgl2_renderer) = self.backend.as_webgl2_mut() {
            return webgl2_renderer.register_file_icon(extension, color);
        }

        // Try Software
        if let Some(software_renderer) = self.backend.as_software_mut() {
            return software_renderer.register_file_icon(extension, color);
        }

        false
    }

    // ========================================================================
    // Vsync Mode (wgpu only)
    // ========================================================================

    /// Sets vsync mode for the renderer.
    ///
    /// This controls whether frames are synchronized to the display refresh rate:
    /// - `true` (default): Vsync enabled, frames sync to display refresh (~60 FPS)
    /// - `false`: Vsync disabled, uncapped frame rate (300+ FPS possible)
    ///
    /// **Note:** This only affects the wgpu backend (WebGPU). WebGL2 and software
    /// renderers always use requestAnimationFrame timing which is vsync-aligned.
    ///
    /// **Performance Impact:** Disabling vsync increases GPU utilization and power
    /// consumption. Use with caution on battery-powered devices.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// // Disable vsync for uncapped FPS
    /// rource.setVsync(false);
    ///
    /// // Re-enable vsync for power efficiency
    /// rource.setVsync(true);
    /// ```
    #[wasm_bindgen(js_name = setVsync)]
    pub fn set_vsync(&mut self, enabled: bool) {
        // wgpu backend supports vsync mode configuration
        #[cfg(target_arch = "wasm32")]
        if let Some(wgpu_renderer) = self.backend.as_wgpu_mut() {
            let mode = if enabled {
                VsyncMode::Enabled
            } else {
                VsyncMode::Disabled
            };
            wgpu_renderer.set_vsync_mode(mode);
        }

        // Suppress unused variable warning on non-wasm32 targets
        #[cfg(not(target_arch = "wasm32"))]
        let _ = enabled;
    }

    /// Returns whether vsync is currently enabled.
    ///
    /// Returns `true` if:
    /// - Using wgpu backend with vsync enabled
    /// - Using WebGL2 or software backend (always vsync-aligned)
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// const vsyncEnabled = rource.isVsyncEnabled();
    /// console.log('Vsync:', vsyncEnabled ? 'ON' : 'OFF');
    /// ```
    #[wasm_bindgen(js_name = isVsyncEnabled)]
    pub fn is_vsync_enabled(&self) -> bool {
        #[cfg(target_arch = "wasm32")]
        if let Some(wgpu_renderer) = self.backend.as_wgpu() {
            return wgpu_renderer.is_vsync_enabled();
        }

        // WebGL2 and software are always vsync-aligned via requestAnimationFrame
        true
    }
}
