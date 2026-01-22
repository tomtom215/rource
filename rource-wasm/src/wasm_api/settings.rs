//! Visual settings control.
//!
//! This module provides methods to configure visual appearance:
//! - Bloom effect toggle
//! - Background color
//! - Label visibility and font size

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
}
