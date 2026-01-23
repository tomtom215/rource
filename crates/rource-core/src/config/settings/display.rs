// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Display and visual settings.

use rource_math::Color;

/// Display settings for visual elements.
#[derive(Debug, Clone)]
pub struct DisplaySettings {
    /// Window/viewport width in pixels.
    pub width: u32,
    /// Window/viewport height in pixels.
    pub height: u32,
    /// Run in fullscreen mode.
    pub fullscreen: bool,
    /// Background color.
    pub background_color: Color,
    /// Font size for labels.
    pub font_size: f32,
    /// Enable bloom/glow effect.
    pub bloom_enabled: bool,
    /// Bloom intensity (0.0 - 2.0).
    pub bloom_intensity: f32,
    /// Enable drop shadows.
    pub shadows_enabled: bool,
}

impl Default for DisplaySettings {
    fn default() -> Self {
        Self {
            width: 1280,
            height: 720,
            fullscreen: false,
            background_color: Color::BLACK,
            font_size: 12.0,
            bloom_enabled: true,
            bloom_intensity: 1.0,
            shadows_enabled: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_display_settings_default() {
        let display = DisplaySettings::default();
        assert_eq!(display.width, 1280);
        assert_eq!(display.height, 720);
        assert!(!display.fullscreen);
        assert!(display.bloom_enabled);
    }
}
