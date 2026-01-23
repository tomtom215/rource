// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Logo and background overlay settings.

/// Overlay settings for logo and background images.
#[derive(Debug, Clone, Default)]
pub struct OverlaySettings {
    /// Path to logo image file.
    pub logo_path: Option<String>,
    /// Logo position offset from top-right corner (x, y).
    pub logo_offset: (i32, i32),
    /// Path to background image file.
    pub background_image: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_overlay_settings_default() {
        let overlay = OverlaySettings::default();
        assert!(overlay.logo_path.is_none());
        assert_eq!(overlay.logo_offset, (0, 0));
        assert!(overlay.background_image.is_none());
    }
}
