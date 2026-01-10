//! Default embedded font for text rendering.
//!
//! This module provides a default monospace font (Roboto Mono) for rendering
//! text when no custom font is loaded. The font is embedded directly in the
//! binary to ensure text rendering works without external dependencies.
//!
//! # License
//!
//! Roboto Mono is licensed under the Apache License, Version 2.0.
//! See: <https://github.com/google/fonts/tree/main/apache/robotomono>

/// Default font data (Roboto Mono Regular).
///
/// This is a variable-weight TrueType font embedded directly in the binary.
/// Use this with `Renderer::load_font()` to enable text rendering.
///
/// # Example
///
/// ```ignore
/// use rource_render::{Renderer, SoftwareRenderer, default_font};
///
/// let mut renderer = SoftwareRenderer::new(800, 600);
/// let font_id = renderer.load_font(default_font::ROBOTO_MONO).unwrap();
/// ```
pub static ROBOTO_MONO: &[u8] = include_bytes!("../assets/RobotoMono-Regular.ttf");

/// Returns the default font data.
///
/// This is a convenience function that returns the embedded Roboto Mono font.
#[inline]
pub fn default_font_data() -> &'static [u8] {
    ROBOTO_MONO
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_font_data_not_empty() {
        assert!(!ROBOTO_MONO.is_empty());
    }

    #[test]
    fn test_font_data_has_ttf_signature() {
        // TrueType/OpenType fonts start with specific magic bytes
        // - TrueType: 0x00010000
        // - OpenType: 'OTTO'
        // - TrueType Collection: 'ttcf'
        assert!(ROBOTO_MONO.len() > 4);

        // Check for variable font signature (TrueType outlines)
        // First 4 bytes should be 0x00010000 for TrueType
        let is_truetype =
            ROBOTO_MONO[0] == 0x00 && ROBOTO_MONO[1] == 0x01 && ROBOTO_MONO[2] == 0x00;

        // Or 'OTTO' for OpenType with CFF outlines
        let is_opentype = ROBOTO_MONO[0] == b'O'
            && ROBOTO_MONO[1] == b'T'
            && ROBOTO_MONO[2] == b'T'
            && ROBOTO_MONO[3] == b'O';

        assert!(
            is_truetype || is_opentype,
            "Font should have valid TrueType or OpenType signature"
        );
    }

    #[test]
    fn test_default_font_data_function() {
        let data = default_font_data();
        assert_eq!(data.as_ptr(), ROBOTO_MONO.as_ptr());
    }
}
