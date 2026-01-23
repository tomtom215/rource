// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Screenshot and full-map export functionality.
//!
//! This module provides methods for exporting visualizations:
//! - Entity bounds calculation
//! - Full map dimensions for high-resolution export
//! - Screenshot capture to PNG

use wasm_bindgen::prelude::*;

use rource_core::camera::Camera;
use rource_math::Vec2;

use crate::png::write_png;
use crate::render_phases::AUTO_FIT_MIN_ZOOM;
use crate::Rource;

// ============================================================================
// Helper Functions (testable without Rource instance)
// ============================================================================

#[allow(dead_code)]
mod helpers {
    /// Maximum dimension for WebGL textures.
    pub const MAX_TEXTURE_DIMENSION: u32 = 16384;

    /// Default padding ratio for export bounds.
    pub const DEFAULT_PADDING: f32 = 0.2;

    /// Calculates padded dimensions with a given padding ratio.
    ///
    /// # Arguments
    /// * `width` - Original width
    /// * `height` - Original height
    /// * `padding` - Padding ratio (0.2 = 20% on each side)
    ///
    /// # Returns
    /// Tuple of (`padded_width`, `padded_height`).
    #[inline]
    #[must_use]
    pub fn calculate_padded_dimensions(width: f32, height: f32, padding: f32) -> (f32, f32) {
        let multiplier = 1.0 + padding * 2.0;
        (width * multiplier, height * multiplier)
    }

    /// Calculates the zoom level needed for readable labels.
    ///
    /// # Arguments
    /// * `min_label_font_size` - Minimum desired font size for labels
    /// * `base_font_size` - The base font size in settings
    ///
    /// # Returns
    /// The zoom level, clamped to at least 0.5.
    #[inline]
    #[must_use]
    pub fn calculate_readable_zoom(min_label_font_size: f32, base_font_size: f32) -> f32 {
        (min_label_font_size / base_font_size).max(0.5)
    }

    /// Calculates canvas dimensions from world dimensions and zoom.
    ///
    /// # Arguments
    /// * `world_width` - Width in world coordinates
    /// * `world_height` - Height in world coordinates
    /// * `zoom` - Zoom level
    ///
    /// # Returns
    /// Tuple of (`canvas_width`, `canvas_height`) as u32.
    #[inline]
    #[must_use]
    pub fn calculate_canvas_dimensions(
        world_width: f32,
        world_height: f32,
        zoom: f32,
    ) -> (u32, u32) {
        (
            (world_width * zoom).ceil() as u32,
            (world_height * zoom).ceil() as u32,
        )
    }

    /// Scales dimensions to fit within the maximum texture size.
    ///
    /// # Arguments
    /// * `width` - Original width
    /// * `height` - Original height
    /// * `zoom` - Original zoom level
    /// * `max_dimension` - Maximum allowed dimension
    ///
    /// # Returns
    /// Tuple of (`final_width`, `final_height`, `final_zoom`).
    #[must_use]
    pub fn scale_to_max_dimension(
        width: u32,
        height: u32,
        zoom: f32,
        max_dimension: u32,
    ) -> (u32, u32, f32) {
        if width > max_dimension || height > max_dimension {
            let scale = (max_dimension as f32) / (width.max(height) as f32);
            let scaled_width = ((width as f32) * scale).ceil() as u32;
            let scaled_height = ((height as f32) * scale).ceil() as u32;
            let scaled_zoom = zoom * scale;
            (scaled_width, scaled_height, scaled_zoom)
        } else {
            (width, height, zoom)
        }
    }

    /// Formats entity bounds as a JSON string.
    ///
    /// # Arguments
    /// * `min_x` - Minimum X coordinate
    /// * `min_y` - Minimum Y coordinate
    /// * `max_x` - Maximum X coordinate
    /// * `max_y` - Maximum Y coordinate
    ///
    /// # Returns
    /// JSON string with bounds information.
    #[must_use]
    pub fn format_bounds_json(min_x: f32, min_y: f32, max_x: f32, max_y: f32) -> String {
        let width = max_x - min_x;
        let height = max_y - min_y;
        format!(
            r#"{{"minX":{min_x},"minY":{min_y},"maxX":{max_x},"maxY":{max_y},"width":{width},"height":{height}}}"#
        )
    }

    /// Formats full map dimensions as a JSON string.
    ///
    /// # Arguments
    /// * `width` - Canvas width
    /// * `height` - Canvas height
    /// * `zoom` - Zoom level
    /// * `center_x` - Center X coordinate
    /// * `center_y` - Center Y coordinate
    ///
    /// # Returns
    /// JSON string with dimensions information.
    #[must_use]
    pub fn format_dimensions_json(
        width: u32,
        height: u32,
        zoom: f32,
        center_x: f32,
        center_y: f32,
    ) -> String {
        format!(
            r#"{{"width":{width},"height":{height},"zoom":{zoom},"centerX":{center_x},"centerY":{center_y}}}"#
        )
    }
}

#[allow(unused_imports)]
pub use helpers::*;

// ============================================================================
// Export / Screenshot API
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Returns the bounding box of all entities as JSON.
    ///
    /// Returns `{"minX", "minY", "maxX", "maxY", "width", "height"}` or null
    /// if no entities exist.
    #[wasm_bindgen(js_name = getEntityBounds)]
    pub fn get_entity_bounds(&mut self) -> Option<String> {
        self.scene.compute_entity_bounds().map(|bounds| {
            format!(
                r#"{{"minX":{},"minY":{},"maxX":{},"maxY":{},"width":{},"height":{}}}"#,
                bounds.min.x,
                bounds.min.y,
                bounds.max.x,
                bounds.max.y,
                bounds.width(),
                bounds.height()
            )
        })
    }

    /// Calculates the required canvas dimensions for full map export.
    ///
    /// Returns dimensions that ensure labels are readable at the specified
    /// minimum font size, capped at 16384 pixels per dimension.
    ///
    /// # Arguments
    /// * `min_label_font_size` - Minimum font size for readable labels (e.g., 8.0)
    ///
    /// # Returns
    /// JSON object: `{"width", "height", "zoom", "centerX", "centerY"}` or null
    #[wasm_bindgen(js_name = getFullMapDimensions)]
    pub fn get_full_map_dimensions(&mut self, min_label_font_size: f32) -> Option<String> {
        let bounds = self.scene.compute_entity_bounds()?;

        // Add padding around content
        let padding = 0.2;
        let padded_width = bounds.width() * (1.0 + padding * 2.0);
        let padded_height = bounds.height() * (1.0 + padding * 2.0);

        if padded_width <= 0.0 || padded_height <= 0.0 {
            return None;
        }

        // Calculate zoom needed for readable labels
        let base_font_size = self.settings.display.font_size;
        let readable_zoom = (min_label_font_size / base_font_size).max(0.5);

        let canvas_width = (padded_width * readable_zoom).ceil() as u32;
        let canvas_height = (padded_height * readable_zoom).ceil() as u32;

        // Cap at maximum WebGL texture size
        let max_dimension = 16384_u32;
        let (final_width, final_height, final_zoom) =
            if canvas_width > max_dimension || canvas_height > max_dimension {
                let scale = (max_dimension as f32) / (canvas_width.max(canvas_height) as f32);
                let scaled_width = ((canvas_width as f32) * scale).ceil() as u32;
                let scaled_height = ((canvas_height as f32) * scale).ceil() as u32;
                let scaled_zoom = readable_zoom * scale;
                (scaled_width, scaled_height, scaled_zoom)
            } else {
                (canvas_width, canvas_height, readable_zoom)
            };

        let center = bounds.center();

        Some(format!(
            r#"{{"width":{},"height":{},"zoom":{},"centerX":{},"centerY":{}}}"#,
            final_width, final_height, final_zoom, center.x, center.y
        ))
    }

    /// Prepares the renderer for full map export.
    ///
    /// Resizes canvas and positions camera for high-resolution capture.
    /// Call `forceRender()` after this, then `captureScreenshot()`.
    ///
    /// # Arguments
    /// * `width` - Target canvas width
    /// * `height` - Target canvas height
    /// * `zoom` - Zoom level for the export
    /// * `center_x` - World X coordinate for camera center
    /// * `center_y` - World Y coordinate for camera center
    #[wasm_bindgen(js_name = prepareFullMapExport)]
    pub fn prepare_full_map_export(
        &mut self,
        width: u32,
        height: u32,
        zoom: f32,
        center_x: f32,
        center_y: f32,
    ) {
        self.canvas.set_width(width);
        self.canvas.set_height(height);
        self.backend.resize(width, height);
        self.camera = Camera::new(width as f32, height as f32);
        // Use AUTO_FIT_MIN_ZOOM (0.03) as minimum to prevent LOD culling all entities
        self.camera.set_zoom_limits(AUTO_FIT_MIN_ZOOM, 1000.0);
        self.camera.jump_to(Vec2::new(center_x, center_y));
        self.camera.set_zoom(zoom);
        self.settings.display.width = width;
        self.settings.display.height = height;
    }

    /// Restores the renderer after full map export.
    ///
    /// Resizes canvas back to normal dimensions and fits camera to content.
    ///
    /// # Arguments
    /// * `width` - Original canvas width
    /// * `height` - Original canvas height
    #[wasm_bindgen(js_name = restoreAfterExport)]
    pub fn restore_after_export(&mut self, width: u32, height: u32) {
        self.canvas.set_width(width);
        self.canvas.set_height(height);
        self.backend.resize(width, height);
        self.camera = Camera::new(width as f32, height as f32);
        // Use AUTO_FIT_MIN_ZOOM (0.03) as minimum to prevent LOD culling all entities
        self.camera.set_zoom_limits(AUTO_FIT_MIN_ZOOM, 1000.0);
        self.settings.display.width = width;
        self.settings.display.height = height;
        self.fit_camera_to_content();
    }

    /// Captures a screenshot and returns it as PNG data.
    ///
    /// Only works with software renderer. WebGL2/wgpu renderers don't support
    /// direct pixel readback from JavaScript.
    ///
    /// # Returns
    /// PNG file data as a byte vector, or error message.
    #[wasm_bindgen(js_name = captureScreenshot)]
    pub fn capture_screenshot(&self) -> Result<Vec<u8>, JsValue> {
        if let Some(pixels) = self.backend.pixels() {
            let width = self.backend.width();
            let height = self.backend.height();

            let mut png_data = Vec::new();
            write_png(&mut png_data, pixels, width, height)
                .map_err(|e| JsValue::from_str(&format!("Failed to create PNG: {e}")))?;

            Ok(png_data)
        } else {
            Err(JsValue::from_str(
                "Screenshot not supported with WebGL2 renderer",
            ))
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // Padded Dimensions Tests
    // ========================================================================

    #[test]
    fn test_calculate_padded_dimensions_basic() {
        let (w, h) = calculate_padded_dimensions(100.0, 100.0, 0.2);
        assert!((w - 140.0).abs() < 0.001); // 100 * 1.4
        assert!((h - 140.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_padded_dimensions_zero_padding() {
        let (w, h) = calculate_padded_dimensions(100.0, 50.0, 0.0);
        assert!((w - 100.0).abs() < 0.001);
        assert!((h - 50.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_padded_dimensions_different_sizes() {
        let (w, h) = calculate_padded_dimensions(1000.0, 500.0, 0.1);
        assert!((w - 1200.0).abs() < 0.001); // 1000 * 1.2
        assert!((h - 600.0).abs() < 0.001); // 500 * 1.2
    }

    // ========================================================================
    // Readable Zoom Tests
    // ========================================================================

    #[test]
    fn test_calculate_readable_zoom_normal() {
        let zoom = calculate_readable_zoom(8.0, 16.0);
        assert!((zoom - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_calculate_readable_zoom_larger_label() {
        let zoom = calculate_readable_zoom(16.0, 16.0);
        assert!((zoom - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_readable_zoom_minimum_clamp() {
        // Even with tiny label request, minimum is 0.5
        let zoom = calculate_readable_zoom(1.0, 16.0);
        assert!((zoom - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_calculate_readable_zoom_large_label() {
        let zoom = calculate_readable_zoom(32.0, 16.0);
        assert!((zoom - 2.0).abs() < 0.001);
    }

    // ========================================================================
    // Canvas Dimensions Tests
    // ========================================================================

    #[test]
    fn test_calculate_canvas_dimensions_identity() {
        let (w, h) = calculate_canvas_dimensions(100.0, 50.0, 1.0);
        assert_eq!(w, 100);
        assert_eq!(h, 50);
    }

    #[test]
    fn test_calculate_canvas_dimensions_zoomed() {
        let (w, h) = calculate_canvas_dimensions(100.0, 50.0, 2.0);
        assert_eq!(w, 200);
        assert_eq!(h, 100);
    }

    #[test]
    fn test_calculate_canvas_dimensions_fractional() {
        let (w, h) = calculate_canvas_dimensions(100.0, 50.0, 1.5);
        assert_eq!(w, 150);
        assert_eq!(h, 75);
    }

    #[test]
    fn test_calculate_canvas_dimensions_rounding() {
        // Ceil rounding
        let (w, h) = calculate_canvas_dimensions(100.1, 50.1, 1.0);
        assert_eq!(w, 101);
        assert_eq!(h, 51);
    }

    // ========================================================================
    // Scale to Max Dimension Tests
    // ========================================================================

    #[test]
    fn test_scale_to_max_dimension_no_scaling_needed() {
        let (w, h, z) = scale_to_max_dimension(1920, 1080, 1.0, 16384);
        assert_eq!(w, 1920);
        assert_eq!(h, 1080);
        assert!((z - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_scale_to_max_dimension_width_exceeds() {
        let (w, h, z) = scale_to_max_dimension(20000, 10000, 1.0, 16384);
        assert!(w <= 16384);
        assert!(h <= 16384);
        assert!(z < 1.0);
    }

    #[test]
    fn test_scale_to_max_dimension_height_exceeds() {
        let (w, h, z) = scale_to_max_dimension(10000, 20000, 1.0, 16384);
        assert!(w <= 16384);
        assert!(h <= 16384);
        assert!(z < 1.0);
    }

    #[test]
    fn test_scale_to_max_dimension_both_exceed() {
        let (w, h, z) = scale_to_max_dimension(32768, 32768, 1.0, 16384);
        assert!(w <= 16384);
        assert!(h <= 16384);
        // Scale should be approximately 0.5
        assert!(z < 1.0);
    }

    #[test]
    fn test_scale_to_max_dimension_preserves_aspect_ratio() {
        let (w, h, _) = scale_to_max_dimension(20000, 10000, 1.0, 16384);
        let original_ratio = 20000.0 / 10000.0;
        let scaled_ratio = w as f32 / h as f32;
        assert!((original_ratio - scaled_ratio).abs() < 0.1);
    }

    // ========================================================================
    // Bounds JSON Formatting Tests
    // ========================================================================

    #[test]
    fn test_format_bounds_json_basic() {
        let json = format_bounds_json(0.0, 0.0, 100.0, 50.0);
        assert!(json.contains(r#""minX":0"#));
        assert!(json.contains(r#""minY":0"#));
        assert!(json.contains(r#""maxX":100"#));
        assert!(json.contains(r#""maxY":50"#));
        assert!(json.contains(r#""width":100"#));
        assert!(json.contains(r#""height":50"#));
    }

    #[test]
    fn test_format_bounds_json_negative() {
        let json = format_bounds_json(-50.0, -25.0, 50.0, 25.0);
        assert!(json.contains(r#""minX":-50"#));
        assert!(json.contains(r#""width":100"#));
        assert!(json.contains(r#""height":50"#));
    }

    // ========================================================================
    // Dimensions JSON Formatting Tests
    // ========================================================================

    #[test]
    fn test_format_dimensions_json_basic() {
        let json = format_dimensions_json(1920, 1080, 1.0, 0.0, 0.0);
        assert!(json.contains(r#""width":1920"#));
        assert!(json.contains(r#""height":1080"#));
        assert!(json.contains(r#""zoom":1"#));
        assert!(json.contains(r#""centerX":0"#));
        assert!(json.contains(r#""centerY":0"#));
    }

    #[test]
    fn test_format_dimensions_json_fractional() {
        let json = format_dimensions_json(4096, 2048, 0.75, 100.5, -50.25);
        assert!(json.contains(r#""width":4096"#));
        assert!(json.contains(r#""zoom":0.75"#));
        assert!(json.contains(r#""centerX":100.5"#));
        assert!(json.contains(r#""centerY":-50.25"#));
    }

    #[test]
    fn test_format_dimensions_json_is_valid_json() {
        let json = format_dimensions_json(1920, 1080, 1.0, 0.0, 0.0);
        assert!(json.starts_with('{'));
        assert!(json.ends_with('}'));
    }
}
