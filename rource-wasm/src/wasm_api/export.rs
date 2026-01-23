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
