//! Camera control for view manipulation.
//!
//! This module provides methods to control the visualization viewport:
//! - Zoom in/out (with optional focal point)
//! - Pan/scroll
//! - Canvas resize
//! - Camera state serialization/restoration

use wasm_bindgen::prelude::*;

use rource_core::camera::Camera;
use rource_math::Vec2;

use crate::render_phases::AUTO_FIT_MIN_ZOOM;
use crate::Rource;

// ============================================================================
// Camera Control
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Zooms the camera by a factor (> 1 zooms in, < 1 zooms out).
    ///
    /// Max zoom is 1000.0 to support deep zoom into massive repositories.
    /// Min zoom is `AUTO_FIT_MIN_ZOOM` (0.03) to prevent LOD culling all entities.
    /// Disables auto-fit when user manually zooms.
    pub fn zoom(&mut self, factor: f32) {
        self.auto_fit = false; // User is taking manual control
        let new_zoom = (self.camera.zoom() * factor).clamp(AUTO_FIT_MIN_ZOOM, 1000.0);
        self.camera.set_zoom(new_zoom);
    }

    /// Zooms the camera toward a specific screen point.
    ///
    /// This provides intuitive zoom behavior where the point under the cursor
    /// stays fixed during zoom operations.
    /// Min zoom is `AUTO_FIT_MIN_ZOOM` (0.03) to prevent LOD culling all entities.
    /// Disables auto-fit when user manually zooms.
    #[wasm_bindgen(js_name = zoomToward)]
    pub fn zoom_toward(&mut self, screen_x: f32, screen_y: f32, factor: f32) {
        self.auto_fit = false; // User is taking manual control
        let screen_point = Vec2::new(screen_x, screen_y);
        let world_before = self.camera.screen_to_world(screen_point);

        // Use AUTO_FIT_MIN_ZOOM (0.03) as minimum to prevent LOD culling all entities
        let new_zoom = (self.camera.zoom() * factor).clamp(AUTO_FIT_MIN_ZOOM, 1000.0);
        self.camera.set_zoom(new_zoom);

        let world_after = self.camera.screen_to_world(screen_point);
        let diff = world_before - world_after;
        let new_pos = self.camera.position() + diff;
        self.camera.jump_to(new_pos);
    }

    /// Pans the camera by the given delta in screen pixels.
    /// Disables auto-fit when user manually pans.
    pub fn pan(&mut self, dx: f32, dy: f32) {
        self.auto_fit = false; // User is taking manual control
        let world_delta = Vec2::new(dx, dy) / self.camera.zoom();
        let new_pos = self.camera.position() - world_delta;
        self.camera.jump_to(new_pos);
    }

    /// Resets the camera to fit all content.
    #[wasm_bindgen(js_name = resetCamera)]
    pub fn reset_camera(&mut self) {
        self.fit_camera_to_content();
    }

    /// Resizes the canvas and renderer.
    ///
    /// Should be called when the canvas element size changes.
    pub fn resize(&mut self, width: u32, height: u32) {
        self.canvas.set_width(width);
        self.canvas.set_height(height);
        self.backend.resize(width, height);
        self.camera = Camera::new(width as f32, height as f32);
        // Use AUTO_FIT_MIN_ZOOM (0.03) as minimum to prevent LOD culling all entities
        self.camera.set_zoom_limits(AUTO_FIT_MIN_ZOOM, 1000.0);
        self.settings.display.width = width;
        self.settings.display.height = height;
    }

    /// Returns the current zoom level.
    #[wasm_bindgen(js_name = getZoom)]
    pub fn get_zoom(&self) -> f32 {
        self.camera.zoom()
    }

    /// Returns the canvas width in pixels.
    #[wasm_bindgen(js_name = getCanvasWidth)]
    pub fn get_canvas_width(&self) -> u32 {
        self.backend.width()
    }

    /// Returns the canvas height in pixels.
    #[wasm_bindgen(js_name = getCanvasHeight)]
    pub fn get_canvas_height(&self) -> u32 {
        self.backend.height()
    }

    /// Returns the current camera state as JSON.
    ///
    /// Returns `{"x": <f32>, "y": <f32>, "zoom": <f32>}`
    #[wasm_bindgen(js_name = getCameraState)]
    pub fn get_camera_state(&self) -> String {
        format!(
            r#"{{"x":{},"y":{},"zoom":{}}}"#,
            self.camera.position().x,
            self.camera.position().y,
            self.camera.zoom()
        )
    }

    /// Restores camera state from previously saved values.
    ///
    /// Use with `getCameraState()` to save/restore view positions.
    #[wasm_bindgen(js_name = restoreCameraState)]
    pub fn restore_camera_state(&mut self, x: f32, y: f32, zoom: f32) {
        self.camera.jump_to(Vec2::new(x, y));
        self.camera.set_zoom(zoom);
    }

    /// Enables or disables auto-fit mode.
    ///
    /// When enabled, the camera automatically zooms out to keep all content visible
    /// as the visualization grows. Manual zoom/pan operations disable auto-fit.
    ///
    /// Auto-fit is disabled by default due to coordination issues with LOD culling
    /// and spatial indexing. Use `resetCamera()` for one-time camera fitting instead.
    #[wasm_bindgen(js_name = setAutoFit)]
    pub fn set_auto_fit(&mut self, enabled: bool) {
        self.auto_fit = enabled;
    }

    /// Returns whether auto-fit mode is currently enabled.
    #[wasm_bindgen(js_name = isAutoFit)]
    pub fn is_auto_fit(&self) -> bool {
        self.auto_fit
    }
}
