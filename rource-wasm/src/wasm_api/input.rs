// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Input handling for mouse and keyboard events.
//!
//! This module contains all user interaction event handlers including:
//! - Mouse down/up/move for entity dragging and camera panning
//! - Mouse wheel for zooming
//! - Keyboard shortcuts for playback and navigation

use wasm_bindgen::prelude::*;

use rource_math::Vec2;

use crate::interaction::{
    hit_test_directory, hit_test_file, hit_test_user, move_connected_entities_for_directory,
    move_connected_entities_for_file, move_connected_entities_for_user, DragTarget,
    ENTITY_HIT_RADIUS,
};
use crate::Rource;

// ============================================================================
// Helper Functions (testable without Rource instance)
// ============================================================================

#[allow(dead_code)]
#[allow(clippy::wildcard_imports)]
mod helpers {
    use super::*;

    /// Normalizes mouse wheel delta to a consistent range.
    ///
    /// Different browsers report different delta values. This normalizes
    /// by dividing by 100 and clamping to [-2, 2].
    ///
    /// # Arguments
    /// * `delta_y` - Raw `delta_y` from wheel event
    ///
    /// # Returns
    /// Normalized delta in range [-2, 2].
    #[inline]
    #[must_use]
    pub fn normalize_wheel_delta(delta_y: f32) -> f32 {
        (delta_y / 100.0).clamp(-2.0, 2.0)
    }

    /// Calculates the zoom factor from normalized wheel delta.
    ///
    /// # Arguments
    /// * `normalized_delta` - Normalized delta from `normalize_wheel_delta`
    ///
    /// # Returns
    /// Zoom factor (> 1 for zoom in, < 1 for zoom out).
    #[inline]
    #[must_use]
    pub fn calculate_wheel_zoom_factor(normalized_delta: f32) -> f32 {
        1.0 - (normalized_delta * 0.08)
    }

    /// Calculates the hit test radius adjusted for current zoom level.
    ///
    /// # Arguments
    /// * `base_radius` - The base hit test radius in screen pixels
    /// * `zoom` - Current camera zoom level
    ///
    /// # Returns
    /// Hit radius in world coordinates.
    #[inline]
    #[must_use]
    pub fn calculate_hit_radius(base_radius: f32, zoom: f32) -> f32 {
        base_radius / zoom
    }

    /// Calculates world delta from screen delta.
    ///
    /// # Arguments
    /// * `screen_delta` - Delta in screen pixels
    /// * `zoom` - Current camera zoom level
    ///
    /// # Returns
    /// Delta in world coordinates.
    #[inline]
    #[must_use]
    pub fn screen_to_world_delta(screen_delta: Vec2, zoom: f32) -> Vec2 {
        screen_delta / zoom
    }

    /// Checks if a keyboard key is a recognized shortcut.
    ///
    /// # Arguments
    /// * `key` - The key string from the keyboard event
    ///
    /// # Returns
    /// `true` if the key is a recognized shortcut.
    #[must_use]
    pub fn is_recognized_shortcut(key: &str) -> bool {
        matches!(
            key,
            " " | "Space"
                | "+"
                | "="
                | "-"
                | "_"
                | "ArrowUp"
                | "ArrowDown"
                | "ArrowLeft"
                | "ArrowRight"
                | "r"
                | "R"
                | "l"
                | "L"
                | "["
                | "]"
                | ","
                | "<"
                | "."
                | ">"
                | "Home"
                | "End"
        )
    }
}

#[allow(unused_imports)]
pub use helpers::*;

// ============================================================================
// Input Handling
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Returns debug information about hit testing at the given coordinates.
    ///
    /// Use this to diagnose why drag might not be working:
    /// - Check if `screen_to_world` conversion is correct
    /// - Check if entities are in the spatial index
    /// - Check if entities are within hit radius
    #[wasm_bindgen(js_name = debugHitTest)]
    pub fn debug_hit_test(&self, x: f32, y: f32) -> String {
        let screen_pos = Vec2::new(x, y);
        let world_pos = self.camera.screen_to_world(screen_pos);
        let hit_radius = ENTITY_HIT_RADIUS / self.camera.zoom();

        // Query the spatial index
        let entities = self.scene.query_entities_circle(world_pos, hit_radius);

        // Count entities by type directly (avoid needless collect)
        let user_count = entities
            .iter()
            .filter(|e| matches!(e, rource_core::scene::EntityType::User(_)))
            .count();
        let file_count = entities
            .iter()
            .filter(|e| matches!(e, rource_core::scene::EntityType::File(_)))
            .count();
        let dir_count = entities
            .iter()
            .filter(|e| matches!(e, rource_core::scene::EntityType::Directory(_)))
            .count();

        format!(
            r#"{{"screenX":{},"screenY":{},"worldX":{:.2},"worldY":{:.2},"zoom":{:.4},"hitRadius":{:.2},"viewportWidth":{},"viewportHeight":{},"totalFiles":{},"totalUsers":{},"totalDirs":{},"spatialQueryCount":{},"usersInRadius":{},"filesInRadius":{},"dirsInRadius":{}}}"#,
            x,
            y,
            world_pos.x,
            world_pos.y,
            self.camera.zoom(),
            hit_radius,
            self.backend.width(),
            self.backend.height(),
            self.scene.file_count(),
            self.scene.user_count(),
            self.scene.directory_count(),
            entities.len(),
            user_count,
            file_count,
            dir_count,
        )
    }

    /// Handles mouse down events.
    ///
    /// Initiates entity dragging if an entity is clicked, otherwise starts
    /// camera panning mode.
    #[wasm_bindgen(js_name = onMouseDown)]
    pub fn on_mouse_down(&mut self, x: f32, y: f32) {
        self.mouse_down = true;
        self.drag_start_x = x;
        self.drag_start_y = y;
        self.mouse_x = x;
        self.mouse_y = y;
        self.wake_renderer();

        let screen_pos = Vec2::new(x, y);
        let world_pos = self.camera.screen_to_world(screen_pos);
        let hit_radius = ENTITY_HIT_RADIUS / self.camera.zoom();

        // Check users first (highest priority for selection)
        if let Some(drag_target) = hit_test_user(&self.scene, world_pos, hit_radius) {
            self.drag_target = Some(drag_target);
            if let DragTarget::User(user_id) = drag_target {
                if let Some(user) = self.scene.get_user(user_id) {
                    self.drag_offset = user.position() - world_pos;
                    self.drag_last_pos = user.position();
                }
            }
            return;
        }

        // Check files
        if let Some(drag_target) = hit_test_file(&self.scene, world_pos, hit_radius) {
            self.drag_target = Some(drag_target);
            if let DragTarget::File(file_id) = drag_target {
                if let Some(file) = self.scene.get_file_mut(file_id) {
                    self.drag_offset = file.position() - world_pos;
                    self.drag_last_pos = file.position();
                    file.set_pinned(true);
                }
            }
            return;
        }

        // Check directories
        if let Some(drag_target) = hit_test_directory(&self.scene, world_pos, hit_radius) {
            self.drag_target = Some(drag_target);
            if let DragTarget::Directory(dir_id) = drag_target {
                if let Some(dir) = self.scene.directories().get(dir_id) {
                    self.drag_offset = dir.position() - world_pos;
                    self.drag_last_pos = dir.position();
                }
            }
            return;
        }

        // No entity hit, set up for camera panning
        self.drag_target = None;
        self.camera_start_x = self.camera.position().x;
        self.camera_start_y = self.camera.position().y;
    }

    /// Handles mouse up events.
    ///
    /// Releases any dragged entity and resets drag state.
    #[wasm_bindgen(js_name = onMouseUp)]
    pub fn on_mouse_up(&mut self) {
        // Unpin file if it was being dragged
        if let Some(DragTarget::File(file_id)) = self.drag_target {
            if let Some(file) = self.scene.get_file_mut(file_id) {
                file.set_pinned(false);
            }
        }

        self.mouse_down = false;
        self.drag_target = None;
        self.drag_offset = Vec2::ZERO;
        self.drag_last_pos = Vec2::ZERO;
        self.wake_renderer();
    }

    /// Handles mouse move events.
    ///
    /// Updates entity position if dragging, or pans camera if no entity is selected.
    #[wasm_bindgen(js_name = onMouseMove)]
    pub fn on_mouse_move(&mut self, x: f32, y: f32) {
        self.mouse_x = x;
        self.mouse_y = y;

        if !self.mouse_down {
            return;
        }

        self.wake_renderer();

        let screen_pos = Vec2::new(x, y);
        let world_pos = self.camera.screen_to_world(screen_pos);

        if let Some(drag_target) = self.drag_target {
            let new_entity_pos = world_pos + self.drag_offset;
            let delta = new_entity_pos - self.drag_last_pos;

            match drag_target {
                DragTarget::User(user_id) => {
                    if let Some(user) = self.scene.get_user_mut(user_id) {
                        user.set_position(new_entity_pos);
                        user.clear_target();
                    }
                    move_connected_entities_for_user(&mut self.scene, user_id, delta);
                }
                DragTarget::File(file_id) => {
                    let dir_id = self
                        .scene
                        .get_file(file_id)
                        .map(rource_core::scene::FileNode::directory);

                    if let Some(file) = self.scene.get_file_mut(file_id) {
                        file.set_position(new_entity_pos);
                        file.set_target(new_entity_pos);
                    }

                    if let Some(dir_id) = dir_id {
                        move_connected_entities_for_file(&mut self.scene, file_id, dir_id, delta);
                    }
                }
                DragTarget::Directory(dir_id) => {
                    if let Some(dir) = self.scene.directories_mut().get_mut(dir_id) {
                        dir.set_position(new_entity_pos);
                        dir.set_velocity(Vec2::ZERO);
                    }
                    move_connected_entities_for_directory(&mut self.scene, dir_id, delta);
                }
            }

            self.drag_last_pos = new_entity_pos;
            self.scene.invalidate_bounds_cache();
        } else {
            // Camera panning
            let dx = x - self.drag_start_x;
            let dy = y - self.drag_start_y;
            let world_delta = Vec2::new(dx, dy) / self.camera.zoom();
            let new_pos = Vec2::new(self.camera_start_x, self.camera_start_y) - world_delta;
            self.camera.jump_to(new_pos);
        }
    }

    /// Handles mouse wheel events for zooming.
    ///
    /// Zooms toward the mouse cursor position for intuitive navigation.
    #[wasm_bindgen(js_name = onWheel)]
    pub fn on_wheel(&mut self, delta_y: f32, mouse_x: f32, mouse_y: f32) {
        let normalized_delta = delta_y / 100.0;
        let clamped_delta = normalized_delta.clamp(-2.0, 2.0);
        let factor = 1.0 - (clamped_delta * 0.08);
        self.zoom_toward(mouse_x, mouse_y, factor);
        // wake_renderer() called by zoom_toward()
    }

    /// Handles keyboard events.
    ///
    /// Supports the following shortcuts:
    /// - Space: Toggle play/pause
    /// - +/-: Zoom in/out
    /// - Arrows: Pan camera
    /// - R: Reset camera
    /// - L: Toggle labels
    /// - [/]: Decrease/increase speed
    /// - </> or ,/.: Step backward/forward
    /// - Home/End: Jump to start/end
    #[wasm_bindgen(js_name = onKeyDown)]
    pub fn on_key_down(&mut self, key: &str) {
        match key {
            " " | "Space" => self.toggle_play(),
            "+" | "=" => self.zoom(1.2),
            "-" | "_" => self.zoom(0.8),
            "ArrowUp" => self.pan(0.0, -50.0),
            "ArrowDown" => self.pan(0.0, 50.0),
            "ArrowLeft" => self.pan(-50.0, 0.0),
            "ArrowRight" => self.pan(50.0, 0.0),
            "r" | "R" => self.reset_camera(),
            "l" | "L" => {
                self.show_labels = !self.show_labels;
                self.wake_renderer();
            }
            "[" => self.set_speed(self.settings.playback.seconds_per_day * 0.5),
            "]" => self.set_speed(self.settings.playback.seconds_per_day * 2.0),
            "," | "<" => self.step_backward(),
            "." | ">" => self.step_forward(),
            "Home" => self.seek(0),
            "End" => {
                if !self.commits.is_empty() {
                    let last = self.commits.len().saturating_sub(1);
                    self.seek(last);
                }
            }
            _ => {}
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
    // Wheel Delta Normalization Tests
    // ========================================================================

    #[test]
    fn test_normalize_wheel_delta_small_positive() {
        let delta = normalize_wheel_delta(100.0);
        assert!((delta - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_normalize_wheel_delta_small_negative() {
        let delta = normalize_wheel_delta(-100.0);
        assert!((delta - (-1.0)).abs() < 0.001);
    }

    #[test]
    fn test_normalize_wheel_delta_zero() {
        let delta = normalize_wheel_delta(0.0);
        assert!((delta - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_normalize_wheel_delta_clamp_max() {
        // Large positive values should clamp to 2.0
        let delta = normalize_wheel_delta(500.0);
        assert!((delta - 2.0).abs() < 0.001);
    }

    #[test]
    fn test_normalize_wheel_delta_clamp_min() {
        // Large negative values should clamp to -2.0
        let delta = normalize_wheel_delta(-500.0);
        assert!((delta - (-2.0)).abs() < 0.001);
    }

    #[test]
    fn test_normalize_wheel_delta_fractional() {
        let delta = normalize_wheel_delta(50.0);
        assert!((delta - 0.5).abs() < 0.001);
    }

    // ========================================================================
    // Zoom Factor Calculation Tests
    // ========================================================================

    #[test]
    fn test_calculate_wheel_zoom_factor_zero_delta() {
        // Zero delta should result in no zoom (factor = 1.0)
        let factor = calculate_wheel_zoom_factor(0.0);
        assert!((factor - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_wheel_zoom_factor_positive_delta() {
        // Positive delta (scroll down) should zoom out (factor < 1.0)
        let factor = calculate_wheel_zoom_factor(1.0);
        assert!((factor - 0.92).abs() < 0.001);
    }

    #[test]
    fn test_calculate_wheel_zoom_factor_negative_delta() {
        // Negative delta (scroll up) should zoom in (factor > 1.0)
        let factor = calculate_wheel_zoom_factor(-1.0);
        assert!((factor - 1.08).abs() < 0.001);
    }

    #[test]
    fn test_calculate_wheel_zoom_factor_max_delta() {
        let factor = calculate_wheel_zoom_factor(2.0);
        assert!((factor - 0.84).abs() < 0.001);
    }

    #[test]
    fn test_calculate_wheel_zoom_factor_min_delta() {
        let factor = calculate_wheel_zoom_factor(-2.0);
        assert!((factor - 1.16).abs() < 0.001);
    }

    // ========================================================================
    // Hit Radius Calculation Tests
    // ========================================================================

    #[test]
    fn test_calculate_hit_radius_zoom_1() {
        let radius = calculate_hit_radius(10.0, 1.0);
        assert!((radius - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_hit_radius_zoom_2() {
        // At 2x zoom, hit radius should be halved in world units
        let radius = calculate_hit_radius(10.0, 2.0);
        assert!((radius - 5.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_hit_radius_zoom_half() {
        // At 0.5x zoom, hit radius should be doubled in world units
        let radius = calculate_hit_radius(10.0, 0.5);
        assert!((radius - 20.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_hit_radius_small_zoom() {
        // At very low zoom, hit radius should be large
        let radius = calculate_hit_radius(10.0, 0.1);
        assert!((radius - 100.0).abs() < 0.001);
    }

    // ========================================================================
    // Screen to World Delta Tests
    // ========================================================================

    #[test]
    fn test_screen_to_world_delta_zoom_1() {
        let delta = screen_to_world_delta(Vec2::new(100.0, 50.0), 1.0);
        assert!((delta.x - 100.0).abs() < 0.001);
        assert!((delta.y - 50.0).abs() < 0.001);
    }

    #[test]
    fn test_screen_to_world_delta_zoom_2() {
        // At 2x zoom, screen delta is halved in world units
        let delta = screen_to_world_delta(Vec2::new(100.0, 50.0), 2.0);
        assert!((delta.x - 50.0).abs() < 0.001);
        assert!((delta.y - 25.0).abs() < 0.001);
    }

    #[test]
    fn test_screen_to_world_delta_zoom_half() {
        // At 0.5x zoom, screen delta is doubled in world units
        let delta = screen_to_world_delta(Vec2::new(100.0, 50.0), 0.5);
        assert!((delta.x - 200.0).abs() < 0.001);
        assert!((delta.y - 100.0).abs() < 0.001);
    }

    #[test]
    fn test_screen_to_world_delta_zero() {
        let delta = screen_to_world_delta(Vec2::ZERO, 1.0);
        assert!((delta.x - 0.0).abs() < 0.001);
        assert!((delta.y - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_screen_to_world_delta_negative() {
        let delta = screen_to_world_delta(Vec2::new(-50.0, -25.0), 1.0);
        assert!((delta.x - (-50.0)).abs() < 0.001);
        assert!((delta.y - (-25.0)).abs() < 0.001);
    }

    // ========================================================================
    // Keyboard Shortcut Recognition Tests
    // ========================================================================

    #[test]
    fn test_is_recognized_shortcut_space() {
        assert!(is_recognized_shortcut(" "));
        assert!(is_recognized_shortcut("Space"));
    }

    #[test]
    fn test_is_recognized_shortcut_zoom() {
        assert!(is_recognized_shortcut("+"));
        assert!(is_recognized_shortcut("="));
        assert!(is_recognized_shortcut("-"));
        assert!(is_recognized_shortcut("_"));
    }

    #[test]
    fn test_is_recognized_shortcut_arrows() {
        assert!(is_recognized_shortcut("ArrowUp"));
        assert!(is_recognized_shortcut("ArrowDown"));
        assert!(is_recognized_shortcut("ArrowLeft"));
        assert!(is_recognized_shortcut("ArrowRight"));
    }

    #[test]
    fn test_is_recognized_shortcut_reset_labels() {
        assert!(is_recognized_shortcut("r"));
        assert!(is_recognized_shortcut("R"));
        assert!(is_recognized_shortcut("l"));
        assert!(is_recognized_shortcut("L"));
    }

    #[test]
    fn test_is_recognized_shortcut_speed() {
        assert!(is_recognized_shortcut("["));
        assert!(is_recognized_shortcut("]"));
    }

    #[test]
    fn test_is_recognized_shortcut_step() {
        assert!(is_recognized_shortcut(","));
        assert!(is_recognized_shortcut("<"));
        assert!(is_recognized_shortcut("."));
        assert!(is_recognized_shortcut(">"));
    }

    #[test]
    fn test_is_recognized_shortcut_navigation() {
        assert!(is_recognized_shortcut("Home"));
        assert!(is_recognized_shortcut("End"));
    }

    #[test]
    fn test_is_recognized_shortcut_unrecognized() {
        assert!(!is_recognized_shortcut("a"));
        assert!(!is_recognized_shortcut("Enter"));
        assert!(!is_recognized_shortcut("Escape"));
        assert!(!is_recognized_shortcut("Tab"));
        assert!(!is_recognized_shortcut("F1"));
        assert!(!is_recognized_shortcut(""));
    }
}
