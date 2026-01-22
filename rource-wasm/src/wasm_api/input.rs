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
// Input Handling
// ============================================================================

#[wasm_bindgen]
impl Rource {
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
            "l" | "L" => self.show_labels = !self.show_labels,
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
