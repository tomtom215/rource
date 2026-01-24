// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Camera system for the visualization.
//!
//! This module provides camera control including:
//!
//! - Pan and zoom (2D orthographic)
//! - Orbit controls (3D perspective)
//! - Auto-tracking of entities
//! - Smooth camera transitions
//! - View frustum calculations
//!
//! # Example (2D Camera)
//!
//! ```
//! use rource_core::camera::{Camera, CameraMode};
//! use rource_math::Vec2;
//!
//! let mut camera = Camera::new(1920.0, 1080.0);
//!
//! // Set manual position
//! camera.set_mode(CameraMode::Manual);
//! camera.set_target_position(Vec2::new(100.0, 50.0));
//!
//! // Update each frame
//! camera.update(0.016);
//! ```
//!
//! # Example (3D Camera)
//!
//! ```
//! use rource_core::camera::Camera3D;
//! use rource_math::Vec3;
//!
//! let mut camera = Camera3D::new(1920.0, 1080.0);
//!
//! // Orbit around the target
//! camera.orbit(0.1, 0.05); // yaw, pitch
//!
//! // Update each frame
//! camera.update(0.016);
//! ```

mod camera3d;

pub use camera3d::Camera3D;

use rource_math::{Bounds, Vec2};

use crate::animation::{Easing, Tween};

// ============================================================================
// Helper Functions (testable without Camera instance)
// ============================================================================

#[allow(dead_code)]
mod helpers {
    /// Calculates the lerp factor for smooth camera interpolation.
    ///
    /// The formula `1.0 - smoothness.powf(dt * 60.0)` produces a frame-rate
    /// independent lerp factor that converges toward the target.
    ///
    /// # Arguments
    /// * `smoothness` - Smoothness value (0.0 = instant, higher = slower)
    /// * `dt` - Delta time in seconds
    ///
    /// # Returns
    /// Lerp factor between 0.0 and 1.0.
    #[inline]
    #[must_use]
    pub fn calculate_lerp_factor(smoothness: f32, dt: f32) -> f32 {
        1.0 - smoothness.powf(dt * 60.0)
    }

    /// Calculates the zoom level needed to fit content within a viewport.
    ///
    /// # Arguments
    /// * `viewport_width` - Viewport width in pixels
    /// * `viewport_height` - Viewport height in pixels
    /// * `content_width` - Content width in world units
    /// * `content_height` - Content height in world units
    /// * `padding` - Padding to add around content
    ///
    /// # Returns
    /// Zoom level that fits content (uses smaller of width/height fit).
    #[inline]
    #[must_use]
    pub fn calculate_fit_zoom(
        viewport_width: f32,
        viewport_height: f32,
        content_width: f32,
        content_height: f32,
        padding: f32,
    ) -> f32 {
        let zoom_x = viewport_width / (content_width + padding * 2.0);
        let zoom_y = viewport_height / (content_height + padding * 2.0);
        zoom_x.min(zoom_y)
    }

    /// Clamps a zoom value to the valid range.
    ///
    /// # Arguments
    /// * `zoom` - Zoom value to clamp
    /// * `min_zoom` - Minimum allowed zoom
    /// * `max_zoom` - Maximum allowed zoom
    ///
    /// # Returns
    /// Clamped zoom value.
    #[inline]
    #[must_use]
    pub fn clamp_zoom(zoom: f32, min_zoom: f32, max_zoom: f32) -> f32 {
        zoom.clamp(min_zoom, max_zoom)
    }

    /// Calculates the half-size of the visible area in world units.
    ///
    /// # Arguments
    /// * `viewport_width` - Viewport width in pixels
    /// * `viewport_height` - Viewport height in pixels
    /// * `zoom` - Current zoom level
    ///
    /// # Returns
    /// Tuple of (`half_width`, `half_height`) in world units.
    #[inline]
    #[must_use]
    pub fn visible_half_size(viewport_width: f32, viewport_height: f32, zoom: f32) -> (f32, f32) {
        (
            viewport_width / (2.0 * zoom),
            viewport_height / (2.0 * zoom),
        )
    }

    /// Checks if a position has effectively reached its target.
    ///
    /// # Arguments
    /// * `current` - Current position
    /// * `target` - Target position
    /// * `threshold` - Distance threshold (default: 0.01)
    ///
    /// # Returns
    /// `true` if the positions are within threshold distance.
    #[inline]
    #[must_use]
    pub fn has_reached_target_position(
        current_x: f32,
        current_y: f32,
        target_x: f32,
        target_y: f32,
        threshold: f32,
    ) -> bool {
        let dx = target_x - current_x;
        let dy = target_y - current_y;
        dx.hypot(dy) <= threshold
    }

    /// Checks if a zoom value has effectively reached its target.
    ///
    /// # Arguments
    /// * `current` - Current zoom
    /// * `target` - Target zoom
    /// * `threshold` - Difference threshold (default: 0.001)
    ///
    /// # Returns
    /// `true` if the zoom values are within threshold.
    #[inline]
    #[must_use]
    pub fn has_reached_target_zoom(current: f32, target: f32, threshold: f32) -> bool {
        (target - current).abs() <= threshold
    }

    /// Calculates the new zoom level after zooming in by a factor.
    ///
    /// # Arguments
    /// * `current_zoom` - Current zoom level
    /// * `factor` - Zoom factor (positive = zoom in)
    /// * `zoom_speed` - Speed multiplier
    ///
    /// # Returns
    /// New zoom level (not clamped).
    #[inline]
    #[must_use]
    pub fn calculate_zoom_in(current_zoom: f32, factor: f32, zoom_speed: f32) -> f32 {
        current_zoom * (1.0 + factor * zoom_speed)
    }

    /// Calculates the new zoom level after zooming out by a factor.
    ///
    /// # Arguments
    /// * `current_zoom` - Current zoom level
    /// * `factor` - Zoom factor (positive = zoom out)
    /// * `zoom_speed` - Speed multiplier
    ///
    /// # Returns
    /// New zoom level (not clamped).
    #[inline]
    #[must_use]
    pub fn calculate_zoom_out(current_zoom: f32, factor: f32, zoom_speed: f32) -> f32 {
        current_zoom / (1.0 + factor * zoom_speed)
    }

    /// Converts screen coordinates to world coordinates.
    ///
    /// # Arguments
    /// * `screen_x` - Screen X coordinate
    /// * `screen_y` - Screen Y coordinate
    /// * `camera_x` - Camera position X
    /// * `camera_y` - Camera position Y
    /// * `viewport_width` - Viewport width
    /// * `viewport_height` - Viewport height
    /// * `zoom` - Camera zoom level
    ///
    /// # Returns
    /// Tuple of (`world_x`, `world_y`).
    #[inline]
    #[must_use]
    pub fn screen_to_world_coords(
        screen_x: f32,
        screen_y: f32,
        camera_x: f32,
        camera_y: f32,
        viewport_width: f32,
        viewport_height: f32,
        zoom: f32,
    ) -> (f32, f32) {
        let centered_x = screen_x - viewport_width * 0.5;
        let centered_y = screen_y - viewport_height * 0.5;
        let world_x = camera_x + centered_x / zoom;
        let world_y = camera_y + centered_y / zoom;
        (world_x, world_y)
    }

    /// Converts world coordinates to screen coordinates.
    ///
    /// # Arguments
    /// * `world_x` - World X coordinate
    /// * `world_y` - World Y coordinate
    /// * `camera_x` - Camera position X
    /// * `camera_y` - Camera position Y
    /// * `viewport_width` - Viewport width
    /// * `viewport_height` - Viewport height
    /// * `zoom` - Camera zoom level
    ///
    /// # Returns
    /// Tuple of (`screen_x`, `screen_y`).
    #[inline]
    #[must_use]
    pub fn world_to_screen_coords(
        world_x: f32,
        world_y: f32,
        camera_x: f32,
        camera_y: f32,
        viewport_width: f32,
        viewport_height: f32,
        zoom: f32,
    ) -> (f32, f32) {
        let offset_x = world_x - camera_x;
        let offset_y = world_y - camera_y;
        let screen_x = offset_x * zoom + viewport_width * 0.5;
        let screen_y = offset_y * zoom + viewport_height * 0.5;
        (screen_x, screen_y)
    }

    /// Calculates the optimal zoom for a tracker to fit all positions.
    ///
    /// # Arguments
    /// * `bounds_width` - Width of bounds containing positions
    /// * `bounds_height` - Height of bounds containing positions
    /// * `viewport_width` - Viewport width
    /// * `viewport_height` - Viewport height
    ///
    /// # Returns
    /// Optimal zoom level.
    #[inline]
    #[must_use]
    pub fn calculate_tracker_zoom(
        bounds_width: f32,
        bounds_height: f32,
        viewport_width: f32,
        viewport_height: f32,
    ) -> f32 {
        let zoom_x = viewport_width / bounds_width;
        let zoom_y = viewport_height / bounds_height;
        zoom_x.min(zoom_y)
    }

    /// Validates smoothness value and clamps to valid range.
    ///
    /// # Arguments
    /// * `smoothness` - Input smoothness value
    ///
    /// # Returns
    /// Clamped smoothness value between 0.0 and 0.99.
    #[inline]
    #[must_use]
    pub fn clamp_smoothness(smoothness: f32) -> f32 {
        smoothness.clamp(0.0, 0.99)
    }

    /// Calculates interpolation progress for transition.
    ///
    /// # Arguments
    /// * `t` - Progress value (0.0 to 1.0)
    /// * `start` - Start value
    /// * `end` - End value
    ///
    /// # Returns
    /// Interpolated value.
    #[inline]
    #[must_use]
    pub fn lerp(t: f32, start: f32, end: f32) -> f32 {
        start + (end - start) * t
    }
}

/// Default camera zoom level.
pub const DEFAULT_ZOOM: f32 = 1.0;

/// Minimum zoom level (zoomed out).
///
/// Set to 0.05 to ensure entities remain visible above LOD thresholds:
/// - Files: `world_radius`=5.0, LOD=0.1 → `min_zoom` = 0.1/5.0 = 0.02
/// - Users: `world_radius`=15.0, LOD=0.3 → `min_zoom` = 0.3/15.0 = 0.02
///
/// Using 0.05 provides a comfortable margin (150% above threshold at minimum zoom).
/// At 0.05: file `screen_radius` = 5.0 * 0.05 = 0.25 > 0.1 threshold
pub const MIN_ZOOM: f32 = 0.05;

/// Maximum zoom level (zoomed in).
pub const MAX_ZOOM: f32 = 10.0;

/// Default camera smoothness (0 = instant, 1 = very slow).
pub const DEFAULT_SMOOTHNESS: f32 = 0.85;

/// Default zoom speed multiplier.
pub const DEFAULT_ZOOM_SPEED: f32 = 0.1;

/// The camera mode determines how the camera position is updated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CameraMode {
    /// Camera follows user input/manual control.
    #[default]
    Manual,

    /// Camera automatically tracks a target position.
    AutoTrack,

    /// Camera follows a spline path.
    Path,

    /// Camera is locked in place.
    Locked,
}

/// Camera state for the visualization.
///
/// The camera provides a 2D view into the scene with pan and zoom.
/// It supports smooth transitions and auto-tracking of entities.
#[derive(Debug, Clone)]
pub struct Camera {
    /// Current position (center of view).
    position: Vec2,

    /// Target position for smooth movement.
    target_position: Vec2,

    /// Current zoom level (1.0 = default, <1.0 = zoomed out, >1.0 = zoomed in).
    zoom: f32,

    /// Target zoom level.
    target_zoom: f32,

    /// Viewport width in pixels.
    viewport_width: f32,

    /// Viewport height in pixels.
    viewport_height: f32,

    /// Camera mode.
    mode: CameraMode,

    /// Smoothness factor (0.0 = instant, 1.0 = very slow).
    smoothness: f32,

    /// Minimum zoom level.
    min_zoom: f32,

    /// Maximum zoom level.
    max_zoom: f32,

    /// Zoom speed multiplier.
    zoom_speed: f32,

    /// Optional bounds to constrain the camera.
    bounds: Option<Bounds>,

    /// Whether the camera needs to update its view matrix.
    dirty: bool,

    /// Transition tween for smooth movements.
    transition: Option<CameraTransition>,
}

/// A camera transition for smooth movements.
#[derive(Debug, Clone)]
struct CameraTransition {
    start_position: Vec2,
    end_position: Vec2,
    start_zoom: f32,
    end_zoom: f32,
    tween: Tween,
}

impl Default for Camera {
    fn default() -> Self {
        Self::new(1920.0, 1080.0)
    }
}

impl Camera {
    /// Creates a new camera with the given viewport size.
    #[must_use]
    pub fn new(viewport_width: f32, viewport_height: f32) -> Self {
        Self {
            position: Vec2::ZERO,
            target_position: Vec2::ZERO,
            zoom: DEFAULT_ZOOM,
            target_zoom: DEFAULT_ZOOM,
            viewport_width,
            viewport_height,
            mode: CameraMode::default(),
            smoothness: DEFAULT_SMOOTHNESS,
            min_zoom: MIN_ZOOM,
            max_zoom: MAX_ZOOM,
            zoom_speed: DEFAULT_ZOOM_SPEED,
            bounds: None,
            dirty: true,
            transition: None,
        }
    }

    /// Creates a camera centered on the given position.
    #[must_use]
    pub fn centered_on(position: Vec2, viewport_width: f32, viewport_height: f32) -> Self {
        Self {
            position,
            target_position: position,
            ..Self::new(viewport_width, viewport_height)
        }
    }

    /// Returns the current position.
    #[inline]
    #[must_use]
    pub const fn position(&self) -> Vec2 {
        self.position
    }

    /// Returns the target position.
    #[inline]
    #[must_use]
    pub const fn target_position(&self) -> Vec2 {
        self.target_position
    }

    /// Sets the target position for smooth movement.
    pub fn set_target_position(&mut self, position: Vec2) {
        self.target_position = position;
        self.dirty = true;
    }

    /// Jumps immediately to the given position.
    pub fn jump_to(&mut self, position: Vec2) {
        self.position = position;
        self.target_position = position;
        self.transition = None;
        self.dirty = true;
    }

    /// Returns the current zoom level.
    #[inline]
    #[must_use]
    pub const fn zoom(&self) -> f32 {
        self.zoom
    }

    /// Returns the target zoom level.
    #[inline]
    #[must_use]
    pub const fn target_zoom(&self) -> f32 {
        self.target_zoom
    }

    /// Sets the target zoom level.
    pub fn set_target_zoom(&mut self, zoom: f32) {
        self.target_zoom = zoom.clamp(self.min_zoom, self.max_zoom);
        self.dirty = true;
    }

    /// Jumps immediately to the given zoom level.
    pub fn set_zoom(&mut self, zoom: f32) {
        self.zoom = zoom.clamp(self.min_zoom, self.max_zoom);
        self.target_zoom = self.zoom;
        self.transition = None;
        self.dirty = true;
    }

    /// Zooms in by a factor.
    pub fn zoom_in(&mut self, factor: f32) {
        let new_zoom = self.target_zoom * (1.0 + factor * self.zoom_speed);
        self.set_target_zoom(new_zoom);
    }

    /// Zooms out by a factor.
    pub fn zoom_out(&mut self, factor: f32) {
        let new_zoom = self.target_zoom / (1.0 + factor * self.zoom_speed);
        self.set_target_zoom(new_zoom);
    }

    /// Zooms toward a specific point.
    ///
    /// This adjusts the camera position so the point stays in the same
    /// screen position after zooming.
    pub fn zoom_toward(&mut self, screen_point: Vec2, factor: f32) {
        let world_before = self.screen_to_world(screen_point);

        if factor > 0.0 {
            self.zoom_in(factor);
        } else {
            self.zoom_out(-factor);
        }

        // Adjust position so world_before stays at the same screen position
        let world_after = self.screen_to_world(screen_point);
        let diff = world_before - world_after;
        self.target_position += diff;
    }

    /// Returns the viewport size.
    #[inline]
    #[must_use]
    pub const fn viewport_size(&self) -> (f32, f32) {
        (self.viewport_width, self.viewport_height)
    }

    /// Sets the viewport size.
    pub fn set_viewport_size(&mut self, width: f32, height: f32) {
        self.viewport_width = width;
        self.viewport_height = height;
        self.dirty = true;
    }

    /// Returns the camera mode.
    #[inline]
    #[must_use]
    pub const fn mode(&self) -> CameraMode {
        self.mode
    }

    /// Sets the camera mode.
    pub fn set_mode(&mut self, mode: CameraMode) {
        self.mode = mode;
    }

    /// Returns the smoothness factor.
    #[inline]
    #[must_use]
    pub const fn smoothness(&self) -> f32 {
        self.smoothness
    }

    /// Sets the smoothness factor (0.0 = instant, 1.0 = very slow).
    pub fn set_smoothness(&mut self, smoothness: f32) {
        self.smoothness = smoothness.clamp(0.0, 0.99);
    }

    /// Sets the zoom limits.
    pub fn set_zoom_limits(&mut self, min: f32, max: f32) {
        self.min_zoom = min.max(0.001);
        self.max_zoom = max.max(min);
    }

    /// Sets the optional camera bounds.
    pub fn set_bounds(&mut self, bounds: Option<Bounds>) {
        self.bounds = bounds;
    }

    /// Returns the visible world bounds.
    #[must_use]
    pub fn visible_bounds(&self) -> Bounds {
        let half_width = self.viewport_width / (2.0 * self.zoom);
        let half_height = self.viewport_height / (2.0 * self.zoom);

        Bounds::new(
            self.position - Vec2::new(half_width, half_height),
            self.position + Vec2::new(half_width, half_height),
        )
    }

    /// Converts a screen position to world coordinates.
    #[must_use]
    pub fn screen_to_world(&self, screen_pos: Vec2) -> Vec2 {
        let centered =
            screen_pos - Vec2::new(self.viewport_width * 0.5, self.viewport_height * 0.5);
        let scaled = centered / self.zoom;
        self.position + scaled
    }

    /// Converts a world position to screen coordinates.
    #[must_use]
    pub fn world_to_screen(&self, world_pos: Vec2) -> Vec2 {
        let offset = world_pos - self.position;
        let scaled = offset * self.zoom;
        scaled + Vec2::new(self.viewport_width * 0.5, self.viewport_height * 0.5)
    }

    /// Returns true if the world position is visible.
    #[must_use]
    pub fn is_visible(&self, world_pos: Vec2) -> bool {
        self.visible_bounds().contains(world_pos)
    }

    /// Returns true if the world bounds intersect the visible area.
    #[must_use]
    pub fn is_bounds_visible(&self, bounds: &Bounds) -> bool {
        self.visible_bounds().intersects(*bounds)
    }

    /// Pans the camera by a screen offset.
    pub fn pan(&mut self, screen_delta: Vec2) {
        let world_delta = screen_delta / self.zoom;
        self.target_position -= world_delta;
        self.dirty = true;
    }

    /// Pans the camera by a world offset.
    pub fn pan_world(&mut self, world_delta: Vec2) {
        self.target_position += world_delta;
        self.dirty = true;
    }

    /// Starts a smooth transition to a new position and zoom.
    pub fn transition_to(&mut self, position: Vec2, zoom: f32, duration: f32) {
        self.transition = Some(CameraTransition {
            start_position: self.position,
            end_position: position,
            start_zoom: self.zoom,
            end_zoom: zoom.clamp(self.min_zoom, self.max_zoom),
            tween: Tween::new(0.0, 1.0, duration, Easing::QuadInOut),
        });
    }

    /// Fits the camera to show the given bounds with optional padding.
    pub fn fit_to_bounds(&mut self, bounds: &Bounds, padding: f32) {
        let center = bounds.center();
        let size = bounds.size();

        // Calculate zoom to fit
        let zoom_x = self.viewport_width / (size.x + padding * 2.0);
        let zoom_y = self.viewport_height / (size.y + padding * 2.0);
        let new_zoom = zoom_x.min(zoom_y).clamp(self.min_zoom, self.max_zoom);

        self.target_position = center;
        self.target_zoom = new_zoom;
        self.dirty = true;
    }

    /// Smoothly fits the camera to bounds over a duration.
    pub fn animate_fit_to_bounds(&mut self, bounds: &Bounds, padding: f32, duration: f32) {
        let center = bounds.center();
        let size = bounds.size();

        let zoom_x = self.viewport_width / (size.x + padding * 2.0);
        let zoom_y = self.viewport_height / (size.y + padding * 2.0);
        let new_zoom = zoom_x.min(zoom_y).clamp(self.min_zoom, self.max_zoom);

        self.transition_to(center, new_zoom, duration);
    }

    /// Updates the camera state.
    ///
    /// Call this once per frame with the delta time.
    pub fn update(&mut self, dt: f32) {
        if self.mode == CameraMode::Locked {
            return;
        }

        // Handle active transition
        if let Some(ref mut transition) = self.transition {
            transition.tween.update(dt);
            let t = transition.tween.eased_progress();

            self.position = transition.start_position.lerp(transition.end_position, t);
            self.zoom = transition.start_zoom + (transition.end_zoom - transition.start_zoom) * t;

            if transition.tween.is_complete() {
                self.target_position = self.position;
                self.target_zoom = self.zoom;
                self.transition = None;
            }

            self.dirty = true;
            return;
        }

        // Smooth interpolation
        let lerp_factor = 1.0 - self.smoothness.powf(dt * 60.0);

        // Update position
        if (self.target_position - self.position).length() > 0.01 {
            self.position = self.position.lerp(self.target_position, lerp_factor);
            self.dirty = true;
        } else {
            self.position = self.target_position;
        }

        // Update zoom
        if (self.target_zoom - self.zoom).abs() > 0.001 {
            self.zoom = self.zoom + (self.target_zoom - self.zoom) * lerp_factor;
            self.dirty = true;
        } else {
            self.zoom = self.target_zoom;
        }

        // Clamp to bounds if set
        if let Some(ref bounds) = self.bounds {
            self.position.x = self.position.x.clamp(bounds.min.x, bounds.max.x);
            self.position.y = self.position.y.clamp(bounds.min.y, bounds.max.y);
        }
    }

    /// Returns true if the camera state has changed since last frame.
    #[inline]
    #[must_use]
    pub const fn is_dirty(&self) -> bool {
        self.dirty
    }

    /// Clears the dirty flag.
    pub fn clear_dirty(&mut self) {
        self.dirty = false;
    }

    /// Resets the camera to default state.
    pub fn reset(&mut self) {
        self.position = Vec2::ZERO;
        self.target_position = Vec2::ZERO;
        self.zoom = DEFAULT_ZOOM;
        self.target_zoom = DEFAULT_ZOOM;
        self.transition = None;
        self.dirty = true;
    }
}

/// Camera controller for tracking multiple entities.
///
/// This helper calculates the optimal camera position and zoom
/// to keep a set of tracked positions visible.
#[derive(Debug, Clone, Default)]
pub struct CameraTracker {
    /// Tracked positions.
    positions: Vec<Vec2>,

    /// Padding around tracked entities.
    padding: f32,

    /// Weight for each position (defaults to 1.0).
    weights: Vec<f32>,
}

impl CameraTracker {
    /// Creates a new camera tracker.
    #[must_use]
    pub fn new() -> Self {
        Self {
            positions: Vec::new(),
            padding: 50.0,
            weights: Vec::new(),
        }
    }

    /// Sets the padding around tracked entities.
    pub fn set_padding(&mut self, padding: f32) {
        self.padding = padding.max(0.0);
    }

    /// Clears all tracked positions.
    pub fn clear(&mut self) {
        self.positions.clear();
        self.weights.clear();
    }

    /// Adds a position to track.
    pub fn track(&mut self, position: Vec2) {
        self.positions.push(position);
        self.weights.push(1.0);
    }

    /// Adds a position with a weight.
    ///
    /// Higher weight positions have more influence on the camera.
    pub fn track_weighted(&mut self, position: Vec2, weight: f32) {
        self.positions.push(position);
        self.weights.push(weight.max(0.0));
    }

    /// Returns the number of tracked positions.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.positions.len()
    }

    /// Returns true if no positions are tracked.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.positions.is_empty()
    }

    /// Calculates the weighted center of all tracked positions.
    #[must_use]
    pub fn weighted_center(&self) -> Vec2 {
        if self.positions.is_empty() {
            return Vec2::ZERO;
        }

        let total_weight: f32 = self.weights.iter().sum();
        if total_weight < f32::EPSILON {
            return Vec2::ZERO;
        }

        let weighted_sum: Vec2 = self
            .positions
            .iter()
            .zip(self.weights.iter())
            .map(|(&pos, &weight)| pos * weight)
            .fold(Vec2::ZERO, |acc, p| acc + p);

        weighted_sum / total_weight
    }

    /// Calculates the bounds containing all tracked positions.
    #[must_use]
    pub fn tracked_bounds(&self) -> Option<Bounds> {
        if self.positions.is_empty() {
            return None;
        }

        let mut min = self.positions[0];
        let mut max = self.positions[0];

        for &pos in &self.positions[1..] {
            min.x = min.x.min(pos.x);
            min.y = min.y.min(pos.y);
            max.x = max.x.max(pos.x);
            max.y = max.y.max(pos.y);
        }

        // Add padding
        min -= Vec2::splat(self.padding);
        max += Vec2::splat(self.padding);

        Some(Bounds::new(min, max))
    }

    /// Calculates optimal zoom to fit all tracked positions.
    #[must_use]
    pub fn optimal_zoom(&self, viewport_width: f32, viewport_height: f32) -> f32 {
        self.tracked_bounds().map_or(DEFAULT_ZOOM, |bounds| {
            let size = bounds.size();
            let zoom_x = viewport_width / size.x;
            let zoom_y = viewport_height / size.y;
            zoom_x.min(zoom_y)
        })
    }

    /// Applies tracking to a camera.
    ///
    /// This sets the camera's target position and zoom to fit
    /// all tracked positions.
    pub fn apply_to_camera(&self, camera: &mut Camera) {
        if self.is_empty() {
            return;
        }

        camera.set_target_position(self.weighted_center());

        if let Some(bounds) = self.tracked_bounds() {
            let (vw, vh) = camera.viewport_size();
            let size = bounds.size();
            let zoom_x = vw / size.x;
            let zoom_y = vh / size.y;
            let new_zoom = zoom_x.min(zoom_y);
            camera.set_target_zoom(new_zoom);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use helpers::*;

    const EPSILON: f32 = 0.01;

    fn approx_eq(a: f32, b: f32) -> bool {
        (a - b).abs() < EPSILON
    }

    fn vec2_approx_eq(a: Vec2, b: Vec2) -> bool {
        approx_eq(a.x, b.x) && approx_eq(a.y, b.y)
    }

    // ========================================================================
    // Helper Function Tests
    // ========================================================================

    #[test]
    fn test_calculate_lerp_factor_zero_smoothness() {
        let factor = calculate_lerp_factor(0.0, 0.016);
        // Zero smoothness = instant movement (factor = 1.0)
        assert!(approx_eq(factor, 1.0));
    }

    #[test]
    fn test_calculate_lerp_factor_high_smoothness() {
        let factor = calculate_lerp_factor(0.9, 0.016);
        // High smoothness = slow movement (small factor)
        assert!(factor > 0.0 && factor < 1.0);
    }

    #[test]
    fn test_calculate_lerp_factor_frame_rate_independence() {
        // Two frames at 60fps should equal one at 30fps roughly
        let factor_60fps = calculate_lerp_factor(0.5, 1.0 / 60.0);
        let factor_30fps = calculate_lerp_factor(0.5, 1.0 / 30.0);
        assert!(factor_30fps > factor_60fps);
    }

    #[test]
    fn test_calculate_fit_zoom_square() {
        let zoom = calculate_fit_zoom(800.0, 800.0, 400.0, 400.0, 0.0);
        assert!(approx_eq(zoom, 2.0));
    }

    #[test]
    fn test_calculate_fit_zoom_wide_content() {
        let zoom = calculate_fit_zoom(800.0, 600.0, 1600.0, 600.0, 0.0);
        // Width is limiting factor: 800/1600 = 0.5
        assert!(approx_eq(zoom, 0.5));
    }

    #[test]
    fn test_calculate_fit_zoom_tall_content() {
        let zoom = calculate_fit_zoom(800.0, 600.0, 400.0, 1200.0, 0.0);
        // Height is limiting factor: 600/1200 = 0.5
        assert!(approx_eq(zoom, 0.5));
    }

    #[test]
    fn test_calculate_fit_zoom_with_padding() {
        let zoom = calculate_fit_zoom(800.0, 600.0, 700.0, 500.0, 50.0);
        // With 50px padding: 800/(700+100)=1.0, 600/(500+100)=1.0
        assert!(approx_eq(zoom, 1.0));
    }

    #[test]
    fn test_clamp_zoom_within_range() {
        assert!(approx_eq(clamp_zoom(1.0, 0.1, 10.0), 1.0));
    }

    #[test]
    fn test_clamp_zoom_below_min() {
        assert!(approx_eq(clamp_zoom(0.01, 0.1, 10.0), 0.1));
    }

    #[test]
    fn test_clamp_zoom_above_max() {
        assert!(approx_eq(clamp_zoom(100.0, 0.1, 10.0), 10.0));
    }

    #[test]
    fn test_visible_half_size_zoom_1() {
        let (hw, hh) = visible_half_size(800.0, 600.0, 1.0);
        assert!(approx_eq(hw, 400.0));
        assert!(approx_eq(hh, 300.0));
    }

    #[test]
    fn test_visible_half_size_zoom_2() {
        let (hw, hh) = visible_half_size(800.0, 600.0, 2.0);
        assert!(approx_eq(hw, 200.0));
        assert!(approx_eq(hh, 150.0));
    }

    #[test]
    fn test_has_reached_target_position_at_target() {
        assert!(has_reached_target_position(
            100.0, 100.0, 100.0, 100.0, 0.01
        ));
    }

    #[test]
    fn test_has_reached_target_position_within_threshold() {
        assert!(has_reached_target_position(
            100.0, 100.0, 100.005, 100.005, 0.01
        ));
    }

    #[test]
    fn test_has_reached_target_position_outside_threshold() {
        assert!(!has_reached_target_position(
            100.0, 100.0, 101.0, 101.0, 0.01
        ));
    }

    #[test]
    fn test_has_reached_target_zoom_at_target() {
        assert!(has_reached_target_zoom(1.0, 1.0, 0.001));
    }

    #[test]
    fn test_has_reached_target_zoom_within_threshold() {
        assert!(has_reached_target_zoom(1.0, 1.0005, 0.001));
    }

    #[test]
    fn test_has_reached_target_zoom_outside_threshold() {
        assert!(!has_reached_target_zoom(1.0, 1.5, 0.001));
    }

    #[test]
    fn test_calculate_zoom_in() {
        let new_zoom = calculate_zoom_in(1.0, 1.0, 0.1);
        assert!(approx_eq(new_zoom, 1.1));
    }

    #[test]
    fn test_calculate_zoom_out() {
        let new_zoom = calculate_zoom_out(1.0, 1.0, 0.1);
        // 1.0 / 1.1 ≈ 0.909
        assert!(new_zoom < 1.0);
    }

    #[test]
    fn test_screen_to_world_coords_center() {
        let (wx, wy) = screen_to_world_coords(400.0, 300.0, 0.0, 0.0, 800.0, 600.0, 1.0);
        assert!(approx_eq(wx, 0.0));
        assert!(approx_eq(wy, 0.0));
    }

    #[test]
    fn test_screen_to_world_coords_top_left() {
        let (wx, wy) = screen_to_world_coords(0.0, 0.0, 0.0, 0.0, 800.0, 600.0, 1.0);
        assert!(approx_eq(wx, -400.0));
        assert!(approx_eq(wy, -300.0));
    }

    #[test]
    fn test_screen_to_world_coords_with_zoom() {
        let (wx, wy) = screen_to_world_coords(400.0, 300.0, 0.0, 0.0, 800.0, 600.0, 2.0);
        assert!(approx_eq(wx, 0.0));
        assert!(approx_eq(wy, 0.0));
    }

    #[test]
    fn test_world_to_screen_coords_origin() {
        let (sx, sy) = world_to_screen_coords(0.0, 0.0, 0.0, 0.0, 800.0, 600.0, 1.0);
        assert!(approx_eq(sx, 400.0));
        assert!(approx_eq(sy, 300.0));
    }

    #[test]
    fn test_world_to_screen_coords_offset() {
        let (sx, sy) = world_to_screen_coords(100.0, 50.0, 0.0, 0.0, 800.0, 600.0, 1.0);
        assert!(approx_eq(sx, 500.0));
        assert!(approx_eq(sy, 350.0));
    }

    #[test]
    fn test_calculate_tracker_zoom_square() {
        let zoom = calculate_tracker_zoom(400.0, 400.0, 800.0, 800.0);
        assert!(approx_eq(zoom, 2.0));
    }

    #[test]
    fn test_calculate_tracker_zoom_rectangular() {
        let zoom = calculate_tracker_zoom(1600.0, 600.0, 800.0, 600.0);
        // Width is limiting: 800/1600 = 0.5
        assert!(approx_eq(zoom, 0.5));
    }

    #[test]
    fn test_clamp_smoothness_valid() {
        assert!(approx_eq(clamp_smoothness(0.5), 0.5));
    }

    #[test]
    fn test_clamp_smoothness_below_min() {
        assert!(approx_eq(clamp_smoothness(-0.5), 0.0));
    }

    #[test]
    fn test_clamp_smoothness_above_max() {
        assert!(approx_eq(clamp_smoothness(1.5), 0.99));
    }

    #[test]
    fn test_lerp_start() {
        assert!(approx_eq(lerp(0.0, 10.0, 20.0), 10.0));
    }

    #[test]
    fn test_lerp_end() {
        assert!(approx_eq(lerp(1.0, 10.0, 20.0), 20.0));
    }

    #[test]
    fn test_lerp_middle() {
        assert!(approx_eq(lerp(0.5, 10.0, 20.0), 15.0));
    }

    // ========================================================================
    // Camera Tests (existing)
    // ========================================================================

    #[test]
    fn test_camera_new() {
        let camera = Camera::new(1920.0, 1080.0);

        assert_eq!(camera.position(), Vec2::ZERO);
        assert_eq!(camera.zoom(), DEFAULT_ZOOM);
        assert_eq!(camera.viewport_size(), (1920.0, 1080.0));
    }

    #[test]
    fn test_camera_centered_on() {
        let camera = Camera::centered_on(Vec2::new(100.0, 50.0), 800.0, 600.0);

        assert_eq!(camera.position(), Vec2::new(100.0, 50.0));
    }

    #[test]
    fn test_camera_set_position() {
        let mut camera = Camera::new(800.0, 600.0);

        camera.set_target_position(Vec2::new(100.0, 100.0));
        assert_eq!(camera.target_position(), Vec2::new(100.0, 100.0));

        camera.jump_to(Vec2::new(200.0, 200.0));
        assert_eq!(camera.position(), Vec2::new(200.0, 200.0));
        assert_eq!(camera.target_position(), Vec2::new(200.0, 200.0));
    }

    #[test]
    fn test_camera_zoom() {
        let mut camera = Camera::new(800.0, 600.0);

        camera.set_zoom(2.0);
        assert_eq!(camera.zoom(), 2.0);

        camera.set_target_zoom(0.5);
        assert_eq!(camera.target_zoom(), 0.5);

        // Zoom limits
        camera.set_zoom(100.0);
        assert_eq!(camera.zoom(), MAX_ZOOM);

        camera.set_zoom(0.0);
        assert_eq!(camera.zoom(), MIN_ZOOM);
    }

    #[test]
    fn test_camera_zoom_in_out() {
        let mut camera = Camera::new(800.0, 600.0);
        camera.set_zoom(1.0);

        let initial_zoom = camera.zoom();

        camera.zoom_in(1.0);
        assert!(camera.target_zoom() > initial_zoom);

        camera.set_zoom(1.0);
        camera.zoom_out(1.0);
        assert!(camera.target_zoom() < initial_zoom);
    }

    #[test]
    fn test_camera_visible_bounds() {
        let mut camera = Camera::new(800.0, 600.0);
        camera.jump_to(Vec2::ZERO);
        camera.set_zoom(1.0);

        let bounds = camera.visible_bounds();

        assert!(approx_eq(bounds.center().x, 0.0));
        assert!(approx_eq(bounds.center().y, 0.0));
        assert!(approx_eq(bounds.size().x, 800.0));
        assert!(approx_eq(bounds.size().y, 600.0));
    }

    #[test]
    fn test_camera_screen_to_world() {
        let mut camera = Camera::new(800.0, 600.0);
        camera.jump_to(Vec2::ZERO);
        camera.set_zoom(1.0);

        // Center of screen should map to camera position
        let center = camera.screen_to_world(Vec2::new(400.0, 300.0));
        assert!(vec2_approx_eq(center, Vec2::ZERO));

        // Top-left corner
        let top_left = camera.screen_to_world(Vec2::ZERO);
        assert!(vec2_approx_eq(top_left, Vec2::new(-400.0, -300.0)));
    }

    #[test]
    fn test_camera_world_to_screen() {
        let mut camera = Camera::new(800.0, 600.0);
        camera.jump_to(Vec2::ZERO);
        camera.set_zoom(1.0);

        // Camera position should map to center of screen
        let center = camera.world_to_screen(Vec2::ZERO);
        assert!(vec2_approx_eq(center, Vec2::new(400.0, 300.0)));
    }

    #[test]
    fn test_camera_is_visible() {
        let mut camera = Camera::new(800.0, 600.0);
        camera.jump_to(Vec2::ZERO);
        camera.set_zoom(1.0);

        assert!(camera.is_visible(Vec2::ZERO));
        assert!(camera.is_visible(Vec2::new(100.0, 100.0)));
        assert!(!camera.is_visible(Vec2::new(1000.0, 1000.0)));
    }

    #[test]
    fn test_camera_pan() {
        let mut camera = Camera::new(800.0, 600.0);
        camera.jump_to(Vec2::ZERO);
        camera.set_zoom(1.0);

        camera.pan(Vec2::new(100.0, 0.0));
        // Pan inverts direction (dragging right moves view left)
        assert!(camera.target_position().x < 0.0);
    }

    #[test]
    fn test_camera_update_smooth() {
        let mut camera = Camera::new(800.0, 600.0);
        camera.set_smoothness(0.5);
        camera.set_target_position(Vec2::new(100.0, 0.0));

        // After update, should be moving toward target
        camera.update(0.016);
        assert!(camera.position().x > 0.0);
        assert!(camera.position().x < 100.0);

        // After many updates, should reach target
        for _ in 0..1000 {
            camera.update(0.016);
        }
        assert!(vec2_approx_eq(camera.position(), Vec2::new(100.0, 0.0)));
    }

    #[test]
    fn test_camera_transition() {
        let mut camera = Camera::new(800.0, 600.0);
        camera.jump_to(Vec2::ZERO);
        camera.set_zoom(1.0);

        camera.transition_to(Vec2::new(100.0, 100.0), 2.0, 1.0);

        // After half the duration
        camera.update(0.5);
        assert!(camera.position().x > 0.0 && camera.position().x < 100.0);
        assert!(camera.zoom() > 1.0 && camera.zoom() < 2.0);

        // After full duration
        camera.update(0.6);
        assert!(vec2_approx_eq(camera.position(), Vec2::new(100.0, 100.0)));
        assert!(approx_eq(camera.zoom(), 2.0));
    }

    #[test]
    fn test_camera_fit_to_bounds() {
        let mut camera = Camera::new(800.0, 600.0);

        let bounds = Bounds::new(Vec2::new(0.0, 0.0), Vec2::new(1600.0, 1200.0));
        camera.fit_to_bounds(&bounds, 0.0);

        // Camera should center on bounds
        assert!(vec2_approx_eq(
            camera.target_position(),
            Vec2::new(800.0, 600.0)
        ));

        // Zoom should be 0.5 to fit 1600x1200 in 800x600
        assert!(approx_eq(camera.target_zoom(), 0.5));
    }

    #[test]
    fn test_camera_mode() {
        let mut camera = Camera::new(800.0, 600.0);

        assert_eq!(camera.mode(), CameraMode::Manual);

        camera.set_mode(CameraMode::Locked);
        assert_eq!(camera.mode(), CameraMode::Locked);

        // Locked camera should not update
        camera.set_target_position(Vec2::new(100.0, 0.0));
        camera.update(1.0);
        assert_eq!(camera.position(), Vec2::ZERO);
    }

    #[test]
    fn test_camera_reset() {
        let mut camera = Camera::new(800.0, 600.0);
        camera.jump_to(Vec2::new(100.0, 100.0));
        camera.set_zoom(2.0);

        camera.reset();

        assert_eq!(camera.position(), Vec2::ZERO);
        assert_eq!(camera.zoom(), DEFAULT_ZOOM);
    }

    #[test]
    fn test_camera_tracker_new() {
        let tracker = CameraTracker::new();
        assert!(tracker.is_empty());
    }

    #[test]
    fn test_camera_tracker_track() {
        let mut tracker = CameraTracker::new();

        tracker.track(Vec2::new(0.0, 0.0));
        tracker.track(Vec2::new(100.0, 100.0));

        assert_eq!(tracker.len(), 2);
        assert!(!tracker.is_empty());
    }

    #[test]
    fn test_camera_tracker_weighted_center() {
        let mut tracker = CameraTracker::new();

        tracker.track_weighted(Vec2::new(0.0, 0.0), 1.0);
        tracker.track_weighted(Vec2::new(100.0, 0.0), 1.0);

        let center = tracker.weighted_center();
        assert!(vec2_approx_eq(center, Vec2::new(50.0, 0.0)));

        // With different weights
        let mut tracker2 = CameraTracker::new();
        tracker2.track_weighted(Vec2::new(0.0, 0.0), 1.0);
        tracker2.track_weighted(Vec2::new(100.0, 0.0), 3.0);

        let center2 = tracker2.weighted_center();
        // Weighted toward 100.0
        assert!(center2.x > 50.0);
    }

    #[test]
    fn test_camera_tracker_bounds() {
        let mut tracker = CameraTracker::new();
        tracker.set_padding(0.0);

        tracker.track(Vec2::new(0.0, 0.0));
        tracker.track(Vec2::new(100.0, 100.0));

        let bounds = tracker.tracked_bounds().unwrap();
        assert!(vec2_approx_eq(bounds.min, Vec2::new(0.0, 0.0)));
        assert!(vec2_approx_eq(bounds.max, Vec2::new(100.0, 100.0)));
    }

    #[test]
    fn test_camera_tracker_clear() {
        let mut tracker = CameraTracker::new();
        tracker.track(Vec2::new(100.0, 100.0));

        assert!(!tracker.is_empty());

        tracker.clear();
        assert!(tracker.is_empty());
    }

    #[test]
    fn test_camera_tracker_apply() {
        let mut camera = Camera::new(800.0, 600.0);
        let mut tracker = CameraTracker::new();
        tracker.set_padding(0.0);

        tracker.track(Vec2::new(0.0, 0.0));
        tracker.track(Vec2::new(100.0, 100.0));

        tracker.apply_to_camera(&mut camera);

        assert!(vec2_approx_eq(
            camera.target_position(),
            Vec2::new(50.0, 50.0)
        ));
    }
}
