// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! 3D Orbit Camera for perspective visualization.
//!
//! This module provides a 3D camera with orbit controls for Gource-style
//! visualization where the camera can rotate around a target point.
//!
//! # Example
//!
//! ```
//! use rource_core::camera::Camera3D;
//! use rource_math::Vec3;
//!
//! let mut camera = Camera3D::new(1920.0, 1080.0);
//!
//! // Orbit the camera around the target
//! camera.orbit(0.1, 0.05); // yaw, pitch in radians
//!
//! // Get the view-projection matrix for rendering
//! let vp = camera.view_projection_matrix();
//! ```

use rource_math::{Mat4, Vec2, Vec3};

use crate::animation::{Easing, Tween};

/// Default field of view in radians (45 degrees).
pub const DEFAULT_FOV: f32 = std::f32::consts::FRAC_PI_4;

/// Default near clipping plane.
pub const DEFAULT_NEAR: f32 = 0.1;

/// Default far clipping plane.
pub const DEFAULT_FAR: f32 = 10000.0;

/// Default orbit distance.
pub const DEFAULT_ORBIT_DISTANCE: f32 = 500.0;

/// Minimum orbit distance.
pub const MIN_ORBIT_DISTANCE: f32 = 10.0;

/// Maximum orbit distance.
pub const MAX_ORBIT_DISTANCE: f32 = 5000.0;

/// Default pitch angle (radians) - slightly from above.
pub const DEFAULT_PITCH: f32 = -0.3;

/// Minimum pitch angle (looking from above, radians).
pub const MIN_PITCH: f32 = -std::f32::consts::FRAC_PI_2 + 0.1;

/// Maximum pitch angle (looking from below, radians).
pub const MAX_PITCH: f32 = std::f32::consts::FRAC_PI_2 - 0.1;

/// Default auto-rotation speed (radians per second).
pub const DEFAULT_AUTO_ROTATION_SPEED: f32 = 0.05;

/// Default camera smoothness (0 = instant, 1 = very slow).
pub const DEFAULT_3D_SMOOTHNESS: f32 = 0.9;

/// 3D orbit camera for perspective visualization.
///
/// The camera orbits around a target point and can be controlled via:
/// - Orbit (yaw/pitch rotation around target)
/// - Zoom (change orbit distance)
/// - Pan (move target point)
/// - Auto-rotation (slow automatic yaw rotation)
#[derive(Debug, Clone)]
pub struct Camera3D {
    /// Target point the camera orbits around.
    target: Vec3,

    /// Target position for smooth movement.
    target_target: Vec3,

    /// Current orbit yaw angle (radians, around Y axis).
    yaw: f32,

    /// Target yaw for smooth rotation.
    target_yaw: f32,

    /// Current orbit pitch angle (radians, around X axis).
    pitch: f32,

    /// Target pitch for smooth rotation.
    target_pitch: f32,

    /// Current orbit distance from target.
    distance: f32,

    /// Target distance for smooth zoom.
    target_distance: f32,

    /// Field of view (radians).
    fov: f32,

    /// Near clipping plane.
    near: f32,

    /// Far clipping plane.
    far: f32,

    /// Viewport width.
    viewport_width: f32,

    /// Viewport height.
    viewport_height: f32,

    /// Smoothness factor (0.0 = instant, 1.0 = very slow).
    smoothness: f32,

    /// Whether auto-rotation is enabled.
    auto_rotate: bool,

    /// Auto-rotation speed (radians per second).
    auto_rotation_speed: f32,

    /// Time since last user interaction (for auto-rotation delay).
    idle_time: f32,

    /// Idle time threshold before auto-rotation starts (seconds).
    auto_rotation_delay: f32,

    /// Cached view matrix.
    view_matrix: Mat4,

    /// Cached projection matrix.
    projection_matrix: Mat4,

    /// Whether matrices need recalculation.
    dirty: bool,

    /// Optional transition animation.
    transition: Option<Camera3DTransition>,
}

/// A camera transition for smooth movements.
#[derive(Debug, Clone)]
struct Camera3DTransition {
    start_target: Vec3,
    end_target: Vec3,
    start_yaw: f32,
    end_yaw: f32,
    start_pitch: f32,
    end_pitch: f32,
    start_distance: f32,
    end_distance: f32,
    tween: Tween,
}

impl Default for Camera3D {
    fn default() -> Self {
        Self::new(1920.0, 1080.0)
    }
}

impl Camera3D {
    /// Creates a new 3D camera with the given viewport dimensions.
    #[must_use]
    pub fn new(viewport_width: f32, viewport_height: f32) -> Self {
        let mut camera = Self {
            target: Vec3::ZERO,
            target_target: Vec3::ZERO,
            yaw: 0.0,
            target_yaw: 0.0,
            pitch: DEFAULT_PITCH,
            target_pitch: DEFAULT_PITCH,
            distance: DEFAULT_ORBIT_DISTANCE,
            target_distance: DEFAULT_ORBIT_DISTANCE,
            fov: DEFAULT_FOV,
            near: DEFAULT_NEAR,
            far: DEFAULT_FAR,
            viewport_width,
            viewport_height,
            smoothness: DEFAULT_3D_SMOOTHNESS,
            auto_rotate: true,
            auto_rotation_speed: DEFAULT_AUTO_ROTATION_SPEED,
            idle_time: 0.0,
            auto_rotation_delay: 3.0,
            view_matrix: Mat4::IDENTITY,
            projection_matrix: Mat4::IDENTITY,
            dirty: true,
            transition: None,
        };
        camera.update_matrices();
        camera
    }

    /// Returns the camera's eye position in world space.
    #[must_use]
    pub fn eye_position(&self) -> Vec3 {
        // Calculate eye position from spherical coordinates
        let x = self.distance * self.pitch.cos() * self.yaw.sin();
        let y = self.distance * self.pitch.sin();
        let z = self.distance * self.pitch.cos() * self.yaw.cos();
        self.target + Vec3::new(x, y, z)
    }

    /// Returns the target point the camera orbits around.
    #[inline]
    #[must_use]
    pub const fn target(&self) -> Vec3 {
        self.target
    }

    /// Sets the target point for smooth transition.
    pub fn set_target(&mut self, target: Vec3) {
        self.target_target = target;
        self.dirty = true;
    }

    /// Immediately jumps to a target point.
    pub fn jump_to_target(&mut self, target: Vec3) {
        self.target = target;
        self.target_target = target;
        self.transition = None;
        self.dirty = true;
    }

    /// Returns the current yaw angle (radians).
    #[inline]
    #[must_use]
    pub const fn yaw(&self) -> f32 {
        self.yaw
    }

    /// Returns the current pitch angle (radians).
    #[inline]
    #[must_use]
    pub const fn pitch(&self) -> f32 {
        self.pitch
    }

    /// Returns the current orbit distance.
    #[inline]
    #[must_use]
    pub const fn distance(&self) -> f32 {
        self.distance
    }

    /// Sets the orbit distance for smooth zoom.
    pub fn set_distance(&mut self, distance: f32) {
        self.target_distance = distance.clamp(MIN_ORBIT_DISTANCE, MAX_ORBIT_DISTANCE);
        self.dirty = true;
    }

    /// Immediately sets the orbit distance.
    pub fn jump_to_distance(&mut self, distance: f32) {
        let d = distance.clamp(MIN_ORBIT_DISTANCE, MAX_ORBIT_DISTANCE);
        self.distance = d;
        self.target_distance = d;
        self.transition = None;
        self.dirty = true;
    }

    /// Orbits the camera around the target.
    ///
    /// # Arguments
    /// * `delta_yaw` - Horizontal rotation change (radians, positive = right)
    /// * `delta_pitch` - Vertical rotation change (radians, positive = up)
    pub fn orbit(&mut self, delta_yaw: f32, delta_pitch: f32) {
        self.target_yaw += delta_yaw;
        self.target_pitch = (self.target_pitch + delta_pitch).clamp(MIN_PITCH, MAX_PITCH);
        self.idle_time = 0.0;
        self.dirty = true;
    }

    /// Immediately sets the orbit angles.
    pub fn jump_to_orbit(&mut self, yaw: f32, pitch: f32) {
        self.yaw = yaw;
        self.target_yaw = yaw;
        self.pitch = pitch.clamp(MIN_PITCH, MAX_PITCH);
        self.target_pitch = self.pitch;
        self.transition = None;
        self.dirty = true;
    }

    /// Zooms the camera (changes orbit distance).
    ///
    /// # Arguments
    /// * `factor` - Zoom factor (positive = zoom in, negative = zoom out)
    pub fn zoom(&mut self, factor: f32) {
        let zoom_multiplier = 1.0 - factor * 0.1;
        self.target_distance =
            (self.target_distance * zoom_multiplier).clamp(MIN_ORBIT_DISTANCE, MAX_ORBIT_DISTANCE);
        self.idle_time = 0.0;
        self.dirty = true;
    }

    /// Pans the camera (moves the target point).
    ///
    /// # Arguments
    /// * `delta` - World-space delta to move the target
    pub fn pan(&mut self, delta: Vec3) {
        // Transform delta from camera-relative to world space
        let right = Vec3::new(self.yaw.cos(), 0.0, -self.yaw.sin());
        let up = Vec3::Y;

        self.target_target += right * delta.x + up * delta.y + Vec3::new(0.0, 0.0, delta.z);
        self.idle_time = 0.0;
        self.dirty = true;
    }

    /// Pans the camera based on screen-space delta.
    ///
    /// # Arguments
    /// * `screen_delta` - Screen-space delta (pixels)
    pub fn pan_screen(&mut self, screen_delta: Vec2) {
        // Scale pan by distance so it feels consistent at all zoom levels
        let scale = self.distance * 0.002;
        let world_delta = Vec3::new(-screen_delta.x * scale, screen_delta.y * scale, 0.0);
        self.pan(world_delta);
    }

    /// Returns the field of view (radians).
    #[inline]
    #[must_use]
    pub const fn fov(&self) -> f32 {
        self.fov
    }

    /// Sets the field of view (radians).
    pub fn set_fov(&mut self, fov: f32) {
        self.fov = fov.clamp(0.1, std::f32::consts::PI - 0.1);
        self.dirty = true;
    }

    /// Returns the viewport dimensions.
    #[inline]
    #[must_use]
    pub const fn viewport_size(&self) -> (f32, f32) {
        (self.viewport_width, self.viewport_height)
    }

    /// Sets the viewport dimensions.
    pub fn set_viewport_size(&mut self, width: f32, height: f32) {
        self.viewport_width = width;
        self.viewport_height = height;
        self.dirty = true;
    }

    /// Returns whether auto-rotation is enabled.
    #[inline]
    #[must_use]
    pub const fn auto_rotate(&self) -> bool {
        self.auto_rotate
    }

    /// Enables or disables auto-rotation.
    pub fn set_auto_rotate(&mut self, enabled: bool) {
        self.auto_rotate = enabled;
    }

    /// Returns the auto-rotation speed (radians per second).
    #[inline]
    #[must_use]
    pub const fn auto_rotation_speed(&self) -> f32 {
        self.auto_rotation_speed
    }

    /// Sets the auto-rotation speed (radians per second).
    pub fn set_auto_rotation_speed(&mut self, speed: f32) {
        self.auto_rotation_speed = speed;
    }

    /// Sets the smoothness factor (0.0 = instant, ~0.99 = very slow).
    pub fn set_smoothness(&mut self, smoothness: f32) {
        self.smoothness = smoothness.clamp(0.0, 0.99);
    }

    /// Returns the view matrix.
    #[must_use]
    pub fn view_matrix(&self) -> Mat4 {
        self.view_matrix
    }

    /// Returns the projection matrix.
    #[must_use]
    pub fn projection_matrix(&self) -> Mat4 {
        self.projection_matrix
    }

    /// Returns the combined view-projection matrix.
    #[must_use]
    pub fn view_projection_matrix(&self) -> Mat4 {
        self.projection_matrix * self.view_matrix
    }

    /// Projects a world position to screen coordinates.
    ///
    /// Returns `None` if the point is behind the camera.
    #[must_use]
    pub fn world_to_screen(&self, world_pos: Vec3) -> Option<Vec2> {
        let clip = self.view_projection_matrix().transform_point(world_pos);
        let clip_w = {
            let vp = self.view_projection_matrix();
            world_pos.x * vp.m[3] + world_pos.y * vp.m[7] + world_pos.z * vp.m[11] + vp.m[15]
        };

        // Behind camera
        if clip_w <= 0.0 {
            return None;
        }

        // NDC to screen
        let ndc_x = clip.x / clip_w;
        let ndc_y = clip.y / clip_w;

        let screen_x = (ndc_x + 1.0) * 0.5 * self.viewport_width;
        let screen_y = (1.0 - ndc_y) * 0.5 * self.viewport_height; // Y is flipped

        Some(Vec2::new(screen_x, screen_y))
    }

    /// Calculates the projected radius of a sphere on screen.
    ///
    /// Returns the approximate screen-space radius in pixels.
    #[must_use]
    pub fn project_radius(&self, center: Vec3, radius: f32) -> f32 {
        let distance = (center - self.eye_position()).length();
        if distance < 0.001 {
            return radius * self.viewport_height;
        }

        // Approximate screen radius using field of view
        let projected = radius / (distance * (self.fov * 0.5).tan());
        projected * self.viewport_height * 0.5
    }

    /// Starts a smooth transition to new camera parameters.
    pub fn transition_to(
        &mut self,
        target: Vec3,
        yaw: f32,
        pitch: f32,
        distance: f32,
        duration: f32,
    ) {
        self.transition = Some(Camera3DTransition {
            start_target: self.target,
            end_target: target,
            start_yaw: self.yaw,
            end_yaw: yaw,
            start_pitch: self.pitch,
            end_pitch: pitch.clamp(MIN_PITCH, MAX_PITCH),
            start_distance: self.distance,
            end_distance: distance.clamp(MIN_ORBIT_DISTANCE, MAX_ORBIT_DISTANCE),
            tween: Tween::new(0.0, 1.0, duration, Easing::QuadInOut),
        });
    }

    /// Fits the camera to view the given bounds.
    pub fn fit_to_bounds(&mut self, min: Vec3, max: Vec3, padding: f32) {
        let center = (min + max) * 0.5;
        let size = max - min;
        let max_extent = size.x.max(size.y).max(size.z) + padding * 2.0;

        // Calculate distance to fit the bounds
        let distance = max_extent / (2.0 * (self.fov * 0.5).tan());

        self.target_target = center;
        self.target_distance = distance.clamp(MIN_ORBIT_DISTANCE, MAX_ORBIT_DISTANCE);
        self.dirty = true;
    }

    /// Updates the camera state. Call once per frame.
    pub fn update(&mut self, dt: f32) {
        // Handle active transition
        if let Some(ref mut transition) = self.transition {
            transition.tween.update(dt);
            let t = transition.tween.eased_progress();

            self.target = transition.start_target.lerp(transition.end_target, t);
            self.yaw = transition.start_yaw + (transition.end_yaw - transition.start_yaw) * t;
            self.pitch =
                transition.start_pitch + (transition.end_pitch - transition.start_pitch) * t;
            self.distance = transition.start_distance
                + (transition.end_distance - transition.start_distance) * t;

            if transition.tween.is_complete() {
                self.target_target = self.target;
                self.target_yaw = self.yaw;
                self.target_pitch = self.pitch;
                self.target_distance = self.distance;
                self.transition = None;
            }

            self.dirty = true;
        } else {
            // Smooth interpolation
            let lerp_factor = 1.0 - self.smoothness.powf(dt * 60.0);

            // Update target position
            if (self.target_target - self.target).length() > 0.01 {
                self.target = self.target.lerp(self.target_target, lerp_factor);
                self.dirty = true;
            } else {
                self.target = self.target_target;
            }

            // Update yaw
            if (self.target_yaw - self.yaw).abs() > 0.001 {
                self.yaw = self.yaw + (self.target_yaw - self.yaw) * lerp_factor;
                self.dirty = true;
            } else {
                self.yaw = self.target_yaw;
            }

            // Update pitch
            if (self.target_pitch - self.pitch).abs() > 0.001 {
                self.pitch = self.pitch + (self.target_pitch - self.pitch) * lerp_factor;
                self.dirty = true;
            } else {
                self.pitch = self.target_pitch;
            }

            // Update distance
            if (self.target_distance - self.distance).abs() > 0.01 {
                self.distance =
                    self.distance + (self.target_distance - self.distance) * lerp_factor;
                self.dirty = true;
            } else {
                self.distance = self.target_distance;
            }

            // Auto-rotation
            if self.auto_rotate {
                self.idle_time += dt;
                if self.idle_time > self.auto_rotation_delay {
                    self.yaw += self.auto_rotation_speed * dt;
                    self.target_yaw = self.yaw;
                    self.dirty = true;
                }
            }
        }

        // Update matrices if needed
        if self.dirty {
            self.update_matrices();
            self.dirty = false;
        }
    }

    /// Recalculates the view and projection matrices.
    fn update_matrices(&mut self) {
        // Calculate eye position from spherical coordinates
        let eye = self.eye_position();

        // View matrix
        self.view_matrix = Mat4::look_at(eye, self.target, Vec3::Y);

        // Projection matrix
        let aspect = self.viewport_width / self.viewport_height;
        self.projection_matrix = Mat4::perspective(self.fov, aspect, self.near, self.far);
    }

    /// Resets the camera to default state.
    pub fn reset(&mut self) {
        self.target = Vec3::ZERO;
        self.target_target = Vec3::ZERO;
        self.yaw = 0.0;
        self.target_yaw = 0.0;
        self.pitch = DEFAULT_PITCH;
        self.target_pitch = DEFAULT_PITCH;
        self.distance = DEFAULT_ORBIT_DISTANCE;
        self.target_distance = DEFAULT_ORBIT_DISTANCE;
        self.idle_time = 0.0;
        self.transition = None;
        self.dirty = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPSILON: f32 = 0.01;

    fn approx_eq(a: f32, b: f32) -> bool {
        (a - b).abs() < EPSILON
    }

    #[test]
    fn test_camera3d_new() {
        let camera = Camera3D::new(1920.0, 1080.0);
        assert_eq!(camera.viewport_size(), (1920.0, 1080.0));
        assert_eq!(camera.target(), Vec3::ZERO);
        assert!(approx_eq(camera.pitch(), DEFAULT_PITCH));
    }

    #[test]
    fn test_camera3d_orbit() {
        let mut camera = Camera3D::new(800.0, 600.0);
        let initial_yaw = camera.yaw();

        camera.orbit(0.1, 0.0);
        assert!(approx_eq(camera.target_yaw, initial_yaw + 0.1));
    }

    #[test]
    fn test_camera3d_pitch_clamping() {
        let mut camera = Camera3D::new(800.0, 600.0);

        // Try to pitch beyond limits
        camera.orbit(0.0, 100.0);
        assert!(camera.target_pitch <= MAX_PITCH);

        camera.orbit(0.0, -200.0);
        assert!(camera.target_pitch >= MIN_PITCH);
    }

    #[test]
    fn test_camera3d_zoom() {
        let mut camera = Camera3D::new(800.0, 600.0);
        let initial_distance = camera.distance();

        camera.zoom(1.0); // Zoom in
        assert!(camera.target_distance < initial_distance);

        let after_zoom_in = camera.target_distance;
        camera.zoom(-1.0); // Zoom out
        assert!(camera.target_distance > after_zoom_in);
    }

    #[test]
    fn test_camera3d_distance_clamping() {
        let mut camera = Camera3D::new(800.0, 600.0);

        camera.set_distance(1.0);
        assert!(camera.target_distance >= MIN_ORBIT_DISTANCE);

        camera.set_distance(10000.0);
        assert!(camera.target_distance <= MAX_ORBIT_DISTANCE);
    }

    #[test]
    fn test_camera3d_jump_to() {
        let mut camera = Camera3D::new(800.0, 600.0);

        camera.jump_to_target(Vec3::new(100.0, 50.0, 25.0));
        assert_eq!(camera.target(), Vec3::new(100.0, 50.0, 25.0));
        assert_eq!(camera.target_target, camera.target);
    }

    #[test]
    fn test_camera3d_eye_position() {
        let mut camera = Camera3D::new(800.0, 600.0);
        camera.jump_to_target(Vec3::ZERO);
        camera.jump_to_distance(100.0);
        camera.jump_to_orbit(0.0, 0.0);

        let eye = camera.eye_position();
        // With yaw=0, pitch=0, eye should be at (0, 0, distance)
        assert!(approx_eq(eye.x, 0.0));
        assert!(approx_eq(eye.y, 0.0));
        assert!(approx_eq(eye.z, 100.0));
    }

    #[test]
    fn test_camera3d_view_projection() {
        let camera = Camera3D::new(800.0, 600.0);

        let view = camera.view_matrix();
        let proj = camera.projection_matrix();
        let vp = camera.view_projection_matrix();

        // VP should be proj * view
        let expected_vp = proj * view;
        for i in 0..16 {
            assert!(
                approx_eq(vp.m[i], expected_vp.m[i]),
                "VP matrix mismatch at index {i}"
            );
        }
    }

    #[test]
    fn test_camera3d_world_to_screen_center() {
        let mut camera = Camera3D::new(800.0, 600.0);
        camera.jump_to_target(Vec3::ZERO);
        camera.jump_to_orbit(0.0, 0.0);
        camera.update(0.0);

        // Target should project to center of screen
        if let Some(screen) = camera.world_to_screen(Vec3::ZERO) {
            assert!(
                approx_eq(screen.x, 400.0),
                "Expected x=400, got {}",
                screen.x
            );
            assert!(
                approx_eq(screen.y, 300.0),
                "Expected y=300, got {}",
                screen.y
            );
        }
    }

    #[test]
    fn test_camera3d_reset() {
        let mut camera = Camera3D::new(800.0, 600.0);
        camera.jump_to_target(Vec3::new(100.0, 100.0, 100.0));
        camera.jump_to_distance(200.0);

        camera.reset();

        assert_eq!(camera.target(), Vec3::ZERO);
        assert!(approx_eq(camera.distance(), DEFAULT_ORBIT_DISTANCE));
    }

    #[test]
    fn test_camera3d_update_smooth() {
        let mut camera = Camera3D::new(800.0, 600.0);
        camera.set_smoothness(0.5);
        camera.set_target(Vec3::new(100.0, 0.0, 0.0));

        // After update, should be moving toward target
        camera.update(0.016);
        assert!(camera.target().x > 0.0);
        assert!(camera.target().x < 100.0);

        // After many updates, should reach target
        for _ in 0..1000 {
            camera.update(0.016);
        }
        assert!(approx_eq(camera.target().x, 100.0));
    }

    #[test]
    fn test_camera3d_project_radius() {
        let camera = Camera3D::new(800.0, 600.0);

        // Object at the target should have a reasonable projected size
        let radius = camera.project_radius(camera.target(), 10.0);
        assert!(radius > 0.0);
        assert!(radius < 1000.0);
    }
}
