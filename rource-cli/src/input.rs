//! Input handling for the Rource CLI.
//!
//! This module provides keyboard and mouse input handling for the windowed
//! application mode. Input can be disabled via the `--disable-input` flag.

use rource_core::camera::{Camera, Camera3D};
use rource_core::scene::{ActionType, Scene};
use rource_math::Vec2;
use rource_vcs::FileAction;
use winit::event::{ElementState, KeyEvent, MouseButton, MouseScrollDelta};
use winit::keyboard::{Key, NamedKey};

use crate::app::PlaybackState;

/// Input state for mouse interactions.
#[derive(Debug, Default)]
pub struct MouseState {
    /// Current mouse position in screen coordinates.
    pub position: Vec2,

    /// Whether the mouse is currently being dragged (left button held).
    pub dragging: bool,

    /// Last mouse position when drag started or during drag.
    pub last_position: Vec2,
}

impl MouseState {
    /// Create a new mouse state at the origin.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            position: Vec2::ZERO,
            dragging: false,
            last_position: Vec2::ZERO,
        }
    }

    /// Update the mouse position.
    pub fn set_position(&mut self, x: f64, y: f64) {
        self.position = Vec2::new(x as f32, y as f32);
    }

    /// Start dragging from the current position.
    pub fn start_drag(&mut self) {
        self.dragging = true;
        self.last_position = self.position;
    }

    /// End dragging.
    pub fn end_drag(&mut self) {
        self.dragging = false;
    }

    /// Get the drag delta since last update.
    pub fn get_drag_delta(&mut self) -> Vec2 {
        let delta = self.position - self.last_position;
        self.last_position = self.position;
        delta
    }
}

/// Convert VCS `FileAction` to scene `ActionType`.
#[must_use]
pub const fn file_action_to_action_type(action: FileAction) -> ActionType {
    match action {
        FileAction::Create => ActionType::Create,
        FileAction::Modify => ActionType::Modify,
        FileAction::Delete => ActionType::Delete,
    }
}

/// Handle keyboard input for the visualization.
///
/// Returns `true` if the application should exit.
#[allow(clippy::too_many_arguments)]
pub fn handle_key(
    event: &KeyEvent,
    playback: &mut PlaybackState,
    scene: &mut Scene,
    camera: &mut Camera,
    camera_3d: Option<&mut Camera3D>,
    current_commit: &mut usize,
    last_applied_commit: &mut usize,
    accumulated_time: &mut f64,
    total_commits: usize,
    screenshot_pending: &mut Option<std::path::PathBuf>,
    disable_input: bool,
) -> bool {
    if event.state != ElementState::Pressed {
        return false;
    }

    if disable_input {
        // Only allow quit
        if matches!(&event.logical_key, Key::Named(NamedKey::Escape)) {
            return true;
        }
        return false;
    }

    match &event.logical_key {
        Key::Named(NamedKey::Escape) => {
            return true;
        }
        Key::Named(NamedKey::Space) => {
            playback.paused = !playback.paused;
        }
        Key::Character(c) => match c.as_str() {
            "q" | "Q" => {
                return true;
            }
            "+" | "=" => {
                playback.speed = (playback.speed * 1.5).min(10.0);
                eprintln!("Speed: {:.1}x", playback.speed);
            }
            "-" | "_" => {
                playback.speed = (playback.speed / 1.5).max(0.1);
                eprintln!("Speed: {:.1}x", playback.speed);
            }
            "r" | "R" => {
                // Reset to beginning
                *current_commit = 0;
                *last_applied_commit = 0;
                *accumulated_time = 0.0;
                *scene = Scene::new();
                camera.reset();
                if let Some(cam_3d) = camera_3d {
                    cam_3d.reset();
                }
                eprintln!("Reset to beginning");
            }
            "s" | "S" => {
                // Take screenshot
                let filename = format!(
                    "rource_screenshot_{}.png",
                    chrono::Utc::now().format("%Y%m%d_%H%M%S")
                );
                *screenshot_pending = Some(std::path::PathBuf::from(&filename));
                eprintln!("Screenshot will be saved to: {filename}");
            }
            _ => {}
        },
        Key::Named(NamedKey::ArrowRight) => {
            // Skip forward
            if *current_commit + 10 < total_commits {
                *current_commit += 10;
            } else {
                *current_commit = total_commits.saturating_sub(1);
            }
        }
        Key::Named(NamedKey::ArrowLeft) => {
            // Skip backward
            *current_commit = current_commit.saturating_sub(10);
        }
        _ => {}
    }

    false
}

/// Handle mouse button press/release.
///
/// Returns the seek target commit index if timeline scrubbing occurred.
#[allow(clippy::too_many_arguments)]
pub fn handle_mouse_button(
    button: MouseButton,
    state: ElementState,
    mouse: &mut MouseState,
    camera: &mut Camera,
    camera_3d: Option<&mut Camera3D>,
    viewport_size: (f32, f32),
    total_commits: usize,
    disable_input: bool,
) -> Option<usize> {
    if disable_input {
        return None;
    }

    match button {
        MouseButton::Left => match state {
            ElementState::Pressed => {
                let (width, height) = viewport_size;
                let bar_height = 12.0; // Clickable area is larger than visual bar

                // Check if clicking on progress bar (timeline scrubbing)
                if mouse.position.y >= height - bar_height && total_commits > 0 {
                    let progress = (mouse.position.x / width).clamp(0.0, 1.0);
                    let target_commit = (progress * total_commits as f32).round() as usize;
                    return Some(target_commit);
                }

                mouse.start_drag();
            }
            ElementState::Released => {
                mouse.end_drag();
            }
        },
        MouseButton::Middle => {
            // Middle click resets camera
            if state == ElementState::Pressed {
                if let Some(cam_3d) = camera_3d {
                    cam_3d.reset();
                } else {
                    camera.reset();
                }
            }
        }
        _ => {}
    }

    None
}

/// Handle mouse movement.
pub fn handle_mouse_move(
    x: f64,
    y: f64,
    mouse: &mut MouseState,
    camera: &mut Camera,
    camera_3d: Option<&mut Camera3D>,
    disable_input: bool,
) {
    mouse.set_position(x, y);

    if disable_input {
        return;
    }

    // Pan (2D) or orbit (3D) when dragging
    if mouse.dragging {
        let delta = mouse.get_drag_delta();

        if let Some(cam_3d) = camera_3d {
            // 3D mode: orbit camera based on mouse movement
            // Convert mouse delta to radians (sensitivity factor)
            let sensitivity = 0.005;
            let delta_yaw = delta.x * sensitivity;
            let delta_pitch = -delta.y * sensitivity; // Invert Y for intuitive control
            cam_3d.orbit(delta_yaw, delta_pitch);
        } else {
            // 2D mode: pan camera
            camera.pan(delta);
        }
    }
}

/// Handle mouse scroll wheel.
pub fn handle_mouse_scroll(
    delta: MouseScrollDelta,
    mouse: &MouseState,
    camera: &mut Camera,
    camera_3d: Option<&mut Camera3D>,
    disable_input: bool,
) {
    if disable_input {
        return;
    }

    // Calculate zoom factor from scroll delta
    let zoom_amount = match delta {
        MouseScrollDelta::LineDelta(_x, y) => y * 0.5,
        MouseScrollDelta::PixelDelta(pos) => (pos.y as f32) * 0.01,
    };

    // Zoom
    if zoom_amount.abs() > 0.001 {
        if let Some(cam_3d) = camera_3d {
            // 3D mode: zoom by adjusting orbit distance
            // Positive scroll = zoom in (closer)
            let factor = if zoom_amount > 0.0 { 0.9 } else { 1.1 };
            cam_3d.zoom(factor);
        } else {
            // 2D mode: zoom toward mouse position
            camera.zoom_toward(mouse.position, zoom_amount);
        }
    }
}

/// Cycle camera focus to the next visible user.
///
/// Returns the new user index.
pub fn cycle_to_next_user(scene: &Scene, camera: &mut Camera, current_index: usize) -> usize {
    let user_count = scene.user_count();
    if user_count == 0 {
        return current_index;
    }

    // Get all user IDs
    let user_ids: Vec<_> = scene
        .users()
        .values()
        .map(rource_core::scene::User::id)
        .collect();
    if user_ids.is_empty() {
        return current_index;
    }

    // Move to next user
    let new_index = (current_index + 1) % user_ids.len();
    let user_id = user_ids[new_index];

    // Focus camera on this user
    if let Some(user) = scene.get_user(user_id) {
        camera.jump_to(user.position());
        eprintln!("Following user: {}", user.name());
    }

    new_index
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mouse_state_initial() {
        let mouse = MouseState::new();
        assert_eq!(mouse.position, Vec2::ZERO);
        assert!(!mouse.dragging);
        assert_eq!(mouse.last_position, Vec2::ZERO);
    }

    #[test]
    fn test_mouse_state_position() {
        let mut mouse = MouseState::new();
        mouse.set_position(100.0, 200.0);
        assert_eq!(mouse.position.x, 100.0);
        assert_eq!(mouse.position.y, 200.0);
    }

    #[test]
    fn test_mouse_state_drag() {
        let mut mouse = MouseState::new();
        mouse.set_position(100.0, 100.0);
        mouse.start_drag();
        assert!(mouse.dragging);

        mouse.set_position(150.0, 150.0);
        let delta = mouse.get_drag_delta();
        assert_eq!(delta.x, 50.0);
        assert_eq!(delta.y, 50.0);

        mouse.end_drag();
        assert!(!mouse.dragging);
    }

    #[test]
    fn test_file_action_conversion() {
        assert!(matches!(
            file_action_to_action_type(FileAction::Create),
            ActionType::Create
        ));
        assert!(matches!(
            file_action_to_action_type(FileAction::Modify),
            ActionType::Modify
        ));
        assert!(matches!(
            file_action_to_action_type(FileAction::Delete),
            ActionType::Delete
        ));
    }
}
