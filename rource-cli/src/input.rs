//! Input handling for the Rource CLI.
//!
//! This module provides keyboard and mouse input handling for the windowed
//! application mode. Input can be disabled via the `--disable-input` flag.

use rource_core::camera::{Camera, Camera3D};
use rource_core::entity::{DirId, FileId, UserId};
use rource_core::scene::{ActionType, EntityType, Scene};
use rource_math::Vec2;
use rource_vcs::FileAction;
use winit::event::{ElementState, KeyEvent, MouseButton, MouseScrollDelta};
use winit::keyboard::{Key, NamedKey};

use crate::app::PlaybackState;

/// The entity currently being dragged by the user.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DraggedEntity {
    /// Dragging a directory node.
    Directory(DirId),
    /// Dragging a file node.
    File(FileId),
    /// Dragging a user entity.
    User(UserId),
}

impl From<EntityType> for DraggedEntity {
    fn from(entity: EntityType) -> Self {
        match entity {
            EntityType::Directory(id) => Self::Directory(id),
            EntityType::File(id) => Self::File(id),
            EntityType::User(id) => Self::User(id),
        }
    }
}

/// Input state for mouse interactions.
#[derive(Debug, Default)]
pub struct MouseState {
    /// Current mouse position in screen coordinates.
    pub position: Vec2,

    /// Whether the mouse is currently being dragged (left button held).
    pub dragging: bool,

    /// Last mouse position when drag started or during drag.
    pub last_position: Vec2,

    /// Entity currently being dragged (if any).
    pub dragged_entity: Option<DraggedEntity>,

    /// World-space offset from entity center to mouse click point.
    /// This keeps the entity stable relative to where the user clicked.
    pub drag_offset: Vec2,

    /// Entity currently being hovered over (for visual feedback).
    pub hovered_entity: Option<EntityType>,
}

impl MouseState {
    /// Create a new mouse state at the origin.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            position: Vec2::ZERO,
            dragging: false,
            last_position: Vec2::ZERO,
            dragged_entity: None,
            drag_offset: Vec2::ZERO,
            hovered_entity: None,
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
        self.dragged_entity = None;
        self.drag_offset = Vec2::ZERO;
    }

    /// Get the drag delta since last update.
    pub fn get_drag_delta(&mut self) -> Vec2 {
        let delta = self.position - self.last_position;
        self.last_position = self.position;
        delta
    }

    /// Start dragging an entity.
    pub fn start_entity_drag(&mut self, entity: DraggedEntity, offset: Vec2) {
        self.dragging = true;
        self.last_position = self.position;
        self.dragged_entity = Some(entity);
        self.drag_offset = offset;
    }

    /// Returns true if currently dragging an entity (not camera).
    pub fn is_dragging_entity(&self) -> bool {
        self.dragging && self.dragged_entity.is_some()
    }

    /// Returns true if currently dragging the camera (not an entity).
    pub fn is_dragging_camera(&self) -> bool {
        self.dragging && self.dragged_entity.is_none()
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

/// Radius for hit-testing entities (in screen pixels).
const HIT_TEST_RADIUS: f32 = 20.0;

/// Handle mouse button press/release with entity drag support.
///
/// Returns the seek target commit index if timeline scrubbing occurred.
#[allow(clippy::too_many_arguments)]
pub fn handle_mouse_button(
    button: MouseButton,
    state: ElementState,
    mouse: &mut MouseState,
    scene: &mut Scene,
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

                // Convert screen position to world coordinates
                let world_pos = camera.screen_to_world(mouse.position);

                // Check for entity at click position (hit-test in world space)
                // Use a radius scaled by zoom for consistent hit-testing
                let hit_radius = HIT_TEST_RADIUS / camera.zoom();

                if let Some(entity) = find_entity_at_position(scene, world_pos, hit_radius, camera)
                {
                    // Get entity's current position for offset calculation
                    let entity_pos = get_entity_position(scene, &entity);
                    let offset = entity_pos - world_pos;

                    // Start entity drag
                    mouse.start_entity_drag(entity.into(), offset);

                    // Pin the entity so physics doesn't move it during drag
                    set_entity_pinned(scene, &entity, true);
                } else {
                    // No entity hit - start camera drag
                    mouse.start_drag();
                }
            }
            ElementState::Released => {
                // Entity remains pinned after release (user can unpin with right-click)
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
        MouseButton::Right => {
            // Right-click unpins entities
            if state == ElementState::Pressed {
                let world_pos = camera.screen_to_world(mouse.position);
                let hit_radius = HIT_TEST_RADIUS / camera.zoom();

                if let Some(entity) = find_entity_at_position(scene, world_pos, hit_radius, camera)
                {
                    // Unpin the entity so physics can move it again
                    set_entity_pinned(scene, &entity, false);
                }
            }
        }
        _ => {}
    }

    None
}

/// Handle mouse movement with entity drag support.
pub fn handle_mouse_move(
    x: f64,
    y: f64,
    mouse: &mut MouseState,
    scene: &mut Scene,
    camera: &mut Camera,
    camera_3d: Option<&mut Camera3D>,
    disable_input: bool,
) {
    mouse.set_position(x, y);

    if disable_input {
        return;
    }

    // Handle entity dragging
    if mouse.is_dragging_entity() {
        if let Some(dragged) = mouse.dragged_entity {
            // Convert screen position to world coordinates
            let world_pos = camera.screen_to_world(mouse.position);

            // Calculate new entity position (including offset for smooth drag)
            let new_pos = world_pos + mouse.drag_offset;

            // Update entity position
            match dragged {
                DraggedEntity::Directory(id) => {
                    if let Some(dir) = scene.directories_mut().get_mut(id) {
                        dir.set_position(new_pos);
                        dir.set_velocity(Vec2::ZERO);
                    }
                }
                DraggedEntity::File(id) => {
                    if let Some(file) = scene.get_file_mut(id) {
                        file.set_position(new_pos);
                        file.set_target(new_pos);
                    }
                }
                DraggedEntity::User(id) => {
                    if let Some(user) = scene.get_user_mut(id) {
                        user.set_position(new_pos);
                        user.set_velocity(Vec2::ZERO);
                    }
                }
            }
        }
        // Update last position to track movement
        mouse.last_position = mouse.position;
        return;
    }

    // Handle camera dragging
    if mouse.is_dragging_camera() {
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

// ============================================================================
// Entity Hit-Testing and Manipulation Helpers
// ============================================================================

/// Find the nearest entity at the given world position within the specified radius.
///
/// Returns the closest entity that is within the hit radius, prioritizing:
/// 1. Users (most interactive)
/// 2. Files
/// 3. Directories
fn find_entity_at_position(
    scene: &Scene,
    world_pos: Vec2,
    hit_radius: f32,
    camera: &Camera,
) -> Option<EntityType> {
    // Query entities in a circle around the click position
    let entities = scene.query_entities_circle(world_pos, hit_radius);

    if entities.is_empty() {
        return None;
    }

    // Find the closest entity, prioritizing by type
    let mut best: Option<(EntityType, f32)> = None;

    for entity in entities {
        let entity_pos = get_entity_position(scene, &entity);
        let distance = (entity_pos - world_pos).length();

        // Check if entity is actually within its visual radius
        let visual_radius = get_entity_radius(scene, &entity) * camera.zoom();

        // Priority: Users > Files > Directories (lower = higher priority)
        let priority = match entity {
            EntityType::User(_) => 0,
            EntityType::File(_) => 1,
            EntityType::Directory(_) => 2,
        };

        // Consider this entity if it's within hit radius
        let in_range = distance <= hit_radius.max(visual_radius / camera.zoom());

        if in_range {
            if let Some((_, best_dist)) = best {
                // Prefer closer entities, or same distance with higher priority
                if distance < best_dist * 0.8
                    || (distance < best_dist * 1.2
                        && priority
                            < match best.unwrap().0 {
                                EntityType::User(_) => 0,
                                EntityType::File(_) => 1,
                                EntityType::Directory(_) => 2,
                            })
                {
                    best = Some((entity, distance));
                }
            } else {
                best = Some((entity, distance));
            }
        }
    }

    best.map(|(entity, _)| entity)
}

/// Get the current position of an entity.
fn get_entity_position(scene: &Scene, entity: &EntityType) -> Vec2 {
    match entity {
        EntityType::Directory(id) => scene
            .directories()
            .get(*id)
            .map(|d| d.position())
            .unwrap_or(Vec2::ZERO),
        EntityType::File(id) => scene
            .get_file(*id)
            .map(|f| f.position())
            .unwrap_or(Vec2::ZERO),
        EntityType::User(id) => scene
            .get_user(*id)
            .map(|u| u.position())
            .unwrap_or(Vec2::ZERO),
    }
}

/// Get the visual radius of an entity.
fn get_entity_radius(scene: &Scene, entity: &EntityType) -> f32 {
    match entity {
        EntityType::Directory(id) => scene
            .directories()
            .get(*id)
            .map(|d| d.radius())
            .unwrap_or(10.0),
        EntityType::File(id) => scene.get_file(*id).map(|f| f.radius()).unwrap_or(5.0),
        EntityType::User(id) => scene.get_user(*id).map(|u| u.radius()).unwrap_or(15.0),
    }
}

/// Set the pinned state of an entity.
fn set_entity_pinned(scene: &mut Scene, entity: &EntityType, pinned: bool) {
    match entity {
        EntityType::Directory(id) => {
            if let Some(dir) = scene.directories_mut().get_mut(*id) {
                dir.set_pinned(pinned);
            }
        }
        EntityType::File(id) => {
            if let Some(file) = scene.get_file_mut(*id) {
                file.set_pinned(pinned);
            }
        }
        EntityType::User(id) => {
            if let Some(user) = scene.get_user_mut(*id) {
                user.set_pinned(pinned);
            }
        }
    }
}

/// Update the hovered entity based on current mouse position.
/// This is called each frame for visual feedback.
pub fn update_hover_state(mouse: &mut MouseState, scene: &mut Scene, camera: &Camera) {
    // Clear previous hover state
    if let Some(prev_entity) = mouse.hovered_entity.take() {
        set_entity_highlighted(scene, &prev_entity, false);
    }

    // Don't update hover while dragging
    if mouse.dragging {
        return;
    }

    // Convert screen position to world coordinates
    let world_pos = camera.screen_to_world(mouse.position);
    let hit_radius = HIT_TEST_RADIUS / camera.zoom();

    // Find entity under cursor
    if let Some(entity) = find_entity_at_position(scene, world_pos, hit_radius, camera) {
        set_entity_highlighted(scene, &entity, true);
        mouse.hovered_entity = Some(entity);
    }
}

/// Set the highlighted state of an entity.
fn set_entity_highlighted(scene: &mut Scene, entity: &EntityType, highlighted: bool) {
    match entity {
        EntityType::Directory(id) => {
            if let Some(dir) = scene.directories_mut().get_mut(*id) {
                dir.set_highlighted(highlighted);
            }
        }
        EntityType::File(id) => {
            if let Some(file) = scene.get_file_mut(*id) {
                file.set_highlighted(highlighted);
            }
        }
        EntityType::User(id) => {
            if let Some(user) = scene.get_user_mut(*id) {
                user.set_highlighted(highlighted);
            }
        }
    }
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
