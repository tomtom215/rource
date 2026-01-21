//! Scene graph for the visualization.
//!
//! The scene contains all visual entities (directories, files, users, actions)
//! and manages their relationships and updates.

pub mod action;
pub mod dir_node;
pub mod file;
pub mod tree;
pub mod user;

use std::collections::HashMap;
use std::path::Path;

use rource_math::{Bounds, Vec2};

pub use action::{Action, ActionType};
pub use file::FileNode;
pub use tree::{DirNode, DirTree};
pub use user::User;

use crate::entity::{ActionId, DirId, FileId, IdAllocator, UserId};
use crate::physics::QuadTree;

/// Default bounds for the scene.
pub const DEFAULT_SCENE_SIZE: f32 = 10000.0;

// ============================================================================
// Force-directed layout constants
// ============================================================================

/// Repulsion constant between directory nodes.
/// Higher values push sibling directories further apart.
const FORCE_REPULSION: f32 = 800.0;

/// Attraction constant to parent directory.
/// Higher values pull children closer to their parents.
const FORCE_ATTRACTION: f32 = 0.03;

/// Velocity damping factor (0.0-1.0).
/// Applied each frame to prevent oscillation.
const FORCE_DAMPING: f32 = 0.85;

/// Maximum velocity to prevent instability.
const FORCE_MAX_VELOCITY: f32 = 300.0;

/// Squared maximum velocity for optimized comparisons (avoids sqrt).
const FORCE_MAX_VELOCITY_SQ: f32 = FORCE_MAX_VELOCITY * FORCE_MAX_VELOCITY;

/// Minimum distance for force calculation to prevent extreme forces.
const FORCE_MIN_DISTANCE: f32 = 5.0;

/// Squared minimum distance for optimized comparisons (avoids sqrt).
const FORCE_MIN_DISTANCE_SQ: f32 = FORCE_MIN_DISTANCE * FORCE_MIN_DISTANCE;

/// How often to refresh extension stats cache (in frames).
/// At 60fps, 30 frames = 0.5 seconds - acceptable for legend updates.
const STATS_CACHE_INTERVAL: u32 = 30;

/// Directory data for force-directed layout calculation.
type DirForceData = (DirId, Vec2, u32, Option<DirId>, Option<Vec2>, f32);

/// Entity type for spatial indexing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EntityType {
    /// A directory node.
    Directory(crate::entity::DirId),
    /// A file node.
    File(FileId),
    /// A user.
    User(UserId),
}

/// The main scene graph containing all entities.
///
/// The scene is the central data structure that manages:
/// - Directory tree structure
/// - File entities
/// - User entities
/// - Action animations
/// - Spatial indexing for efficient queries
#[derive(Debug)]
pub struct Scene {
    /// The directory tree.
    directories: DirTree,

    /// All files by ID.
    files: HashMap<FileId, FileNode>,

    /// File ID lookup by path.
    file_by_path: HashMap<std::path::PathBuf, FileId>,

    /// All users by ID.
    users: HashMap<UserId, User>,

    /// User ID lookup by name.
    user_by_name: HashMap<String, UserId>,

    /// Active actions.
    actions: Vec<Action>,

    /// ID allocator for files.
    file_id_allocator: IdAllocator,

    /// ID allocator for users.
    user_id_allocator: IdAllocator,

    /// ID allocator for actions.
    action_id_allocator: IdAllocator,

    /// Spatial index for entities.
    spatial: QuadTree<EntityType>,

    /// Current simulation time.
    time: f32,

    /// Scene bounds.
    bounds: Bounds,

    /// Update counter for throttling spatial index rebuilds.
    update_count: u32,

    /// Cached entity bounds (incrementally updated).
    cached_entity_bounds: Option<Bounds>,

    /// Whether entity bounds need recalculation.
    bounds_dirty: bool,

    /// Whether the radial layout needs recomputation.
    layout_dirty: bool,

    // ========================================================================
    // Reusable buffers (performance optimization to avoid per-frame allocations)
    // ========================================================================
    /// Reusable buffer for completed action tracking during update.
    /// Cleared and reused each frame to avoid allocation overhead.
    completed_actions_buffer: Vec<(ActionId, UserId)>,

    /// Reusable buffer for files marked for removal during update.
    /// Cleared and reused each frame to avoid allocation overhead.
    files_to_remove_buffer: Vec<FileId>,

    /// Reusable buffer for force-directed layout forces.
    /// Cleared and reused each frame to avoid `HashMap` allocation overhead.
    forces_buffer: HashMap<DirId, Vec2>,

    /// Reusable buffer for directory data in force calculations.
    /// Cleared and reused each frame to avoid Vec allocation overhead.
    dir_data_buffer: Vec<DirForceData>,

    // ========================================================================
    // Cached statistics (performance optimization to avoid per-frame recomputation)
    // ========================================================================
    /// Cached file extension statistics for legend rendering.
    /// Invalidated when files are added/removed or every `STATS_CACHE_INTERVAL` frames.
    extension_stats_cache: Vec<(String, usize)>,

    /// Whether extension stats cache needs refresh.
    extension_stats_dirty: bool,

    /// Frame counter for throttling stats refresh.
    stats_cache_frame: u32,
}

impl Scene {
    /// Creates a new empty scene.
    #[must_use]
    pub fn new() -> Self {
        let half_size = DEFAULT_SCENE_SIZE / 2.0;
        let bounds = Bounds::new(
            Vec2::new(-half_size, -half_size),
            Vec2::new(half_size, half_size),
        );

        Self {
            directories: DirTree::new(),
            files: HashMap::new(),
            file_by_path: HashMap::new(),
            users: HashMap::new(),
            user_by_name: HashMap::new(),
            actions: Vec::new(),
            file_id_allocator: IdAllocator::new(),
            user_id_allocator: IdAllocator::new(),
            action_id_allocator: IdAllocator::new(),
            spatial: QuadTree::new(bounds, 16, 8),
            time: 0.0,
            bounds,
            update_count: 0,
            cached_entity_bounds: None,
            bounds_dirty: true,
            layout_dirty: true,
            // Pre-allocate reusable buffers with reasonable initial capacity
            completed_actions_buffer: Vec::with_capacity(64),
            files_to_remove_buffer: Vec::with_capacity(32),
            forces_buffer: HashMap::with_capacity(128),
            dir_data_buffer: Vec::with_capacity(128),
            // Initialize stats cache as empty (will be populated on first request)
            extension_stats_cache: Vec::new(),
            extension_stats_dirty: true,
            stats_cache_frame: 0,
        }
    }

    /// Returns the directory tree.
    #[inline]
    #[must_use]
    pub fn directories(&self) -> &DirTree {
        &self.directories
    }

    /// Returns a mutable reference to the directory tree.
    #[inline]
    pub fn directories_mut(&mut self) -> &mut DirTree {
        &mut self.directories
    }

    /// Returns all files.
    #[inline]
    #[must_use]
    pub fn files(&self) -> &HashMap<FileId, FileNode> {
        &self.files
    }

    /// Returns a file by ID.
    #[must_use]
    pub fn get_file(&self, id: FileId) -> Option<&FileNode> {
        self.files.get(&id)
    }

    /// Returns a mutable file by ID.
    pub fn get_file_mut(&mut self, id: FileId) -> Option<&mut FileNode> {
        self.files.get_mut(&id)
    }

    /// Returns a file by path.
    #[must_use]
    pub fn get_file_by_path(&self, path: &Path) -> Option<&FileNode> {
        self.file_by_path
            .get(path)
            .and_then(|id| self.files.get(id))
    }

    /// Returns all users.
    #[inline]
    #[must_use]
    pub fn users(&self) -> &HashMap<UserId, User> {
        &self.users
    }

    /// Returns a user by ID.
    #[must_use]
    pub fn get_user(&self, id: UserId) -> Option<&User> {
        self.users.get(&id)
    }

    /// Returns a mutable user by ID.
    pub fn get_user_mut(&mut self, id: UserId) -> Option<&mut User> {
        self.users.get_mut(&id)
    }

    /// Returns a user by name.
    #[must_use]
    pub fn get_user_by_name(&self, name: &str) -> Option<&User> {
        self.user_by_name
            .get(name)
            .and_then(|id| self.users.get(id))
    }

    /// Returns active actions.
    #[inline]
    #[must_use]
    pub fn actions(&self) -> &[Action] {
        &self.actions
    }

    /// Returns the current simulation time.
    #[inline]
    #[must_use]
    pub const fn time(&self) -> f32 {
        self.time
    }

    /// Returns the scene bounds (initial allocation bounds, not entity bounds).
    ///
    /// Note: This returns the quadtree/scene allocation bounds, not the
    /// actual bounding box of entities. For entity bounds, use
    /// [`compute_entity_bounds()`](Self::compute_entity_bounds).
    #[inline]
    #[must_use]
    pub fn bounds(&self) -> &Bounds {
        &self.bounds
    }

    /// Computes the actual bounding box of all entities in the scene.
    ///
    /// Returns `None` if there are no entities with positions.
    /// This is useful for camera fitting to actual content.
    ///
    /// Uses caching to avoid recomputing bounds every frame. The cache is
    /// invalidated when entities are added or removed, or when
    /// [`Self::invalidate_bounds_cache`] is called.
    #[must_use]
    pub fn compute_entity_bounds(&mut self) -> Option<Bounds> {
        // Return cached bounds if still valid
        if !self.bounds_dirty {
            if let Some(cached) = self.cached_entity_bounds {
                return Some(cached);
            }
        }

        // Recompute bounds
        let bounds = self.compute_entity_bounds_uncached();
        self.cached_entity_bounds = bounds;
        self.bounds_dirty = false;
        bounds
    }

    /// Computes entity bounds without using cache.
    ///
    /// This is useful when you need fresh bounds and don't want to update the cache.
    #[must_use]
    pub fn compute_entity_bounds_uncached(&self) -> Option<Bounds> {
        let mut bounds = Bounds::INVERTED;

        // Include file positions
        for file in self.files.values() {
            let pos = file.position();
            let radius = file.radius();
            bounds = bounds
                .include_point(pos - Vec2::splat(radius))
                .include_point(pos + Vec2::splat(radius));
        }

        // Include user positions
        for user in self.users.values() {
            let pos = user.position();
            let radius = user.radius();
            bounds = bounds
                .include_point(pos - Vec2::splat(radius))
                .include_point(pos + Vec2::splat(radius));
        }

        // Include directory positions
        for dir in self.directories.iter() {
            let pos = dir.position();
            let radius = dir.radius();
            bounds = bounds
                .include_point(pos - Vec2::splat(radius))
                .include_point(pos + Vec2::splat(radius));
        }

        // Return None if bounds are still inverted (no entities)
        if bounds.min.x > bounds.max.x || bounds.min.y > bounds.max.y {
            None
        } else {
            Some(bounds)
        }
    }

    /// Invalidates the cached entity bounds, forcing a recomputation on next access.
    #[inline]
    pub fn invalidate_bounds_cache(&mut self) {
        self.bounds_dirty = true;
    }

    /// Gets or creates a user with the given name.
    ///
    /// If a user with this name already exists, returns their ID.
    /// Otherwise, creates a new user.
    pub fn get_or_create_user(&mut self, name: &str) -> UserId {
        if let Some(&id) = self.user_by_name.get(name) {
            return id;
        }

        let raw_id = self.user_id_allocator.allocate();
        let id = UserId::new(raw_id.index(), raw_id.generation());
        let user = User::new(id, name);

        self.users.insert(id, user);
        self.user_by_name.insert(name.to_string(), id);

        // Invalidate bounds cache since we added a new entity
        self.bounds_dirty = true;

        id
    }

    /// Creates a file at the given path.
    ///
    /// Also creates any necessary parent directories.
    /// Returns the file ID, or None if a file already exists at this path.
    pub fn create_file(&mut self, path: &Path) -> Option<FileId> {
        // Check if file already exists
        if self.file_by_path.contains_key(path) {
            return None;
        }

        // Get or create parent directory
        let parent_path = path.parent().unwrap_or_else(|| Path::new(""));
        let dir_count_before = self.directories.len();
        let dir_id = self.directories.get_or_create_path(parent_path);

        // If new directories were created, mark layout for recomputation
        if self.directories.len() > dir_count_before {
            self.layout_dirty = true;
        }

        // Create file
        let raw_id = self.file_id_allocator.allocate();
        let id = FileId::new(raw_id.index(), raw_id.generation());
        let mut file = FileNode::new(id, path, dir_id);

        // Position file using radial layout around its parent directory
        if let Some(dir) = self.directories.get(dir_id) {
            // Calculate position within the directory's angular sector
            let file_count = dir.files().len();

            // Get the directory's angular sector
            let start_angle = dir.start_angle();
            let end_angle = dir.end_angle();
            let span = end_angle - start_angle;

            // Offset based on file name hash for sub-positioning within sector
            let name = file.name();
            let hash = name.bytes().fold(0u32, |acc, b| {
                acc.wrapping_mul(31).wrapping_add(u32::from(b))
            });

            // Position file at the outer edge of the directory's sector
            let radial_distance = dir.radial_distance() + dir.radius() * 1.5 + 20.0;

            // Distribute files across the angular sector
            let padding = span * 0.1;
            let usable_span = (span - padding * 2.0).max(0.05);
            let base_angle = if file_count == 0 {
                dir.center_angle()
            } else {
                // Spread files based on hash to avoid clustering
                let t = (hash % 1000) as f32 / 1000.0;
                start_angle + padding + t * usable_span
            };

            let pos = Vec2::new(
                base_angle.cos() * radial_distance,
                base_angle.sin() * radial_distance,
            );

            file.set_position(pos);
            file.set_target(pos);
        }

        // Add to directory
        if let Some(dir) = self.directories.get_mut(dir_id) {
            dir.add_file(id);
        }

        self.file_by_path.insert(path.to_path_buf(), id);
        self.files.insert(id, file);

        // Invalidate caches since we added a new entity
        self.bounds_dirty = true;
        self.extension_stats_dirty = true;

        Some(id)
    }

    /// Gets an existing file or creates a new one.
    pub fn get_or_create_file(&mut self, path: &Path) -> FileId {
        if let Some(&id) = self.file_by_path.get(path) {
            return id;
        }

        self.create_file(path)
            .expect("File creation should succeed for new path")
    }

    /// Spawns an action from a user to a file.
    ///
    /// Returns `Some(ActionId)` if the action was created, or `None` if
    /// the action cap was reached (see `MAX_ACTIONS`).
    pub fn spawn_action(
        &mut self,
        user_id: UserId,
        file_id: FileId,
        action_type: ActionType,
    ) -> Option<ActionId> {
        // Skip spawning if at capacity (prevents accumulation at fast playback)
        if self.actions.len() >= Self::MAX_ACTIONS {
            // Still update user target even if we skip the action
            if let Some(file) = self.files.get(&file_id) {
                if let Some(user) = self.users.get_mut(&user_id) {
                    user.set_target(file.position());
                }
            }
            return None;
        }

        let raw_id = self.action_id_allocator.allocate();
        let id = ActionId::new(raw_id.index(), raw_id.generation());

        let action = Action::new(id, user_id, file_id, action_type);
        self.actions.push(action);

        // Add action to user's active actions
        if let Some(user) = self.users.get_mut(&user_id) {
            user.add_action(id);
        }

        // Set user's target to file position
        // If user is at origin (new user), teleport them near the file first
        if let Some(file) = self.files.get(&file_id) {
            if let Some(user) = self.users.get_mut(&user_id) {
                let file_pos = file.position();

                // If user is still at origin (default position), place them near the file
                if user.position().length() < 1.0 {
                    // Position user slightly offset from file
                    let offset = Vec2::new(-50.0, -30.0);
                    user.set_position(file_pos + offset);
                }

                user.set_target(file_pos);
            }
        }

        Some(id)
    }

    /// Applies a VCS commit to the scene.
    ///
    /// This creates/modifies/deletes files and spawns appropriate actions.
    pub fn apply_commit(&mut self, author: &str, files: &[(std::path::PathBuf, ActionType)]) {
        let user_id = self.get_or_create_user(author);

        for (path, action_type) in files {
            match action_type {
                ActionType::Create => {
                    let file_id = self.get_or_create_file(path);
                    self.spawn_action(user_id, file_id, ActionType::Create);

                    // Touch the file with create color
                    if let Some(file) = self.files.get_mut(&file_id) {
                        file.touch(ActionType::Create.color());
                    }
                }
                ActionType::Modify => {
                    if let Some(&file_id) = self.file_by_path.get(path) {
                        self.spawn_action(user_id, file_id, ActionType::Modify);

                        // Touch the file with modify color
                        if let Some(file) = self.files.get_mut(&file_id) {
                            file.touch(ActionType::Modify.color());
                        }
                    } else {
                        // File doesn't exist yet, treat as create
                        let file_id = self.get_or_create_file(path);
                        self.spawn_action(user_id, file_id, ActionType::Create);

                        if let Some(file) = self.files.get_mut(&file_id) {
                            file.touch(ActionType::Create.color());
                        }
                    }
                }
                ActionType::Delete => {
                    if let Some(&file_id) = self.file_by_path.get(path) {
                        self.spawn_action(user_id, file_id, ActionType::Delete);

                        // Mark file for removal
                        if let Some(file) = self.files.get_mut(&file_id) {
                            file.touch(ActionType::Delete.color());
                            file.mark_for_removal();
                        }
                    }
                }
            }
        }
    }

    /// How often to rebuild the spatial index (every N updates).
    const SPATIAL_REBUILD_INTERVAL: u32 = 5;

    /// Maximum number of concurrent actions (prevents accumulation at fast playback).
    /// At 60fps with `ACTION_SPEED=2.0`, each action takes ~30 frames to complete.
    /// With thousands of commits per second at fast playback, actions accumulate
    /// faster than they expire. This cap ensures smooth rendering performance.
    const MAX_ACTIONS: usize = 5000;

    /// Updates the scene by the given time delta.
    ///
    /// This updates:
    /// - Actions (progress animation)
    /// - Users (movement, fade)
    /// - Files (fade, touch effects)
    /// - Directory physics
    /// - Spatial index (throttled for performance)
    pub fn update(&mut self, dt: f32) {
        self.time += dt;
        self.update_count = self.update_count.wrapping_add(1);

        // Update actions and collect completed ones (reusing buffer)
        self.completed_actions_buffer.clear();
        for action in &mut self.actions {
            if !action.update(dt) {
                self.completed_actions_buffer
                    .push((action.id(), action.user()));
            }
        }

        // Remove completed actions and update users
        // Note: We iterate by index to work around borrow checker with the buffer
        for i in 0..self.completed_actions_buffer.len() {
            let (action_id, user_id) = self.completed_actions_buffer[i];
            if let Some(user) = self.users.get_mut(&user_id) {
                user.remove_action(action_id);
            }
        }
        self.actions.retain(|a| !a.is_complete());

        // Update users
        for user in self.users.values_mut() {
            user.update(dt);
        }

        // Update files and collect ones to remove (reusing buffer)
        self.files_to_remove_buffer.clear();
        for (id, file) in &mut self.files {
            file.update(dt);
            if file.should_remove() {
                self.files_to_remove_buffer.push(*id);
            }
        }

        // Remove deleted files
        let files_removed = !self.files_to_remove_buffer.is_empty();
        for i in 0..self.files_to_remove_buffer.len() {
            let id = self.files_to_remove_buffer[i];
            if let Some(file) = self.files.remove(&id) {
                self.file_by_path.remove(file.path());

                // Remove from parent directory
                let dir_id = file.directory();
                if let Some(dir) = self.directories.get_mut(dir_id) {
                    dir.remove_file(id);
                }

                // Free the ID
                self.file_id_allocator
                    .free(crate::entity::RawEntityId::new(id.index(), id.generation()));
            }
        }

        // Update radial layout if tree structure changed
        if self.layout_dirty {
            self.directories.compute_radial_layout();
            self.layout_dirty = false;

            // Update file positions to match new directory positions
            self.update_file_positions_for_layout();
        }

        // Update parent positions for force calculation
        self.directories.update_parent_positions();

        // Apply force-directed layout to directories
        self.apply_force_directed_layout(dt);

        // Invalidate bounds cache since entities may have moved
        // (only every N frames to avoid constant recomputation)
        if self.update_count % Self::SPATIAL_REBUILD_INTERVAL == 0 || files_removed {
            self.bounds_dirty = true;
        }

        // Invalidate extension stats cache when files are removed
        if files_removed {
            self.extension_stats_dirty = true;
        }

        // Rebuild spatial index periodically (throttled for performance)
        // This is O(n) so we don't want to do it every frame
        if self.update_count % Self::SPATIAL_REBUILD_INTERVAL == 0 || files_removed {
            self.rebuild_spatial_index();
        }
    }

    /// Updates file positions to match their directory's new radial position.
    ///
    /// Called after recomputing the radial layout to ensure files move with
    /// their parent directories.
    fn update_file_positions_for_layout(&mut self) {
        // Collect directory info: (dir_id, position, start_angle, end_angle, radial_distance, radius)
        let dir_info: HashMap<_, _> = self
            .directories
            .iter()
            .map(|d| {
                (
                    d.id(),
                    (
                        d.position(),
                        d.start_angle(),
                        d.end_angle(),
                        d.radial_distance(),
                        d.radius(),
                    ),
                )
            })
            .collect();

        // Update each file's position based on its directory
        for file in self.files.values_mut() {
            // Skip pinned files (e.g., being dragged by user)
            if file.is_pinned() {
                continue;
            }

            let dir_id = file.directory();
            if let Some(&(_dir_pos, start_angle, end_angle, radial_distance, radius)) =
                dir_info.get(&dir_id)
            {
                let span = end_angle - start_angle;

                // Use file name hash for deterministic positioning within sector
                let name = file.name();
                let hash = name.bytes().fold(0u32, |acc, b| {
                    acc.wrapping_mul(31).wrapping_add(u32::from(b))
                });

                // Position file at outer edge of directory's sector
                let file_distance = radial_distance + radius * 1.5 + 20.0;

                // Spread files within the angular sector
                let padding = span * 0.1;
                let usable_span = (span - padding * 2.0).max(0.05);
                let t = (hash % 1000) as f32 / 1000.0;
                let angle = start_angle + padding + t * usable_span;

                let new_pos = Vec2::new(angle.cos() * file_distance, angle.sin() * file_distance);

                file.set_target(new_pos);
                // Optionally, snap position immediately for layout changes
                file.set_position(new_pos);
            }
        }
    }

    /// Applies force-directed layout to directory nodes.
    ///
    /// This simulates physical forces between directories to create a natural,
    /// organic-looking tree layout:
    /// - **Repulsion**: Sibling directories and nearby nodes push each other apart
    /// - **Attraction**: Child directories are pulled toward their parents
    /// - **Damping**: Friction-like force that stabilizes the system
    fn apply_force_directed_layout(&mut self, dt: f32) {
        // Collect directory data for force calculation (reusing buffer)
        self.dir_data_buffer.clear();
        for d in self.directories.iter() {
            self.dir_data_buffer.push((
                d.id(),
                d.position(),
                d.depth(),
                d.parent(),
                d.parent_position(),
                d.target_distance(),
            ));
        }

        // Calculate forces for each directory (reusing buffer)
        self.forces_buffer.clear();

        // Calculate repulsion forces between related directories (O(n²) but n is typically small)
        let dir_count = self.dir_data_buffer.len();
        for i in 0..dir_count {
            let (id_i, pos_i, depth_i, parent_i, _, _) = self.dir_data_buffer[i];
            for j in (i + 1)..dir_count {
                let (id_j, pos_j, depth_j, parent_j, _, _) = self.dir_data_buffer[j];

                // Repel if:
                // 1. Siblings (same parent)
                // 2. Close in depth (within 1 level)
                let are_siblings = parent_i == parent_j && parent_i.is_some();
                let close_depth = depth_i.abs_diff(depth_j) <= 1;

                if !are_siblings && !close_depth {
                    continue;
                }

                let delta = pos_j - pos_i;
                let distance_sq = delta.length_squared();

                // Guard against zero-length delta (check squared distance)
                if distance_sq < 0.001 {
                    // Push apart randomly based on indices
                    let offset = Vec2::new((i as f32).sin() * 5.0, (j as f32).cos() * 5.0);
                    *self.forces_buffer.entry(id_i).or_insert(Vec2::ZERO) -= offset;
                    *self.forces_buffer.entry(id_j).or_insert(Vec2::ZERO) += offset;
                    continue;
                }

                // Use squared distance for inverse-square repulsion: F = k / d²
                // Clamp to minimum squared distance to prevent extreme forces
                let clamped_dist_sq = distance_sq.max(FORCE_MIN_DISTANCE_SQ);
                let force_magnitude = FORCE_REPULSION / clamped_dist_sq;

                // Compute direction only when needed (requires sqrt via length)
                let distance = distance_sq.sqrt();
                let direction = delta / distance; // Equivalent to delta.normalized()
                let force = direction * force_magnitude;

                // Apply equal and opposite forces
                *self.forces_buffer.entry(id_i).or_insert(Vec2::ZERO) -= force;
                *self.forces_buffer.entry(id_j).or_insert(Vec2::ZERO) += force;
            }
        }

        // Calculate attraction forces to parents
        for i in 0..dir_count {
            let (id, pos, _depth, _parent_id, parent_pos, target_dist) = self.dir_data_buffer[i];
            if let Some(parent_pos) = parent_pos {
                let delta = parent_pos - pos;
                let distance_sq = delta.length_squared();
                let target_dist_sq = target_dist * target_dist;

                // Only attract if beyond target distance (compare squared to avoid sqrt)
                if distance_sq > target_dist_sq && distance_sq > 0.001 {
                    // Now compute actual distance since we need it for the force
                    let distance = distance_sq.sqrt();
                    let excess = distance - target_dist;
                    let direction = delta / distance; // Equivalent to delta.normalized()
                    let force = direction * excess * FORCE_ATTRACTION;
                    *self.forces_buffer.entry(id).or_insert(Vec2::ZERO) += force;
                }
            }
        }

        // Apply forces to directories
        for dir in self.directories.iter_mut() {
            // Skip root (anchor it in place)
            if dir.is_root() {
                continue;
            }

            if let Some(&force) = self.forces_buffer.get(&dir.id()) {
                // Apply force as acceleration (assuming unit mass)
                dir.add_velocity(force * dt);

                // Clamp velocity to prevent instability (use squared comparison)
                let vel = dir.velocity();
                let speed_sq = vel.length_squared();
                if speed_sq > FORCE_MAX_VELOCITY_SQ {
                    // Only compute sqrt when actually needed for clamping
                    let speed = speed_sq.sqrt();
                    dir.set_velocity(vel * (FORCE_MAX_VELOCITY / speed));
                }

                // Apply damping
                dir.set_velocity(dir.velocity() * FORCE_DAMPING);

                // Integrate position
                let new_pos = dir.position() + dir.velocity() * dt;
                dir.set_position(new_pos);
            } else {
                // No force but still apply damping and integration for existing velocity
                dir.update_physics(dt, FORCE_DAMPING);
            }
        }
    }

    /// Rebuilds the spatial index with current entity positions.
    pub fn rebuild_spatial_index(&mut self) {
        self.spatial.clear();

        // Add directories
        for dir in self.directories.iter() {
            self.spatial
                .insert(dir.position(), EntityType::Directory(dir.id()));
        }

        // Add files
        for (id, file) in &self.files {
            self.spatial.insert(file.position(), EntityType::File(*id));
        }

        // Add users
        for (id, user) in &self.users {
            self.spatial.insert(user.position(), EntityType::User(*id));
        }
    }

    /// Queries entities within the given bounds.
    #[must_use]
    pub fn query_entities(&self, bounds: &Bounds) -> Vec<EntityType> {
        self.spatial.query(bounds).into_iter().copied().collect()
    }

    /// Queries entities within a circular region.
    #[must_use]
    pub fn query_entities_circle(&self, center: Vec2, radius: f32) -> Vec<EntityType> {
        self.spatial
            .query_circle_with_pos(center, radius)
            .into_iter()
            .map(|(_, &entity)| entity)
            .collect()
    }

    /// Finds the nearest entity to the given position.
    #[must_use]
    pub fn nearest_entity(&self, position: Vec2) -> Option<EntityType> {
        self.spatial.nearest(position).map(|(_, &entity)| entity)
    }

    /// Returns IDs of files visible within the given bounds.
    ///
    /// This is useful for frustum culling - only render files that are
    /// within the camera's visible bounds. The bounds should typically
    /// include some margin for entity radii.
    #[must_use]
    pub fn visible_file_ids(&self, bounds: &Bounds) -> Vec<FileId> {
        self.spatial
            .query(bounds)
            .into_iter()
            .filter_map(|entity| match entity {
                EntityType::File(id) => Some(*id),
                _ => None,
            })
            .collect()
    }

    /// Returns IDs of users visible within the given bounds.
    ///
    /// This is useful for frustum culling - only render users that are
    /// within the camera's visible bounds.
    #[must_use]
    pub fn visible_user_ids(&self, bounds: &Bounds) -> Vec<UserId> {
        self.spatial
            .query(bounds)
            .into_iter()
            .filter_map(|entity| match entity {
                EntityType::User(id) => Some(*id),
                _ => None,
            })
            .collect()
    }

    /// Returns IDs of directories visible within the given bounds.
    ///
    /// This is useful for frustum culling - only render directories that are
    /// within the camera's visible bounds.
    #[must_use]
    pub fn visible_directory_ids(&self, bounds: &Bounds) -> Vec<crate::entity::DirId> {
        self.spatial
            .query(bounds)
            .into_iter()
            .filter_map(|entity| match entity {
                EntityType::Directory(id) => Some(*id),
                _ => None,
            })
            .collect()
    }

    /// Returns all entity types visible within the given bounds, grouped by type.
    ///
    /// This provides efficient frustum culling by using the spatial index
    /// to query only entities within the visible area.
    #[must_use]
    pub fn visible_entities(
        &self,
        bounds: &Bounds,
    ) -> (Vec<crate::entity::DirId>, Vec<FileId>, Vec<UserId>) {
        let mut dirs = Vec::new();
        let mut files = Vec::new();
        let mut users = Vec::new();

        for entity in self.spatial.query(bounds) {
            match entity {
                EntityType::Directory(id) => dirs.push(*id),
                EntityType::File(id) => files.push(*id),
                EntityType::User(id) => users.push(*id),
            }
        }

        (dirs, files, users)
    }

    /// Returns the expanded bounds for visibility queries.
    ///
    /// This adds a margin to account for entity radii and ensures
    /// entities at the edge of the screen are included.
    #[must_use]
    pub fn expand_bounds_for_visibility(bounds: &Bounds, margin: f32) -> Bounds {
        Bounds::new(
            bounds.min - Vec2::splat(margin),
            bounds.max + Vec2::splat(margin),
        )
    }

    /// Returns the number of files in the scene.
    #[must_use]
    pub fn file_count(&self) -> usize {
        self.files.len()
    }

    /// Returns the number of users in the scene.
    #[must_use]
    pub fn user_count(&self) -> usize {
        self.users.len()
    }

    /// Returns the number of directories in the scene.
    #[must_use]
    pub fn directory_count(&self) -> usize {
        self.directories.len()
    }

    /// Returns the number of active actions.
    #[must_use]
    pub fn action_count(&self) -> usize {
        self.actions.len()
    }

    /// Returns file extension statistics (extension -> count).
    ///
    /// Only includes extensions for files that are currently visible (alpha > 0.1).
    /// Uses caching to avoid recomputation every frame - cache is refreshed when:
    /// - Files are added or removed
    /// - Every `STATS_CACHE_INTERVAL` frames (to account for alpha changes)
    #[must_use]
    pub fn file_extension_stats(&mut self) -> &[(String, usize)] {
        // Check if cache needs refresh
        let needs_refresh = self.extension_stats_dirty
            || self.stats_cache_frame >= STATS_CACHE_INTERVAL
            || self.extension_stats_cache.is_empty();

        if needs_refresh {
            self.recompute_extension_stats();
            self.extension_stats_dirty = false;
            self.stats_cache_frame = 0;
        } else {
            self.stats_cache_frame += 1;
        }

        &self.extension_stats_cache
    }

    /// Recomputes extension statistics and updates the cache.
    fn recompute_extension_stats(&mut self) {
        use std::collections::HashMap;

        let mut stats: HashMap<String, usize> = HashMap::new();

        for file in self.files.values() {
            if file.alpha() < 0.1 {
                continue;
            }
            let ext = file
                .extension()
                .map_or_else(|| "other".to_string(), str::to_lowercase);
            *stats.entry(ext).or_insert(0) += 1;
        }

        // Sort by count descending, then by extension name
        self.extension_stats_cache.clear();
        self.extension_stats_cache.extend(stats);
        self.extension_stats_cache
            .sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    }

    /// Returns file extension statistics without updating the cache.
    ///
    /// This is useful when you need stats but don't want to mutate the scene.
    /// Note: This may return stale data if the cache hasn't been refreshed recently.
    #[must_use]
    pub fn file_extension_stats_cached(&self) -> &[(String, usize)] {
        &self.extension_stats_cache
    }

    /// Invalidates the extension stats cache, forcing a recomputation on next access.
    ///
    /// This is useful for testing or when you need fresh statistics immediately.
    #[inline]
    pub fn invalidate_extension_stats(&mut self) {
        self.extension_stats_dirty = true;
    }
}

impl Default for Scene {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scene_new() {
        let scene = Scene::new();

        assert_eq!(scene.file_count(), 0);
        assert_eq!(scene.user_count(), 0);
        assert_eq!(scene.directory_count(), 1); // Root
        assert_eq!(scene.action_count(), 0);
        assert_eq!(scene.time(), 0.0);
    }

    #[test]
    fn test_scene_get_or_create_user() {
        let mut scene = Scene::new();

        let id1 = scene.get_or_create_user("Alice");
        let id2 = scene.get_or_create_user("Bob");
        let id3 = scene.get_or_create_user("Alice"); // Existing

        assert_eq!(id1, id3);
        assert_ne!(id1, id2);
        assert_eq!(scene.user_count(), 2);
    }

    #[test]
    fn test_scene_create_file() {
        let mut scene = Scene::new();

        let id1 = scene.create_file(Path::new("src/main.rs"));
        let id2 = scene.create_file(Path::new("src/lib.rs"));
        let id3 = scene.create_file(Path::new("src/main.rs")); // Duplicate

        assert!(id1.is_some());
        assert!(id2.is_some());
        assert!(id3.is_none()); // Already exists

        assert_eq!(scene.file_count(), 2);
        assert!(scene.directory_count() >= 2); // Root + src
    }

    #[test]
    fn test_scene_get_file_by_path() {
        let mut scene = Scene::new();

        scene.create_file(Path::new("src/main.rs"));

        let file = scene.get_file_by_path(Path::new("src/main.rs"));
        assert!(file.is_some());
        assert_eq!(file.unwrap().name(), "main.rs");

        let not_found = scene.get_file_by_path(Path::new("nonexistent.rs"));
        assert!(not_found.is_none());
    }

    #[test]
    fn test_scene_spawn_action() {
        let mut scene = Scene::new();

        let user_id = scene.get_or_create_user("Alice");
        let file_id = scene.create_file(Path::new("test.rs")).unwrap();

        let action_id = scene
            .spawn_action(user_id, file_id, ActionType::Modify)
            .unwrap();

        assert_eq!(scene.action_count(), 1);

        let user = scene.get_user(user_id).unwrap();
        assert!(user.active_actions().contains(&action_id));
    }

    #[test]
    fn test_scene_apply_commit() {
        let mut scene = Scene::new();

        let files = vec![
            (std::path::PathBuf::from("src/new.rs"), ActionType::Create),
            (std::path::PathBuf::from("src/mod.rs"), ActionType::Create),
        ];

        scene.apply_commit("Alice", &files);

        assert_eq!(scene.file_count(), 2);
        assert_eq!(scene.user_count(), 1);
        assert_eq!(scene.action_count(), 2);
    }

    #[test]
    fn test_scene_apply_commit_modify() {
        let mut scene = Scene::new();

        // First create a file
        scene.create_file(Path::new("src/lib.rs"));

        let files = vec![(std::path::PathBuf::from("src/lib.rs"), ActionType::Modify)];

        scene.apply_commit("Bob", &files);

        assert_eq!(scene.file_count(), 1);
        assert_eq!(scene.action_count(), 1);

        // Check the action type
        assert_eq!(scene.actions()[0].action_type(), ActionType::Modify);
    }

    #[test]
    fn test_scene_apply_commit_delete() {
        let mut scene = Scene::new();

        // First create a file
        scene.create_file(Path::new("old.rs"));

        let files = vec![(std::path::PathBuf::from("old.rs"), ActionType::Delete)];

        scene.apply_commit("Charlie", &files);

        // File still exists but is marked for removal
        let file = scene.get_file_by_path(Path::new("old.rs")).unwrap();
        assert!(file.is_removing());
    }

    #[test]
    fn test_scene_update() {
        let mut scene = Scene::new();

        // Create a file and action
        let file_id = scene.create_file(Path::new("test.rs")).unwrap();
        let user_id = scene.get_or_create_user("Test");
        let _ = scene.spawn_action(user_id, file_id, ActionType::Create);

        assert_eq!(scene.action_count(), 1);

        // Update until action completes
        for _ in 0..10 {
            scene.update(0.5);
        }

        // Action should be complete and removed
        assert_eq!(scene.action_count(), 0);

        // User should no longer have active actions
        let user = scene.get_user(user_id).unwrap();
        assert!(user.active_actions().is_empty());
    }

    #[test]
    fn test_scene_update_removes_deleted_files() {
        let mut scene = Scene::new();

        // Create and immediately delete a file
        let file_id = scene.create_file(Path::new("temp.rs")).unwrap();
        scene.get_file_mut(file_id).unwrap().mark_for_removal();

        assert_eq!(scene.file_count(), 1);

        // Update until file fades out
        for _ in 0..20 {
            scene.update(0.5);
        }

        // File should be removed
        assert_eq!(scene.file_count(), 0);
        assert!(scene.get_file_by_path(Path::new("temp.rs")).is_none());
    }

    #[test]
    fn test_scene_query_entities() {
        let mut scene = Scene::new();

        scene.create_file(Path::new("a.rs"));
        scene.create_file(Path::new("b.rs"));

        scene.rebuild_spatial_index();

        let entities = scene.query_entities(&scene.bounds().clone());
        assert!(!entities.is_empty());
    }

    #[test]
    fn test_scene_get_user_by_name() {
        let mut scene = Scene::new();

        scene.get_or_create_user("Alice");

        let user = scene.get_user_by_name("Alice");
        assert!(user.is_some());
        assert_eq!(user.unwrap().name(), "Alice");

        let not_found = scene.get_user_by_name("Unknown");
        assert!(not_found.is_none());
    }

    #[test]
    fn test_scene_visible_file_ids() {
        let mut scene = Scene::new();

        // Create files at known positions
        let file_id = scene.create_file(Path::new("visible.rs")).unwrap();
        if let Some(file) = scene.get_file_mut(file_id) {
            file.set_position(Vec2::new(100.0, 100.0));
        }

        scene.rebuild_spatial_index();

        // Query bounds that include the file
        let bounds = Bounds::new(Vec2::new(0.0, 0.0), Vec2::new(200.0, 200.0));
        let visible = scene.visible_file_ids(&bounds);
        assert!(visible.contains(&file_id));

        // Query bounds that don't include the file
        let far_bounds = Bounds::new(Vec2::new(1000.0, 1000.0), Vec2::new(2000.0, 2000.0));
        let not_visible = scene.visible_file_ids(&far_bounds);
        assert!(!not_visible.contains(&file_id));
    }

    #[test]
    fn test_scene_visible_user_ids() {
        let mut scene = Scene::new();

        // Create user at a position
        let user_id = scene.get_or_create_user("Alice");
        if let Some(user) = scene.get_user_mut(user_id) {
            user.set_position(Vec2::new(50.0, 50.0));
        }

        scene.rebuild_spatial_index();

        // Query bounds that include the user
        let bounds = Bounds::new(Vec2::new(0.0, 0.0), Vec2::new(100.0, 100.0));
        let visible = scene.visible_user_ids(&bounds);
        assert!(visible.contains(&user_id));
    }

    #[test]
    fn test_scene_visible_directory_ids() {
        let mut scene = Scene::new();

        // Create a file which will create directory structure
        scene.create_file(Path::new("src/lib.rs"));

        scene.rebuild_spatial_index();

        // Query with full scene bounds should find directories
        let bounds = *scene.bounds();
        let visible = scene.visible_directory_ids(&bounds);
        assert!(!visible.is_empty());
    }

    #[test]
    fn test_scene_visible_entities() {
        let mut scene = Scene::new();

        // Create various entities
        scene.create_file(Path::new("test.rs"));
        scene.get_or_create_user("Bob");

        scene.rebuild_spatial_index();

        // Query all visible entities
        let bounds = *scene.bounds();
        let (dirs, files, users) = scene.visible_entities(&bounds);

        // Should find at least the root directory, one file, and one user
        assert!(!dirs.is_empty());
        assert!(!files.is_empty());
        assert!(!users.is_empty());
    }

    #[test]
    fn test_scene_expand_bounds_for_visibility() {
        let bounds = Bounds::new(Vec2::new(0.0, 0.0), Vec2::new(100.0, 100.0));
        let expanded = Scene::expand_bounds_for_visibility(&bounds, 10.0);

        assert_eq!(expanded.min, Vec2::new(-10.0, -10.0));
        assert_eq!(expanded.max, Vec2::new(110.0, 110.0));
    }

    // ========================================================================
    // Performance optimization tests
    // ========================================================================

    #[test]
    fn test_extension_stats_caching() {
        let mut scene = Scene::new();

        // Create files with different extensions
        scene.create_file(Path::new("src/main.rs"));
        scene.create_file(Path::new("src/lib.rs"));
        scene.create_file(Path::new("src/test.rs"));
        scene.create_file(Path::new("docs/readme.md"));

        // Warm up the files so they're visible (alpha > 0.1)
        for _ in 0..10 {
            scene.update(0.1);
        }

        // First call should compute stats
        let stats1: Vec<_> = scene.file_extension_stats().to_vec();
        assert!(!stats1.is_empty());

        // Find the rs count
        let rs_count = stats1.iter().find(|(ext, _)| ext == "rs").map(|(_, c)| *c);
        assert_eq!(rs_count, Some(3), "Should have 3 .rs files");

        // Second call should return cached result (same data)
        let stats2: Vec<_> = scene.file_extension_stats().to_vec();
        assert_eq!(stats1, stats2, "Cached result should match");

        // Invalidate and verify new computation
        scene.invalidate_extension_stats();
        let stats3: Vec<_> = scene.file_extension_stats().to_vec();
        assert_eq!(stats3, stats1, "Re-computed stats should match");
    }

    #[test]
    fn test_extension_stats_cache_invalidation_on_file_add() {
        let mut scene = Scene::new();

        scene.create_file(Path::new("test.rs"));
        for _ in 0..5 {
            scene.update(0.1);
        }

        let rs_count1 = scene
            .file_extension_stats()
            .iter()
            .find(|(ext, _)| ext == "rs")
            .map(|(_, c)| *c);

        // Add another file - should invalidate cache
        scene.create_file(Path::new("another.rs"));
        for _ in 0..5 {
            scene.update(0.1);
        }

        let rs_count2 = scene
            .file_extension_stats()
            .iter()
            .find(|(ext, _)| ext == "rs")
            .map(|(_, c)| *c);

        // Should have one more .rs file
        assert_eq!(
            rs_count2,
            rs_count1.map(|c| c + 1),
            "Adding file should update stats"
        );
    }

    #[test]
    fn test_reusable_buffers_dont_leak() {
        let mut scene = Scene::new();

        // Create some entities
        for i in 0..100 {
            scene.create_file(&Path::new(&format!("file_{i}.rs")));
        }
        scene.get_or_create_user("TestUser");

        // Run many update cycles
        for _ in 0..100 {
            scene.update(1.0 / 60.0);
        }

        // Buffers should be reused, not growing unbounded
        // The completed_actions_buffer capacity should be reasonable
        // (This is a sanity check - exact values depend on implementation)
        assert!(
            scene.completed_actions_buffer.capacity() < 1000,
            "Buffer should not grow unbounded"
        );
        assert!(
            scene.files_to_remove_buffer.capacity() < 1000,
            "Buffer should not grow unbounded"
        );
    }

    #[test]
    fn test_force_directed_layout_stability() {
        let mut scene = Scene::new();

        // Create a tree structure
        scene.create_file(Path::new("src/main.rs"));
        scene.create_file(Path::new("src/lib.rs"));
        scene.create_file(Path::new("src/utils/helpers.rs"));
        scene.create_file(Path::new("tests/test_main.rs"));

        // Let physics settle
        for _ in 0..100 {
            scene.update(1.0 / 60.0);
        }

        // Record positions
        let mut positions: Vec<_> = scene.directories.iter().map(|d| d.position()).collect();

        // Run more updates
        for _ in 0..50 {
            scene.update(1.0 / 60.0);
        }

        // Positions should be relatively stable (not moving much)
        let new_positions: Vec<_> = scene.directories.iter().map(|d| d.position()).collect();

        for (old, new) in positions.iter_mut().zip(new_positions.iter()) {
            let delta = (*new - *old).length();
            assert!(
                delta < 10.0,
                "Directory positions should stabilize, but moved {delta}"
            );
        }
    }
}
