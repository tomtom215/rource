//! Directory tree structure for the visualization.
//!
//! The directory tree is the backbone of the scene graph, representing
//! the hierarchical file structure of the repository being visualized.

use std::path::{Path, PathBuf};

use rource_math::Vec2;

use crate::entity::{DirId, FileId, Generation};

/// Minimum visual radius for directory nodes.
pub const MIN_DIR_RADIUS: f32 = 5.0;

/// Default radius for new directory nodes.
pub const DEFAULT_DIR_RADIUS: f32 = 20.0;

/// Distance scale per depth level for radial layout.
pub const RADIAL_DISTANCE_SCALE: f32 = 80.0;

/// Minimum angular span for a directory (prevents collapsed sectors).
pub const MIN_ANGULAR_SPAN: f32 = 0.05; // ~3 degrees

/// A node in the directory tree.
///
/// Each directory is represented as a node that can contain files
/// and subdirectories. Directories have physics properties (position,
/// velocity) for force-directed layout.
#[derive(Debug, Clone)]
pub struct DirNode {
    /// The directory ID.
    id: DirId,

    /// Directory name (not the full path).
    name: String,

    /// Full path from repository root.
    path: PathBuf,

    /// Parent directory (None for root).
    parent: Option<DirId>,

    /// Child directories.
    children: Vec<DirId>,

    /// Files directly in this directory.
    files: Vec<FileId>,

    /// Position in 2D space.
    position: Vec2,

    /// Velocity for physics simulation.
    velocity: Vec2,

    /// Visual radius (based on content).
    radius: f32,

    /// Whether this node is visible.
    visible: bool,

    /// Depth in tree (0 = root).
    depth: u32,

    /// Target distance from parent (for layout).
    target_distance: f32,

    /// Cached parent position for physics (updated each frame).
    parent_position: Option<Vec2>,

    /// Start angle of this directory's angular sector (radians).
    start_angle: f32,

    /// End angle of this directory's angular sector (radians).
    end_angle: f32,

    /// Radial distance from root (calculated from depth).
    radial_distance: f32,
}

impl DirNode {
    /// Creates a new root directory node.
    #[must_use]
    pub fn new_root(id: DirId) -> Self {
        Self {
            id,
            name: String::new(),
            path: PathBuf::new(),
            parent: None,
            children: Vec::new(),
            files: Vec::new(),
            position: Vec2::ZERO,
            velocity: Vec2::ZERO,
            radius: DEFAULT_DIR_RADIUS,
            visible: true,
            depth: 0,
            target_distance: 0.0,
            parent_position: None,
            start_angle: 0.0,
            end_angle: std::f32::consts::TAU, // Root owns the full circle
            radial_distance: 0.0,
        }
    }

    /// Creates a new directory node with a name and parent.
    #[must_use]
    pub fn new(id: DirId, name: impl Into<String>, parent: DirId, parent_path: &Path) -> Self {
        let name = name.into();
        let path = parent_path.join(&name);
        Self {
            id,
            name,
            path,
            parent: Some(parent),
            children: Vec::new(),
            files: Vec::new(),
            position: Vec2::ZERO,
            velocity: Vec2::ZERO,
            radius: DEFAULT_DIR_RADIUS,
            visible: true,
            depth: 1, // Will be set correctly when added to tree
            target_distance: DEFAULT_DIR_RADIUS * 3.0,
            parent_position: None,
            start_angle: 0.0, // Will be set when positioned
            end_angle: 0.0,
            radial_distance: RADIAL_DISTANCE_SCALE,
        }
    }

    /// Returns the directory ID.
    #[inline]
    #[must_use]
    pub const fn id(&self) -> DirId {
        self.id
    }

    /// Returns the directory name.
    #[inline]
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the full path from repository root.
    #[inline]
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Returns the parent directory ID, if any.
    #[inline]
    #[must_use]
    pub const fn parent(&self) -> Option<DirId> {
        self.parent
    }

    /// Returns the child directory IDs.
    #[inline]
    #[must_use]
    pub fn children(&self) -> &[DirId] {
        &self.children
    }

    /// Returns the file IDs in this directory.
    #[inline]
    #[must_use]
    pub fn files(&self) -> &[FileId] {
        &self.files
    }

    /// Returns the current position.
    #[inline]
    #[must_use]
    pub const fn position(&self) -> Vec2 {
        self.position
    }

    /// Sets the position.
    #[inline]
    pub fn set_position(&mut self, position: Vec2) {
        self.position = position;
    }

    /// Returns the current velocity.
    #[inline]
    #[must_use]
    pub const fn velocity(&self) -> Vec2 {
        self.velocity
    }

    /// Sets the velocity.
    #[inline]
    pub fn set_velocity(&mut self, velocity: Vec2) {
        self.velocity = velocity;
    }

    /// Adds velocity to the current velocity.
    #[inline]
    pub fn add_velocity(&mut self, delta: Vec2) {
        self.velocity += delta;
    }

    /// Returns the visual radius.
    #[inline]
    #[must_use]
    pub const fn radius(&self) -> f32 {
        self.radius
    }

    /// Sets the visual radius.
    #[inline]
    pub fn set_radius(&mut self, radius: f32) {
        self.radius = radius.max(MIN_DIR_RADIUS);
    }

    /// Returns whether this node is visible.
    #[inline]
    #[must_use]
    pub const fn is_visible(&self) -> bool {
        self.visible
    }

    /// Sets visibility.
    #[inline]
    pub fn set_visible(&mut self, visible: bool) {
        self.visible = visible;
    }

    /// Returns the depth in the tree (0 = root).
    #[inline]
    #[must_use]
    pub const fn depth(&self) -> u32 {
        self.depth
    }

    /// Sets the depth.
    #[inline]
    pub fn set_depth(&mut self, depth: u32) {
        self.depth = depth;
    }

    /// Returns the target distance from parent.
    #[inline]
    #[must_use]
    pub const fn target_distance(&self) -> f32 {
        self.target_distance
    }

    /// Sets the target distance from parent.
    #[inline]
    pub fn set_target_distance(&mut self, distance: f32) {
        self.target_distance = distance;
    }

    /// Returns the cached parent position.
    #[inline]
    #[must_use]
    pub const fn parent_position(&self) -> Option<Vec2> {
        self.parent_position
    }

    /// Sets the cached parent position for physics calculations.
    #[inline]
    pub fn set_parent_position(&mut self, pos: Option<Vec2>) {
        self.parent_position = pos;
    }

    /// Returns the start angle of this directory's angular sector.
    #[inline]
    #[must_use]
    pub const fn start_angle(&self) -> f32 {
        self.start_angle
    }

    /// Returns the end angle of this directory's angular sector.
    #[inline]
    #[must_use]
    pub const fn end_angle(&self) -> f32 {
        self.end_angle
    }

    /// Returns the angular span of this directory's sector.
    #[inline]
    #[must_use]
    pub fn angular_span(&self) -> f32 {
        self.end_angle - self.start_angle
    }

    /// Returns the center angle of this directory's sector.
    #[inline]
    #[must_use]
    pub fn center_angle(&self) -> f32 {
        (self.start_angle + self.end_angle) / 2.0
    }

    /// Sets the angular sector for this directory.
    #[inline]
    pub fn set_angular_sector(&mut self, start: f32, end: f32) {
        self.start_angle = start;
        self.end_angle = end;
    }

    /// Returns the radial distance from root.
    #[inline]
    #[must_use]
    pub const fn radial_distance(&self) -> f32 {
        self.radial_distance
    }

    /// Sets the radial distance.
    #[inline]
    pub fn set_radial_distance(&mut self, distance: f32) {
        self.radial_distance = distance;
    }

    /// Calculates the radial position for this directory node.
    ///
    /// Position is calculated as polar coordinates: (angle, distance) from origin.
    #[must_use]
    pub fn calculate_radial_position(&self) -> Vec2 {
        if self.depth == 0 {
            return Vec2::ZERO; // Root at center
        }

        let angle = self.center_angle();
        Vec2::new(
            angle.cos() * self.radial_distance,
            angle.sin() * self.radial_distance,
        )
    }

    /// Allocates angular sectors for child directories.
    ///
    /// Each child gets a portion of this directory's angular sector based on
    /// its "weight" (number of descendants). Heavier children get more space.
    #[must_use]
    pub fn allocate_child_sectors(&self, child_weights: &[f32]) -> Vec<(f32, f32)> {
        if child_weights.is_empty() {
            return Vec::new();
        }

        let total_weight: f32 = child_weights.iter().sum();
        if total_weight <= 0.0 {
            // Equal distribution if no weights
            let span = self.angular_span() / child_weights.len() as f32;
            return (0..child_weights.len())
                .map(|i| {
                    let start = self.start_angle + i as f32 * span;
                    (start, start + span)
                })
                .collect();
        }

        let mut sectors = Vec::with_capacity(child_weights.len());
        let mut current_angle = self.start_angle;

        for weight in child_weights {
            let proportion = weight / total_weight;
            let span = (self.angular_span() * proportion).max(MIN_ANGULAR_SPAN);
            sectors.push((current_angle, current_angle + span));
            current_angle += span;
        }

        sectors
    }

    /// Gets positions for files arranged around this directory.
    ///
    /// Files are positioned in a semi-circle at the outer edge of the directory's
    /// angular sector, creating a "leaf" pattern at branch ends.
    #[must_use]
    pub fn get_file_positions_radial(&self, count: usize) -> Vec<Vec2> {
        if count == 0 {
            return Vec::new();
        }

        // Files are positioned slightly beyond the directory
        let file_distance = self.radial_distance + self.radius * 1.5;

        // Spread files across the angular sector
        let span = self.angular_span();
        let padding = span * 0.1; // 10% padding on each side
        let usable_span = span - padding * 2.0;
        let start = self.start_angle + padding;

        if count == 1 {
            let angle = self.center_angle();
            return vec![Vec2::new(
                angle.cos() * file_distance,
                angle.sin() * file_distance,
            )];
        }

        (0..count)
            .map(|i| {
                let t = i as f32 / (count - 1) as f32;
                let angle = start + t * usable_span;
                Vec2::new(angle.cos() * file_distance, angle.sin() * file_distance)
            })
            .collect()
    }

    /// Adds a child directory.
    pub fn add_child(&mut self, child_id: DirId) {
        if !self.children.contains(&child_id) {
            self.children.push(child_id);
        }
    }

    /// Removes a child directory.
    pub fn remove_child(&mut self, child_id: DirId) {
        self.children.retain(|&id| id != child_id);
    }

    /// Adds a file to this directory.
    pub fn add_file(&mut self, file_id: FileId) {
        if !self.files.contains(&file_id) {
            self.files.push(file_id);
        }
    }

    /// Removes a file from this directory.
    pub fn remove_file(&mut self, file_id: FileId) {
        self.files.retain(|&id| id != file_id);
    }

    /// Returns true if this is the root directory.
    #[inline]
    #[must_use]
    pub const fn is_root(&self) -> bool {
        self.parent.is_none()
    }

    /// Returns the number of direct children (files + subdirectories).
    #[must_use]
    pub fn child_count(&self) -> usize {
        self.children.len() + self.files.len()
    }

    /// Returns true if this directory is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.children.is_empty() && self.files.is_empty()
    }

    /// Calculate radius based on number of children.
    ///
    /// The radius grows logarithmically with the number of children
    /// to prevent very large directories from dominating the layout.
    #[must_use]
    pub fn calculate_radius_from_count(&self) -> f32 {
        let count = self.child_count();
        if count == 0 {
            MIN_DIR_RADIUS
        } else {
            // Logarithmic growth: base radius + log(count) * scale
            MIN_DIR_RADIUS + (count as f32).ln() * 10.0
        }
    }

    /// Gets optimal positions for child nodes arranged in a circle.
    ///
    /// Returns a vector of positions equally spaced around this node.
    #[must_use]
    pub fn get_child_positions(&self, count: usize) -> Vec<Vec2> {
        if count == 0 {
            return Vec::new();
        }

        let angle_step = std::f32::consts::TAU / count as f32;
        let distance = self.radius * 2.5;

        (0..count)
            .map(|i| {
                let angle = i as f32 * angle_step;
                self.position + Vec2::new(angle.cos() * distance, angle.sin() * distance)
            })
            .collect()
    }

    /// Updates physics: applies velocity and damping.
    pub fn update_physics(&mut self, dt: f32, damping: f32) {
        // Integrate position with current velocity
        self.position += self.velocity * dt;

        // Apply damping for next frame
        self.velocity *= damping;
    }
}

/// A directory tree that manages all directory nodes.
///
/// This provides efficient lookup of directories by path and ID,
/// and maintains the hierarchical structure.
#[derive(Debug, Clone)]
pub struct DirTree {
    /// Storage for all directory nodes, indexed by `DirId`.
    nodes: Vec<Option<DirNode>>,

    /// ID allocator for directory IDs.
    id_allocator: DirIdAllocator,

    /// The root directory ID.
    root_id: DirId,
}

/// A simple allocator for `DirId`s that matches the entity allocator pattern.
#[derive(Debug, Clone)]
struct DirIdAllocator {
    next_index: u32,
    free_list: Vec<(u32, Generation)>,
}

impl DirIdAllocator {
    fn new() -> Self {
        Self {
            next_index: 0,
            free_list: Vec::new(),
        }
    }

    fn allocate(&mut self) -> DirId {
        if let Some((index, generation)) = self.free_list.pop() {
            DirId::new(index, generation)
        } else {
            let index = self.next_index;
            self.next_index = self.next_index.saturating_add(1);
            DirId::new(index, Generation::first())
        }
    }

    fn free(&mut self, id: DirId) {
        let mut generation = id.generation();
        generation.increment();
        self.free_list.push((id.index(), generation));
    }
}

impl Default for DirIdAllocator {
    fn default() -> Self {
        Self::new()
    }
}

impl DirTree {
    /// Creates a new directory tree with a root node.
    #[must_use]
    pub fn new() -> Self {
        let mut allocator = DirIdAllocator::new();
        let root_id = allocator.allocate();
        let root = DirNode::new_root(root_id);

        Self {
            nodes: vec![Some(root)],
            id_allocator: allocator,
            root_id,
        }
    }

    /// Returns the root directory ID.
    #[inline]
    #[must_use]
    pub const fn root_id(&self) -> DirId {
        self.root_id
    }

    /// Returns a reference to the root node.
    #[must_use]
    pub fn root(&self) -> &DirNode {
        self.get(self.root_id).expect("Root node must exist")
    }

    /// Returns a mutable reference to the root node.
    pub fn root_mut(&mut self) -> &mut DirNode {
        let root_id = self.root_id;
        self.get_mut(root_id).expect("Root node must exist")
    }

    /// Gets a directory node by ID.
    #[must_use]
    pub fn get(&self, id: DirId) -> Option<&DirNode> {
        self.nodes
            .get(id.index_usize())
            .and_then(|opt| opt.as_ref())
            .filter(|node| node.id.generation() == id.generation())
    }

    /// Gets a mutable reference to a directory node by ID.
    pub fn get_mut(&mut self, id: DirId) -> Option<&mut DirNode> {
        self.nodes
            .get_mut(id.index_usize())
            .and_then(|opt| opt.as_mut())
            .filter(|node| node.id.generation() == id.generation())
    }

    /// Gets or creates a directory for the given path.
    ///
    /// Creates all intermediate directories as needed.
    pub fn get_or_create_path(&mut self, path: &Path) -> DirId {
        let mut current_id = self.root_id;

        for component in path.components() {
            let name = component.as_os_str().to_string_lossy();

            // Look for existing child with this name
            let existing_child = self.get(current_id).and_then(|node| {
                node.children()
                    .iter()
                    .find(|&&child_id| self.get(child_id).is_some_and(|child| child.name() == name))
            });

            if let Some(&child_id) = existing_child {
                current_id = child_id;
            } else {
                // Create new child directory
                let parent_path = self.get(current_id).map(|n| n.path().to_path_buf());
                let parent_depth = self.get(current_id).map_or(0, DirNode::depth);
                let parent_pos = self.get(current_id).map_or(Vec2::ZERO, DirNode::position);

                let child_id = self.id_allocator.allocate();
                let mut child = DirNode::new(
                    child_id,
                    name.to_string(),
                    current_id,
                    &parent_path.unwrap_or_default(),
                );
                child.set_depth(parent_depth + 1);

                // Position new node near parent with some random offset
                // Using deterministic offset based on name hash
                let hash = name.bytes().fold(0u32, |acc, b| {
                    acc.wrapping_mul(31).wrapping_add(u32::from(b))
                });
                let angle = (hash % 360) as f32 * std::f32::consts::PI / 180.0;
                let offset = Vec2::new(angle.cos(), angle.sin()) * DEFAULT_DIR_RADIUS * 2.0;
                child.set_position(parent_pos + offset);

                // Ensure storage capacity
                let idx = child_id.index_usize();
                if idx >= self.nodes.len() {
                    self.nodes.resize(idx + 1, None);
                }
                self.nodes[idx] = Some(child);

                // Add to parent's children
                if let Some(parent) = self.get_mut(current_id) {
                    parent.add_child(child_id);
                }

                current_id = child_id;
            }
        }

        current_id
    }

    /// Returns an iterator over all directory nodes.
    pub fn iter(&self) -> impl Iterator<Item = &DirNode> {
        self.nodes.iter().filter_map(|opt| opt.as_ref())
    }

    /// Returns a mutable iterator over all directory nodes.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut DirNode> {
        self.nodes.iter_mut().filter_map(|opt| opt.as_mut())
    }

    /// Returns the number of directories in the tree.
    #[must_use]
    pub fn len(&self) -> usize {
        self.nodes.iter().filter(|opt| opt.is_some()).count()
    }

    /// Returns true if the tree only contains the root.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() <= 1
    }

    /// Removes a directory and all its descendants.
    ///
    /// Returns the IDs of all removed directories.
    pub fn remove(&mut self, id: DirId) -> Vec<DirId> {
        if id == self.root_id {
            return Vec::new(); // Cannot remove root
        }

        let mut removed = Vec::new();
        self.remove_recursive(id, &mut removed);

        // Remove from parent's children list
        if let Some(parent_id) = self.get(id).and_then(DirNode::parent) {
            if let Some(parent) = self.get_mut(parent_id) {
                parent.remove_child(id);
            }
        }

        removed
    }

    fn remove_recursive(&mut self, id: DirId, removed: &mut Vec<DirId>) {
        // First, get children to remove
        let children: Vec<DirId> = self
            .get(id)
            .map(|n| n.children().to_vec())
            .unwrap_or_default();

        // Recursively remove children
        for child_id in children {
            self.remove_recursive(child_id, removed);
        }

        // Now remove this node
        if let Some(slot) = self.nodes.get_mut(id.index_usize()) {
            if slot
                .as_ref()
                .is_some_and(|n| n.id.generation() == id.generation())
            {
                *slot = None;
                self.id_allocator.free(id);
                removed.push(id);
            }
        }
    }

    /// Computes the radial tree layout for all directories.
    ///
    /// This assigns angular sectors and radial positions to create a
    /// Gource-like radial tree visualization where:
    /// - Root is at center
    /// - Directories branch out radially based on depth
    /// - Each directory owns an angular sector
    /// - Child directories inherit portions of their parent's sector
    pub fn compute_radial_layout(&mut self) {
        // First pass: calculate weights (total descendants) for each node
        let weights = self.calculate_subtree_weights();

        // Second pass: assign angular sectors starting from root
        self.assign_angular_sectors(self.root_id, 0.0, std::f32::consts::TAU, &weights);

        // Third pass: calculate and apply radial positions
        self.apply_radial_positions();
    }

    /// Calculates the total weight (descendants count) for each directory.
    fn calculate_subtree_weights(&self) -> Vec<f32> {
        let mut weights = vec![0.0f32; self.nodes.len()];

        // Process in reverse depth order (leaves first)
        let mut nodes_by_depth: Vec<(usize, u32)> = self
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(i, opt)| opt.as_ref().map(|n| (i, n.depth())))
            .collect();

        nodes_by_depth.sort_by(|a, b| b.1.cmp(&a.1)); // Descending depth

        for (idx, _depth) in nodes_by_depth {
            if let Some(node) = &self.nodes[idx] {
                // Base weight: 1 for files + accumulated children weights
                let file_weight = node.files().len() as f32;
                let child_weight: f32 = node
                    .children()
                    .iter()
                    .filter_map(|cid| weights.get(cid.index_usize()))
                    .sum();

                weights[idx] = (1.0 + file_weight + child_weight).max(1.0);
            }
        }

        weights
    }

    /// Recursively assigns angular sectors to directories.
    fn assign_angular_sectors(
        &mut self,
        dir_id: DirId,
        start_angle: f32,
        end_angle: f32,
        weights: &[f32],
    ) {
        let idx = dir_id.index_usize();

        // Get children and their weights
        let children: Vec<DirId> = self
            .get(dir_id)
            .map(|n| n.children().to_vec())
            .unwrap_or_default();

        let child_weights: Vec<f32> = children
            .iter()
            .map(|cid| weights.get(cid.index_usize()).copied().unwrap_or(1.0))
            .collect();

        // Set this node's sector
        if let Some(node) = self.nodes.get_mut(idx).and_then(|opt| opt.as_mut()) {
            node.set_angular_sector(start_angle, end_angle);
        }

        if children.is_empty() {
            return;
        }

        // Allocate sectors to children based on weight
        let total_weight: f32 = child_weights.iter().sum();
        let span = end_angle - start_angle;
        let mut current_angle = start_angle;

        for (child_id, weight) in children.iter().zip(child_weights.iter()) {
            let proportion = if total_weight > 0.0 {
                weight / total_weight
            } else {
                1.0 / children.len() as f32
            };
            let child_span = (span * proportion).max(MIN_ANGULAR_SPAN);
            let child_end = current_angle + child_span;

            self.assign_angular_sectors(*child_id, current_angle, child_end, weights);

            current_angle = child_end;
        }
    }

    /// Applies radial positions to all directories based on their sectors.
    fn apply_radial_positions(&mut self) {
        for node in self.nodes.iter_mut().flatten() {
            let depth = node.depth();
            let distance = depth as f32 * RADIAL_DISTANCE_SCALE;
            node.set_radial_distance(distance);

            let new_pos = node.calculate_radial_position();
            node.set_position(new_pos);
        }
    }

    /// Recalculates radial layout for a single branch when a new directory is added.
    ///
    /// More efficient than full `compute_radial_layout()` for incremental updates.
    pub fn update_branch_layout(&mut self, dir_id: DirId) {
        // Find the root of this branch (first ancestor with multiple children or root)
        let mut branch_root = dir_id;
        while let Some(parent_id) = self.get(branch_root).and_then(DirNode::parent) {
            if let Some(parent) = self.get(parent_id) {
                if parent.children().len() > 1 || parent.is_root() {
                    branch_root = parent_id;
                    break;
                }
            }
            branch_root = parent_id;
        }

        // Recompute layout for this subtree
        let weights = self.calculate_subtree_weights();

        if let Some(root) = self.get(branch_root) {
            let start = root.start_angle();
            let end = root.end_angle();
            self.assign_angular_sectors(branch_root, start, end, &weights);
        }

        // Apply positions to this subtree
        self.apply_positions_recursive(branch_root);
    }

    /// Recursively applies radial positions to a subtree.
    fn apply_positions_recursive(&mut self, dir_id: DirId) {
        let children: Vec<DirId> = self
            .get(dir_id)
            .map(|n| n.children().to_vec())
            .unwrap_or_default();

        // Update this node's position
        if let Some(node) = self.get_mut(dir_id) {
            let depth = node.depth();
            let distance = depth as f32 * RADIAL_DISTANCE_SCALE;
            node.set_radial_distance(distance);
            let new_pos = node.calculate_radial_position();
            node.set_position(new_pos);
        }

        // Recurse to children
        for child_id in children {
            self.apply_positions_recursive(child_id);
        }
    }

    /// Updates parent positions cache for physics simulation.
    pub fn update_parent_positions(&mut self) {
        // Collect parent positions
        let parent_positions: Vec<_> = self
            .nodes
            .iter()
            .map(|opt| {
                opt.as_ref().and_then(|node| {
                    node.parent().and_then(|parent_id| {
                        self.nodes
                            .get(parent_id.index_usize())
                            .and_then(|p| p.as_ref())
                            .filter(|p| p.id.generation() == parent_id.generation())
                            .map(|p| p.position)
                    })
                })
            })
            .collect();

        // Apply to nodes
        for (node, parent_pos) in self.nodes.iter_mut().zip(parent_positions) {
            if let Some(n) = node {
                n.set_parent_position(parent_pos);
            }
        }
    }
}

impl Default for DirTree {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dir_node_new_root() {
        let id = DirId::from_index(0);
        let root = DirNode::new_root(id);

        assert_eq!(root.id(), id);
        assert!(root.is_root());
        assert!(root.name().is_empty());
        assert!(root.path().as_os_str().is_empty());
        assert_eq!(root.depth(), 0);
    }

    #[test]
    fn test_dir_node_new() {
        let parent_id = DirId::from_index(0);
        let id = DirId::from_index(1);
        let node = DirNode::new(id, "src", parent_id, Path::new(""));

        assert_eq!(node.id(), id);
        assert!(!node.is_root());
        assert_eq!(node.name(), "src");
        assert_eq!(node.path(), Path::new("src"));
        assert_eq!(node.parent(), Some(parent_id));
    }

    #[test]
    fn test_dir_node_physics() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);

        node.set_position(Vec2::new(10.0, 20.0));
        node.set_velocity(Vec2::new(5.0, -3.0));

        assert_eq!(node.position(), Vec2::new(10.0, 20.0));
        assert_eq!(node.velocity(), Vec2::new(5.0, -3.0));

        node.update_physics(1.0, 0.9);

        // Position should change by velocity
        assert!((node.position().x - 15.0).abs() < 0.001);
        assert!((node.position().y - 17.0).abs() < 0.001);

        // Velocity should be damped
        assert!((node.velocity().x - 4.5).abs() < 0.001);
        assert!((node.velocity().y - (-2.7)).abs() < 0.001);
    }

    #[test]
    fn test_dir_node_children() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);

        let child1 = DirId::from_index(1);
        let child2 = DirId::from_index(2);

        node.add_child(child1);
        node.add_child(child2);
        node.add_child(child1); // Duplicate should be ignored

        assert_eq!(node.children().len(), 2);
        assert!(node.children().contains(&child1));
        assert!(node.children().contains(&child2));

        node.remove_child(child1);
        assert_eq!(node.children().len(), 1);
        assert!(!node.children().contains(&child1));
    }

    #[test]
    fn test_dir_node_files() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);

        let file1 = FileId::from_index(0);
        let file2 = FileId::from_index(1);

        node.add_file(file1);
        node.add_file(file2);

        assert_eq!(node.files().len(), 2);
        assert_eq!(node.child_count(), 2);
        assert!(!node.is_empty());

        node.remove_file(file1);
        assert_eq!(node.files().len(), 1);
    }

    #[test]
    fn test_dir_node_radius() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);

        node.set_radius(100.0);
        assert_eq!(node.radius(), 100.0);

        node.set_radius(0.0);
        assert_eq!(node.radius(), MIN_DIR_RADIUS); // Minimum enforced
    }

    #[test]
    fn test_dir_node_child_positions() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);
        node.set_radius(10.0);

        let positions = node.get_child_positions(4);
        assert_eq!(positions.len(), 4);

        // First position should be to the right (angle = 0)
        let distance = node.radius() * 2.5;
        assert!((positions[0].x - distance).abs() < 0.001);
        assert!(positions[0].y.abs() < 0.001);
    }

    #[test]
    fn test_dir_tree_new() {
        let tree = DirTree::new();

        // A tree with only the root is considered "empty" (no subdirectories)
        assert!(tree.is_empty());
        assert_eq!(tree.len(), 1);
        assert!(tree.root().is_root());
    }

    #[test]
    fn test_dir_tree_get_or_create_path() {
        let mut tree = DirTree::new();

        let dir_id = tree.get_or_create_path(Path::new("src/lib"));
        let node = tree.get(dir_id).unwrap();

        assert_eq!(node.name(), "lib");
        assert_eq!(node.path(), Path::new("src/lib"));
        assert_eq!(node.depth(), 2);

        // Getting the same path should return the same ID
        let same_id = tree.get_or_create_path(Path::new("src/lib"));
        assert_eq!(dir_id, same_id);

        // Tree should now have 3 nodes: root, src, lib
        assert_eq!(tree.len(), 3);
    }

    #[test]
    fn test_dir_tree_hierarchy() {
        let mut tree = DirTree::new();

        let lib_id = tree.get_or_create_path(Path::new("src/lib"));
        let main_id = tree.get_or_create_path(Path::new("src/main"));

        // Get the src directory
        let src_id = tree.get(lib_id).unwrap().parent().unwrap();
        let src = tree.get(src_id).unwrap();

        assert_eq!(src.name(), "src");
        assert!(src.children().contains(&lib_id));
        assert!(src.children().contains(&main_id));
    }

    #[test]
    fn test_dir_tree_remove() {
        let mut tree = DirTree::new();

        let _lib_id = tree.get_or_create_path(Path::new("src/lib/utils"));
        let src_id = tree.get_or_create_path(Path::new("src"));

        // Remove src and all descendants
        let removed = tree.remove(src_id);

        // Should have removed src, lib, utils (3 nodes)
        assert_eq!(removed.len(), 3);

        // Only root should remain
        assert_eq!(tree.len(), 1);
    }

    #[test]
    fn test_dir_tree_cannot_remove_root() {
        let mut tree = DirTree::new();
        let removed = tree.remove(tree.root_id());

        assert!(removed.is_empty());
        assert_eq!(tree.len(), 1);
    }

    #[test]
    fn test_dir_tree_iter() {
        let mut tree = DirTree::new();
        let _id1 = tree.get_or_create_path(Path::new("a"));
        let _id2 = tree.get_or_create_path(Path::new("b"));

        let names: Vec<_> = tree.iter().map(|n| n.name().to_string()).collect();
        assert_eq!(names.len(), 3);
        assert!(names.contains(&String::new())); // root
        assert!(names.contains(&"a".to_string()));
        assert!(names.contains(&"b".to_string()));
    }

    #[test]
    fn test_dir_tree_update_parent_positions() {
        let mut tree = DirTree::new();
        tree.root_mut().set_position(Vec2::new(100.0, 200.0));

        let child_id = tree.get_or_create_path(Path::new("child"));
        tree.update_parent_positions();

        let child = tree.get(child_id).unwrap();
        assert_eq!(child.parent_position(), Some(Vec2::new(100.0, 200.0)));
    }

    #[test]
    fn test_dir_node_angular_sector() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);

        node.set_angular_sector(0.0, std::f32::consts::PI);
        assert!((node.angular_span() - std::f32::consts::PI).abs() < 0.001);
        assert!((node.center_angle() - std::f32::consts::PI / 2.0).abs() < 0.001);
    }

    #[test]
    fn test_dir_node_radial_distance() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);

        node.set_radial_distance(50.0);
        assert_eq!(node.radial_distance(), 50.0);
    }

    #[test]
    fn test_dir_node_calculate_radial_position() {
        let parent_id = DirId::from_index(0);
        let id = DirId::from_index(1);
        let mut node = DirNode::new(id, "child", parent_id, Path::new(""));

        // Set center angle to 0 (pointing right)
        node.set_angular_sector(0.0, 0.0);
        node.set_radial_distance(100.0);
        node.set_depth(1); // Not root

        let pos = node.calculate_radial_position();
        // At angle 0, position should be (100, 0)
        assert!((pos.x - 100.0).abs() < 0.01);
        assert!(pos.y.abs() < 0.01);
    }

    #[test]
    fn test_dir_node_calculate_radial_position_root() {
        let id = DirId::from_index(0);
        let node = DirNode::new_root(id);

        // Root node should always be at origin
        let pos = node.calculate_radial_position();
        assert_eq!(pos, Vec2::ZERO);
    }

    #[test]
    fn test_dir_node_allocate_child_sectors() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);
        node.set_angular_sector(0.0, std::f32::consts::TAU);

        // Equal weights
        let sectors = node.allocate_child_sectors(&[1.0, 1.0, 1.0]);
        assert_eq!(sectors.len(), 3);

        // Each sector should span 2*PI/3
        let expected_span = std::f32::consts::TAU / 3.0;
        for sector in &sectors {
            let span = sector.1 - sector.0;
            assert!((span - expected_span).abs() < 0.01);
        }
    }

    #[test]
    fn test_dir_node_get_file_positions_radial() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);
        node.set_position(Vec2::new(0.0, 0.0));
        node.set_radius(10.0);
        node.set_angular_sector(0.0, std::f32::consts::TAU);

        let positions = node.get_file_positions_radial(4);
        assert_eq!(positions.len(), 4);

        // Positions should be at roughly the same distance from center
        for pos in &positions {
            let dist = pos.length();
            assert!(dist > 10.0); // Should be outside the directory radius
        }
    }

    #[test]
    fn test_dir_node_calculate_radius_from_count() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);

        // Add some files
        for i in 0..10 {
            node.add_file(FileId::from_index(i));
        }

        let radius = node.calculate_radius_from_count();
        assert!(radius >= MIN_DIR_RADIUS);
    }

    #[test]
    fn test_dir_node_update_physics() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);

        node.set_position(Vec2::new(0.0, 0.0));
        node.set_velocity(Vec2::new(100.0, 100.0));

        node.update_physics(0.1, 0.9);

        // Position should have moved
        assert!(node.position().x > 0.0);
        assert!(node.position().y > 0.0);

        // Velocity should be damped
        assert!(node.velocity().x < 100.0);
        assert!(node.velocity().y < 100.0);
    }

    #[test]
    fn test_dir_node_velocity() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);

        node.set_velocity(Vec2::new(10.0, 20.0));
        assert_eq!(node.velocity(), Vec2::new(10.0, 20.0));

        node.add_velocity(Vec2::new(5.0, -5.0));
        assert_eq!(node.velocity(), Vec2::new(15.0, 15.0));
    }

    #[test]
    fn test_dir_node_visibility() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);

        assert!(node.is_visible());

        node.set_visible(false);
        assert!(!node.is_visible());

        node.set_visible(true);
        assert!(node.is_visible());
    }

    #[test]
    fn test_dir_node_depth() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);

        assert_eq!(node.depth(), 0);

        node.set_depth(5);
        assert_eq!(node.depth(), 5);
    }

    #[test]
    fn test_dir_node_target_distance() {
        let id = DirId::from_index(0);
        let mut node = DirNode::new_root(id);

        node.set_target_distance(150.0);
        assert_eq!(node.target_distance(), 150.0);
    }

    #[test]
    fn test_dir_tree_compute_radial_layout() {
        let mut tree = DirTree::new();

        // Create some directories
        let src_id = tree.get_or_create_path(Path::new("src"));
        let _b = tree.get_or_create_path(Path::new("src/lib"));
        let _c = tree.get_or_create_path(Path::new("tests"));

        tree.compute_radial_layout();

        // Root should be at origin
        assert_eq!(tree.root().position(), Vec2::ZERO);

        // Children should have been positioned
        let src_node = tree.get(src_id).unwrap();
        assert!(src_node.position() != Vec2::ZERO);
    }

    #[test]
    fn test_dir_tree_path_lookup() {
        let mut tree = DirTree::new();

        // Create path and verify we can look it up
        let created_id = tree.get_or_create_path(Path::new("src/lib"));

        // Getting the same path again should return the same ID
        let same_id = tree.get_or_create_path(Path::new("src/lib"));
        assert_eq!(created_id, same_id);

        // The node should have the correct path
        let node = tree.get(created_id).unwrap();
        assert_eq!(node.path(), Path::new("src/lib"));
    }

    #[test]
    fn test_dir_tree_default() {
        let tree = DirTree::default();
        assert_eq!(tree.len(), 1);
        assert!(tree.root().is_root());
    }

    #[test]
    fn test_dir_tree_iter_mut() {
        let mut tree = DirTree::new();
        let _ = tree.get_or_create_path(Path::new("a"));
        let _ = tree.get_or_create_path(Path::new("b"));

        // Set all nodes' visibility to false
        for node in tree.iter_mut() {
            node.set_visible(false);
        }

        // Verify all nodes are now invisible
        for node in tree.iter() {
            assert!(!node.is_visible());
        }
    }
}
