// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Directory tree structure for the visualization.
//!
//! The directory tree is the backbone of the scene graph, representing
//! the hierarchical file structure of the repository being visualized.
//!
//! This module re-exports [`DirNode`] and related constants from
//! [`super::dir_node`] for backward compatibility.

mod dir_node_mod {
    pub use super::super::dir_node::*;
}

// Re-export DirNode and constants for backward compatibility
pub use dir_node_mod::{
    DirNode, DEFAULT_DIR_RADIUS, MIN_ANGULAR_SPAN, MIN_DIR_RADIUS, RADIAL_DISTANCE_SCALE,
};

use std::collections::HashMap;
use std::path::Path;

use rource_math::Vec2;

use crate::config::LayoutSettings;
use crate::entity::{DirId, Generation};

/// Runtime configuration for radial layout computation.
///
/// This struct holds the computed layout parameters used during layout.
/// It can be constructed from [`LayoutSettings`] or using defaults.
///
/// # Performance
///
/// Creating a `LayoutConfig` is cheap (no allocations). It's designed to
/// be created once per layout computation and passed by reference.
#[derive(Debug, Clone, Copy)]
pub struct LayoutConfig {
    /// Distance per depth level (world units).
    pub radial_distance_scale: f32,
    /// Minimum angular span per directory (radians).
    pub min_angular_span: f32,
    /// Exponent for depth-based distance scaling.
    pub depth_distance_exponent: f32,
    /// Multiplier for sibling angular spacing.
    pub sibling_spacing_multiplier: f32,
}

impl Default for LayoutConfig {
    fn default() -> Self {
        Self {
            radial_distance_scale: RADIAL_DISTANCE_SCALE,
            min_angular_span: MIN_ANGULAR_SPAN,
            depth_distance_exponent: 1.0,
            sibling_spacing_multiplier: 1.0,
        }
    }
}

impl LayoutConfig {
    /// Creates a layout config from layout settings.
    #[must_use]
    pub fn from_settings(settings: &LayoutSettings) -> Self {
        Self {
            radial_distance_scale: settings.radial_distance_scale,
            min_angular_span: settings.min_angular_span,
            depth_distance_exponent: settings.depth_distance_exponent,
            sibling_spacing_multiplier: settings.sibling_spacing_multiplier,
        }
    }

    /// Creates a layout config optimized for large repositories.
    ///
    /// Uses increased spacing and wider angular spans to reduce center density.
    #[must_use]
    pub fn large_repo() -> Self {
        Self {
            radial_distance_scale: 160.0,
            min_angular_span: 0.08,
            depth_distance_exponent: 1.2,
            sibling_spacing_multiplier: 1.2,
        }
    }

    /// Creates a layout config optimized for massive repositories (50k+ files).
    ///
    /// Uses maximum spacing and aggressive depth scaling.
    #[must_use]
    pub fn massive_repo() -> Self {
        Self {
            radial_distance_scale: 250.0,
            min_angular_span: 0.1,
            depth_distance_exponent: 1.3,
            sibling_spacing_multiplier: 1.5,
        }
    }

    /// Computes an appropriate layout config based on repository statistics.
    ///
    /// # Arguments
    /// * `file_count` - Total number of files
    /// * `max_depth` - Maximum directory depth
    /// * `dir_count` - Total number of directories
    #[must_use]
    pub fn from_repo_stats(file_count: usize, max_depth: u32, dir_count: usize) -> Self {
        let settings = LayoutSettings::from_repo_stats(file_count, max_depth, dir_count);
        Self::from_settings(&settings)
    }
}

/// The directory tree containing all directory nodes.
///
/// The tree manages directory creation, removal, and layout computation.
/// It uses a slot-based storage with generation tracking for safe references.
#[derive(Debug)]
pub struct DirTree {
    /// Storage for all directory nodes, indexed by `DirId`.
    nodes: Vec<Option<DirNode>>,

    /// ID allocator for directory IDs.
    id_allocator: DirIdAllocator,

    /// The root directory ID.
    root_id: DirId,

    /// Index for O(1) child lookup by name.
    /// Maps `(parent_id_index, child_name) -> child_id`.
    /// This eliminates O(c) linear scans in `get_or_create_path`.
    children_by_name: HashMap<(u32, String), DirId>,
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
            children_by_name: HashMap::new(),
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
            .filter(|node| node.id().generation() == id.generation())
    }

    /// Gets a mutable reference to a directory node by ID.
    pub fn get_mut(&mut self, id: DirId) -> Option<&mut DirNode> {
        self.nodes
            .get_mut(id.index_usize())
            .and_then(|opt| opt.as_mut())
            .filter(|node| node.id().generation() == id.generation())
    }

    /// Gets or creates a directory for the given path.
    ///
    /// Creates all intermediate directories as needed.
    /// Uses O(1) `HashMap` lookup for existing children instead of O(n) linear scan.
    pub fn get_or_create_path(&mut self, path: &Path) -> DirId {
        let mut current_id = self.root_id;

        for component in path.components() {
            let name = component.as_os_str().to_string_lossy();
            // Allocate name string once and reuse for both lookup and child creation
            // Previously: name.to_string() was called twice (lookup + child_name)
            let name_string = name.into_owned();

            // O(1) HashMap lookup for existing child with this name
            // Use clone for lookup key since we may need name_string for child creation
            let lookup_key = (current_id.index(), name_string.clone());
            if let Some(&child_id) = self.children_by_name.get(&lookup_key) {
                // Verify the child still exists with correct generation
                if self.get(child_id).is_some() {
                    current_id = child_id;
                    continue;
                }
                // Child was removed, fall through to create new one
            }

            // Create new child directory
            let parent_path = self.get(current_id).map(|n| n.path().to_path_buf());
            let parent_depth = self.get(current_id).map_or(0, DirNode::depth);
            let parent_pos = self.get(current_id).map_or(Vec2::ZERO, DirNode::position);

            let child_id = self.id_allocator.allocate();
            // Reuse name_string instead of calling to_string() again
            let child_name = name_string;
            let mut child = DirNode::new(
                child_id,
                child_name.clone(),
                current_id,
                &parent_path.unwrap_or_default(),
            );
            child.set_depth(parent_depth + 1);

            // Position new node near parent with some random offset
            // Using deterministic offset based on name hash
            let hash = child_name.bytes().fold(0u32, |acc, b| {
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

            // Add to children_by_name index for O(1) future lookups
            self.children_by_name
                .insert((current_id.index(), child_name), child_id);

            current_id = child_id;
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
    /// Also cleans up the `children_by_name` index.
    pub fn remove(&mut self, id: DirId) -> Vec<DirId> {
        if id == self.root_id {
            return Vec::new(); // Cannot remove root
        }

        // Get parent and name before removal for index cleanup
        let parent_and_name = self.get(id).map(|n| (n.parent(), n.name().to_string()));

        let mut removed = Vec::new();
        self.remove_recursive(id, &mut removed);

        // Remove from parent's children list and children_by_name index
        if let Some((Some(parent_id), name)) = parent_and_name {
            if let Some(parent) = self.get_mut(parent_id) {
                parent.remove_child(id);
            }
            // Clean up children_by_name index
            self.children_by_name.remove(&(parent_id.index(), name));
        }

        removed
    }

    fn remove_recursive(&mut self, id: DirId, removed: &mut Vec<DirId>) {
        // First, get children and their names for index cleanup
        let children_with_names: Vec<(DirId, String)> = self
            .get(id)
            .map(|node| {
                node.children()
                    .iter()
                    .filter_map(|&child_id| {
                        self.get(child_id).map(|c| (child_id, c.name().to_string()))
                    })
                    .collect()
            })
            .unwrap_or_default();

        // Recursively remove children
        for (child_id, child_name) in children_with_names {
            self.remove_recursive(child_id, removed);
            // Clean up children_by_name index for this child
            self.children_by_name.remove(&(id.index(), child_name));
        }

        // Now remove this node
        if let Some(slot) = self.nodes.get_mut(id.index_usize()) {
            if slot
                .as_ref()
                .is_some_and(|n| n.id().generation() == id.generation())
            {
                *slot = None;
                self.id_allocator.free(id);
                removed.push(id);
            }
        }
    }

    /// Computes the radial tree layout for all directories using default configuration.
    ///
    /// This assigns angular sectors and radial positions to create a
    /// Gource-like radial tree visualization where:
    /// - Root is at center
    /// - Directories branch out radially based on depth
    /// - Each directory owns an angular sector
    /// - Child directories inherit portions of their parent's sector
    ///
    /// For customizable layout parameters, use [`Self::compute_radial_layout_with_config`].
    pub fn compute_radial_layout(&mut self) {
        self.compute_radial_layout_with_config(&LayoutConfig::default());
    }

    /// Computes the radial tree layout with custom configuration.
    ///
    /// This version allows tuning layout parameters for different repository sizes.
    /// Use [`LayoutConfig::from_repo_stats`] to automatically compute optimal
    /// parameters based on repository characteristics.
    ///
    /// # Arguments
    /// * `config` - Layout configuration with spacing and scaling parameters
    ///
    /// # Example
    /// ```ignore
    /// // For a large repository
    /// let config = LayoutConfig::from_repo_stats(50000, 12, 3000);
    /// tree.compute_radial_layout_with_config(&config);
    /// ```
    pub fn compute_radial_layout_with_config(&mut self, config: &LayoutConfig) {
        // First pass: calculate weights (total descendants) for each node
        let weights = self.calculate_subtree_weights();

        // Second pass: assign angular sectors starting from root
        self.assign_angular_sectors_with_config(
            self.root_id,
            0.0,
            std::f32::consts::TAU,
            &weights,
            config,
        );

        // Third pass: calculate and apply radial positions
        self.apply_radial_positions_with_config(config);
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

        nodes_by_depth.sort_unstable_by(|a, b| b.1.cmp(&a.1)); // Descending depth

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

    /// Recursively assigns angular sectors to directories using default configuration.
    fn assign_angular_sectors(
        &mut self,
        dir_id: DirId,
        start_angle: f32,
        end_angle: f32,
        weights: &[f32],
    ) {
        self.assign_angular_sectors_with_config(
            dir_id,
            start_angle,
            end_angle,
            weights,
            &LayoutConfig::default(),
        );
    }

    /// Recursively assigns angular sectors to directories with custom configuration.
    fn assign_angular_sectors_with_config(
        &mut self,
        dir_id: DirId,
        start_angle: f32,
        end_angle: f32,
        weights: &[f32],
        config: &LayoutConfig,
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

        // Apply sibling spacing multiplier to increase angular separation
        let effective_span = span * config.sibling_spacing_multiplier.min(1.0);
        let padding = (span - effective_span) * 0.5;
        let mut current_angle = start_angle + padding;

        for (child_id, weight) in children.iter().zip(child_weights.iter()) {
            let proportion = if total_weight > 0.0 {
                weight / total_weight
            } else {
                1.0 / children.len() as f32
            };

            // Use configurable minimum angular span
            let child_span = (effective_span * proportion).max(config.min_angular_span);
            let child_end = current_angle + child_span;

            self.assign_angular_sectors_with_config(
                *child_id,
                current_angle,
                child_end,
                weights,
                config,
            );

            current_angle = child_end;
        }
    }

    /// Applies radial positions to all directories.
    ///
    /// Uses configurable radial distance scaling and depth exponent:
    /// - `distance = radial_distance_scale * depth^depth_distance_exponent`
    ///
    /// The depth exponent allows deeper directories to have proportionally
    /// more spacing, which helps reduce center density in large repos.
    fn apply_radial_positions_with_config(&mut self, config: &LayoutConfig) {
        for node in self.nodes.iter_mut().flatten() {
            let depth = node.depth();

            // Apply depth exponent for non-linear scaling
            // depth^exponent where exponent > 1 spreads deeper levels more
            let depth_factor = if config.depth_distance_exponent == 1.0 {
                depth as f32
            } else {
                (depth as f32).powf(config.depth_distance_exponent)
            };

            let distance = depth_factor * config.radial_distance_scale;
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
                            .filter(|p| p.id().generation() == parent_id.generation())
                            .map(DirNode::position)
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
    fn test_dir_tree_new() {
        let tree = DirTree::new();

        assert_eq!(tree.len(), 1);
        assert!(tree.is_empty()); // Only root, no real directories

        let root = tree.root();
        assert!(root.is_root());
        assert_eq!(root.depth(), 0);
    }

    #[test]
    fn test_dir_tree_get_or_create_path() {
        let mut tree = DirTree::new();

        let src_id = tree.get_or_create_path(Path::new("src"));
        let lib_id = tree.get_or_create_path(Path::new("src/lib"));
        let main_id = tree.get_or_create_path(Path::new("src/main"));

        assert_eq!(tree.len(), 4); // root + src + lib + main

        // src should be parent of lib and main
        let src = tree.get(src_id).unwrap();
        assert_eq!(src.name(), "src");
        assert_eq!(src.children().len(), 2);
        assert!(src.children().contains(&lib_id));
        assert!(src.children().contains(&main_id));

        let lib = tree.get(lib_id).unwrap();
        assert_eq!(lib.name(), "lib");
        assert_eq!(lib.parent(), Some(src_id));
        assert_eq!(lib.depth(), 2);
    }

    #[test]
    fn test_dir_tree_get_or_create_path_existing() {
        let mut tree = DirTree::new();

        let id1 = tree.get_or_create_path(Path::new("src"));
        let id2 = tree.get_or_create_path(Path::new("src"));

        assert_eq!(id1, id2);
        assert_eq!(tree.len(), 2); // root + src
    }

    #[test]
    fn test_dir_tree_deep_path() {
        let mut tree = DirTree::new();

        let deep_id = tree.get_or_create_path(Path::new("a/b/c/d/e"));

        let deep = tree.get(deep_id).unwrap();
        assert_eq!(deep.name(), "e");
        assert_eq!(deep.depth(), 5);
        assert_eq!(deep.path(), Path::new("a/b/c/d/e"));

        assert_eq!(tree.len(), 6); // root + a + b + c + d + e
    }

    #[test]
    fn test_dir_tree_iter() {
        let mut tree = DirTree::new();

        tree.get_or_create_path(Path::new("src"));
        tree.get_or_create_path(Path::new("tests"));

        let names: Vec<_> = tree.iter().map(DirNode::name).collect();
        assert_eq!(names.len(), 3);
        assert!(names.contains(&"")); // root
        assert!(names.contains(&"src"));
        assert!(names.contains(&"tests"));
    }

    #[test]
    fn test_dir_tree_remove() {
        let mut tree = DirTree::new();

        let src_id = tree.get_or_create_path(Path::new("src"));
        tree.get_or_create_path(Path::new("src/lib"));
        tree.get_or_create_path(Path::new("src/main"));

        assert_eq!(tree.len(), 4);

        let removed = tree.remove(src_id);
        assert_eq!(removed.len(), 3); // src + lib + main

        assert_eq!(tree.len(), 1); // Only root remains
        assert!(tree.get(src_id).is_none());
    }

    #[test]
    fn test_dir_tree_cannot_remove_root() {
        let mut tree = DirTree::new();
        let root_id = tree.root_id();

        let removed = tree.remove(root_id);
        assert!(removed.is_empty());
        assert_eq!(tree.len(), 1);
    }

    #[test]
    fn test_dir_tree_compute_radial_layout() {
        let mut tree = DirTree::new();

        tree.get_or_create_path(Path::new("src"));
        tree.get_or_create_path(Path::new("tests"));
        tree.get_or_create_path(Path::new("docs"));

        tree.compute_radial_layout();

        // Root should be at center
        let root = tree.root();
        assert_eq!(root.position(), Vec2::ZERO);
        assert!((root.start_angle() - 0.0).abs() < 0.001);
        assert!((root.end_angle() - std::f32::consts::TAU).abs() < 0.001);

        // Children should have different angular sectors
        let children: Vec<_> = tree.iter().filter(|n| n.depth() == 1).collect();
        assert_eq!(children.len(), 3);

        // Each child should have a portion of the full circle
        for child in &children {
            assert!(child.angular_span() > 0.0);
            assert!(child.radial_distance() > 0.0);
        }
    }

    #[test]
    fn test_dir_tree_update_parent_positions() {
        let mut tree = DirTree::new();

        tree.get_or_create_path(Path::new("src/lib"));

        // Set root position
        tree.root_mut().set_position(Vec2::new(100.0, 100.0));

        tree.update_parent_positions();

        // src should have root's position as parent position
        let src_id = tree
            .iter()
            .find(|n| n.name() == "src")
            .map(DirNode::id)
            .unwrap();
        let src = tree.get(src_id).unwrap();
        assert_eq!(src.parent_position(), Some(Vec2::new(100.0, 100.0)));

        // lib should have src's position as parent position
        let lib = tree.iter().find(|n| n.name() == "lib").unwrap();
        assert_eq!(lib.parent_position(), Some(src.position()));
    }

    #[test]
    fn test_dir_tree_update_branch_layout() {
        let mut tree = DirTree::new();

        // Create initial structure
        tree.get_or_create_path(Path::new("src"));
        tree.get_or_create_path(Path::new("tests"));
        tree.compute_radial_layout();

        // Add new directory
        let new_id = tree.get_or_create_path(Path::new("src/new"));
        tree.update_branch_layout(new_id);

        // New directory should have valid position
        let new_dir = tree.get(new_id).unwrap();
        assert!(new_dir.radial_distance() > 0.0);
    }

    #[test]
    fn test_dir_id_allocator() {
        let mut allocator = DirIdAllocator::new();

        let id1 = allocator.allocate();
        let id2 = allocator.allocate();
        let id3 = allocator.allocate();

        assert_eq!(id1.index(), 0);
        assert_eq!(id2.index(), 1);
        assert_eq!(id3.index(), 2);

        // Free id2 and reallocate
        allocator.free(id2);
        let id4 = allocator.allocate();

        assert_eq!(id4.index(), 1); // Reuses index
        assert!(id4.generation().value() > id2.generation().value()); // New generation
    }
}
