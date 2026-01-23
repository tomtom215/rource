// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Spatial partitioning for efficient entity queries.
//!
//! This module provides a quadtree data structure for efficient
//! spatial queries like collision detection and range queries.

use rource_math::{Bounds, Vec2};

/// A quadtree for spatial partitioning of entities.
///
/// The quadtree recursively subdivides space into four quadrants
/// to enable efficient spatial queries. Items are stored at the
/// leaf nodes where they fit.
///
/// # Type Parameters
///
/// - `T`: The type of item stored in the tree. Must be `Clone` for
///   convenience in queries.
#[derive(Debug, Clone)]
pub struct QuadTree<T: Clone> {
    /// The bounds of this node.
    bounds: Bounds,

    /// Items stored at this node.
    items: Vec<(Vec2, T)>,

    /// Child nodes (if subdivided).
    children: Option<Box<[Self; 4]>>,

    /// Maximum items before subdivision.
    max_items: usize,

    /// Maximum depth of the tree.
    max_depth: usize,

    /// Current depth of this node.
    depth: usize,
}

impl<T: Clone> QuadTree<T> {
    /// Creates a new quadtree with the given bounds.
    ///
    /// # Arguments
    ///
    /// - `bounds`: The spatial bounds of the tree
    /// - `max_items`: Maximum items per node before subdivision
    /// - `max_depth`: Maximum tree depth
    #[must_use]
    pub fn new(bounds: Bounds, max_items: usize, max_depth: usize) -> Self {
        Self {
            bounds,
            items: Vec::new(),
            children: None,
            max_items,
            max_depth,
            depth: 0,
        }
    }

    /// Creates a quadtree node with a specific depth (internal use).
    fn with_depth(bounds: Bounds, max_items: usize, max_depth: usize, depth: usize) -> Self {
        Self {
            bounds,
            items: Vec::new(),
            children: None,
            max_items,
            max_depth,
            depth,
        }
    }

    /// Returns the bounds of this quadtree.
    #[inline]
    #[must_use]
    pub fn bounds(&self) -> &Bounds {
        &self.bounds
    }

    /// Returns the number of items in this node (not including children).
    #[inline]
    #[must_use]
    pub fn item_count(&self) -> usize {
        self.items.len()
    }

    /// Returns true if this node has children.
    #[inline]
    #[must_use]
    pub fn is_subdivided(&self) -> bool {
        self.children.is_some()
    }

    /// Returns the total number of items in the tree.
    #[must_use]
    pub fn total_items(&self) -> usize {
        let mut count = self.items.len();
        if let Some(ref children) = self.children {
            for child in children.iter() {
                count += child.total_items();
            }
        }
        count
    }

    /// Clears all items from the tree.
    pub fn clear(&mut self) {
        self.items.clear();
        self.children = None;
    }

    /// Inserts an item at the given position.
    ///
    /// If the position is outside the tree bounds, the item is not inserted.
    pub fn insert(&mut self, position: Vec2, item: T) {
        if !self.bounds.contains(position) {
            return;
        }

        // If we have children, delegate to the appropriate child
        if self.children.is_some() {
            self.insert_into_child(position, item);
            return;
        }

        // Store at this node
        self.items.push((position, item));

        // Subdivide if we exceed capacity and haven't reached max depth
        if self.items.len() > self.max_items && self.depth < self.max_depth {
            self.subdivide();
        }
    }

    /// Inserts an item into the appropriate child node.
    fn insert_into_child(&mut self, position: Vec2, item: T) {
        // Compute index first to avoid borrow conflict
        let index = self.get_child_index(position);
        if let Some(ref mut children) = self.children {
            children[index].insert(position, item);
        }
    }

    /// Gets the index of the child that contains the given position.
    fn get_child_index(&self, position: Vec2) -> usize {
        let center = self.bounds.center();
        let right = position.x >= center.x;
        let bottom = position.y >= center.y;

        match (right, bottom) {
            (false, false) => 0, // Top-left
            (true, false) => 1,  // Top-right
            (false, true) => 2,  // Bottom-left
            (true, true) => 3,   // Bottom-right
        }
    }

    /// Subdivides this node into four children.
    fn subdivide(&mut self) {
        let center = self.bounds.center();
        let min = self.bounds.min;
        let max = self.bounds.max;

        let children = Box::new([
            // Top-left
            Self::with_depth(
                Bounds::new(min, center),
                self.max_items,
                self.max_depth,
                self.depth + 1,
            ),
            // Top-right
            Self::with_depth(
                Bounds::new(Vec2::new(center.x, min.y), Vec2::new(max.x, center.y)),
                self.max_items,
                self.max_depth,
                self.depth + 1,
            ),
            // Bottom-left
            Self::with_depth(
                Bounds::new(Vec2::new(min.x, center.y), Vec2::new(center.x, max.y)),
                self.max_items,
                self.max_depth,
                self.depth + 1,
            ),
            // Bottom-right
            Self::with_depth(
                Bounds::new(center, max),
                self.max_items,
                self.max_depth,
                self.depth + 1,
            ),
        ]);

        self.children = Some(children);

        // Move existing items to children
        let items = std::mem::take(&mut self.items);
        for (pos, item) in items {
            self.insert_into_child(pos, item);
        }
    }

    /// Queries items within the given bounds.
    ///
    /// Returns references to all items whose positions fall within
    /// the query bounds.
    #[must_use]
    pub fn query(&self, bounds: &Bounds) -> Vec<&T> {
        let mut results = Vec::new();
        self.query_recursive(bounds, &mut results);
        results
    }

    /// Recursive query implementation.
    fn query_recursive<'a>(&'a self, bounds: &Bounds, results: &mut Vec<&'a T>) {
        if !self.bounds.intersects(*bounds) {
            return;
        }

        // Check items at this node
        for (pos, item) in &self.items {
            if bounds.contains(*pos) {
                results.push(item);
            }
        }

        // Check children
        if let Some(ref children) = self.children {
            for child in children.iter() {
                child.query_recursive(bounds, results);
            }
        }
    }

    /// Queries items within a circular region.
    ///
    /// Returns references to all items within the given radius of the center.
    /// Note: This delegates to `query_circle_with_pos` and discards positions.
    #[must_use]
    pub fn query_circle(&self, center: Vec2, radius: f32) -> Vec<&T> {
        self.query_circle_with_pos(center, radius)
            .into_iter()
            .map(|(_, item)| item)
            .collect()
    }

    /// Queries items within a circular region, returning positions too.
    #[must_use]
    pub fn query_circle_with_pos(&self, center: Vec2, radius: f32) -> Vec<(Vec2, &T)> {
        let query_bounds = Bounds::new(center - Vec2::splat(radius), center + Vec2::splat(radius));

        let mut results = Vec::new();
        self.query_with_pos_recursive(&query_bounds, &mut results);

        // Filter by actual distance
        let radius_sq = radius * radius;
        results
            .into_iter()
            .filter(|(pos, _)| (*pos - center).length_squared() <= radius_sq)
            .collect()
    }

    /// Recursive query implementation that includes positions.
    fn query_with_pos_recursive<'a>(&'a self, bounds: &Bounds, results: &mut Vec<(Vec2, &'a T)>) {
        if !self.bounds.intersects(*bounds) {
            return;
        }

        for (pos, item) in &self.items {
            if bounds.contains(*pos) {
                results.push((*pos, item));
            }
        }

        if let Some(ref children) = self.children {
            for child in children.iter() {
                child.query_with_pos_recursive(bounds, results);
            }
        }
    }

    /// Finds the nearest item to the given position.
    ///
    /// Returns the item and its position, or None if the tree is empty.
    #[must_use]
    pub fn nearest(&self, position: Vec2) -> Option<(Vec2, &T)> {
        let mut nearest: Option<(Vec2, &T, f32)> = None;
        self.nearest_recursive(position, &mut nearest);
        nearest.map(|(pos, item, _)| (pos, item))
    }

    /// Computes the minimum squared distance from a point to a bounding box.
    fn distance_squared_to_bounds(bounds: &Bounds, point: Vec2) -> f32 {
        // Clamp point to bounds and compute distance
        let clamped_x = point.x.clamp(bounds.min.x, bounds.max.x);
        let clamped_y = point.y.clamp(bounds.min.y, bounds.max.y);
        let dx = point.x - clamped_x;
        let dy = point.y - clamped_y;

        dx * dx + dy * dy
    }

    /// Recursive nearest-neighbor search.
    fn nearest_recursive<'a>(&'a self, position: Vec2, best: &mut Option<(Vec2, &'a T, f32)>) {
        // Check items at this node
        for (pos, item) in &self.items {
            let dist_sq = (*pos - position).length_squared();
            let dominated = best
                .as_ref()
                .is_some_and(|(_, _, best_dist)| dist_sq >= *best_dist);
            if !dominated {
                *best = Some((*pos, item, dist_sq));
            }
        }

        // Check children
        if let Some(ref children) = self.children {
            // Visit children in order of distance to their center
            // Use fixed-size array instead of Vec to avoid heap allocation
            let mut child_indices: [usize; 4] = [0, 1, 2, 3];
            child_indices.sort_by(|&a, &b| {
                let dist_a = (children[a].bounds.center() - position).length_squared();
                let dist_b = (children[b].bounds.center() - position).length_squared();
                dist_a
                    .partial_cmp(&dist_b)
                    .unwrap_or(std::cmp::Ordering::Equal)
            });

            for &idx in &child_indices {
                // Skip if this child can't possibly contain a closer point
                if let Some((_, _, best_dist_sq)) = *best {
                    let min_dist_sq =
                        Self::distance_squared_to_bounds(&children[idx].bounds, position);
                    if min_dist_sq >= best_dist_sq {
                        continue;
                    }
                }

                children[idx].nearest_recursive(position, best);
            }
        }
    }

    /// Returns an iterator over all items in the tree.
    pub fn iter(&self) -> impl Iterator<Item = (Vec2, &T)> {
        QuadTreeIter {
            stack: vec![self],
            current_items: self.items.iter(),
        }
    }
}

/// Iterator over quadtree items.
struct QuadTreeIter<'a, T: Clone> {
    stack: Vec<&'a QuadTree<T>>,
    current_items: std::slice::Iter<'a, (Vec2, T)>,
}

impl<'a, T: Clone> Iterator for QuadTreeIter<'a, T> {
    type Item = (Vec2, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some((pos, item)) = self.current_items.next() {
                return Some((*pos, item));
            }

            // Move to next node
            if let Some(node) = self.stack.pop() {
                if let Some(ref children) = node.children {
                    for child in children.iter().rev() {
                        self.stack.push(child);
                    }
                }

                if let Some(next_node) = self.stack.last() {
                    self.current_items = next_node.items.iter();
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_tree() -> QuadTree<u32> {
        QuadTree::new(Bounds::new(Vec2::ZERO, Vec2::new(100.0, 100.0)), 4, 8)
    }

    #[test]
    fn test_quadtree_new() {
        let tree: QuadTree<u32> = create_test_tree();

        assert_eq!(tree.total_items(), 0);
        assert!(!tree.is_subdivided());
    }

    #[test]
    fn test_quadtree_insert() {
        let mut tree = create_test_tree();

        tree.insert(Vec2::new(10.0, 10.0), 1);
        tree.insert(Vec2::new(20.0, 20.0), 2);
        tree.insert(Vec2::new(30.0, 30.0), 3);

        assert_eq!(tree.total_items(), 3);
    }

    #[test]
    fn test_quadtree_insert_outside_bounds() {
        let mut tree = create_test_tree();

        tree.insert(Vec2::new(-10.0, -10.0), 1);
        tree.insert(Vec2::new(150.0, 150.0), 2);

        assert_eq!(tree.total_items(), 0);
    }

    #[test]
    fn test_quadtree_subdivide() {
        let mut tree = create_test_tree();

        // Insert more than max_items to trigger subdivision
        for i in 0..10 {
            tree.insert(Vec2::new(i as f32 * 5.0, i as f32 * 5.0), i);
        }

        assert!(tree.is_subdivided());
        assert_eq!(tree.total_items(), 10);
    }

    #[test]
    fn test_quadtree_query() {
        let mut tree = create_test_tree();

        tree.insert(Vec2::new(10.0, 10.0), 1);
        tree.insert(Vec2::new(90.0, 90.0), 2);
        tree.insert(Vec2::new(50.0, 50.0), 3);

        // Query lower-left quadrant
        let results = tree.query(&Bounds::new(Vec2::ZERO, Vec2::new(50.0, 50.0)));
        assert_eq!(results.len(), 2); // Items 1 and 3
        assert!(results.contains(&&1));
        assert!(results.contains(&&3));
    }

    #[test]
    fn test_quadtree_query_empty() {
        let mut tree = create_test_tree();

        tree.insert(Vec2::new(10.0, 10.0), 1);

        // Query area with no items
        let results = tree.query(&Bounds::new(Vec2::new(80.0, 80.0), Vec2::new(100.0, 100.0)));
        assert!(results.is_empty());
    }

    #[test]
    fn test_quadtree_query_circle_with_pos() {
        let mut tree = create_test_tree();

        tree.insert(Vec2::new(50.0, 50.0), 1);
        tree.insert(Vec2::new(55.0, 50.0), 2);
        tree.insert(Vec2::new(90.0, 90.0), 3);

        // Query with circle centered at (50, 50) with radius 10
        let results = tree.query_circle_with_pos(Vec2::new(50.0, 50.0), 10.0);
        assert_eq!(results.len(), 2); // Items 1 and 2

        // Verify positions are returned
        assert!(results.iter().any(|(_, &v)| v == 1));
        assert!(results.iter().any(|(_, &v)| v == 2));
    }

    #[test]
    fn test_quadtree_nearest() {
        let mut tree = create_test_tree();

        tree.insert(Vec2::new(10.0, 10.0), 1);
        tree.insert(Vec2::new(50.0, 50.0), 2);
        tree.insert(Vec2::new(90.0, 90.0), 3);

        // Find nearest to (45, 45)
        let result = tree.nearest(Vec2::new(45.0, 45.0));
        assert!(result.is_some());
        let (pos, &value) = result.unwrap();
        assert_eq!(value, 2);
        assert_eq!(pos, Vec2::new(50.0, 50.0));
    }

    #[test]
    fn test_quadtree_nearest_empty() {
        let tree: QuadTree<u32> = create_test_tree();

        let result = tree.nearest(Vec2::new(50.0, 50.0));
        assert!(result.is_none());
    }

    #[test]
    fn test_quadtree_clear() {
        let mut tree = create_test_tree();

        for i in 0..10 {
            tree.insert(Vec2::new(i as f32 * 10.0, i as f32 * 10.0), i);
        }

        assert!(tree.total_items() > 0);
        assert!(tree.is_subdivided());

        tree.clear();

        assert_eq!(tree.total_items(), 0);
        assert!(!tree.is_subdivided());
    }

    #[test]
    fn test_quadtree_iter() {
        let mut tree = create_test_tree();

        tree.insert(Vec2::new(10.0, 10.0), 1);
        tree.insert(Vec2::new(20.0, 20.0), 2);
        tree.insert(Vec2::new(30.0, 30.0), 3);

        let items: Vec<_> = tree.iter().map(|(_, &v)| v).collect();
        assert_eq!(items.len(), 3);
        assert!(items.contains(&1));
        assert!(items.contains(&2));
        assert!(items.contains(&3));
    }

    #[test]
    fn test_quadtree_many_items() {
        let mut tree = create_test_tree();

        // Insert 100 items
        for i in 0..100 {
            let x = (i % 10) as f32 * 10.0 + 1.0;
            let y = (i / 10) as f32 * 10.0 + 1.0;
            tree.insert(Vec2::new(x, y), i);
        }

        assert_eq!(tree.total_items(), 100);

        // Query center
        let results = tree.query(&Bounds::new(Vec2::new(40.0, 40.0), Vec2::new(60.0, 60.0)));
        assert!(!results.is_empty());
    }

    #[test]
    fn test_quadtree_bounds_edge() {
        let mut tree = create_test_tree();

        // Insert at exact bounds
        tree.insert(Vec2::ZERO, 1);
        tree.insert(Vec2::new(100.0, 100.0), 2);

        // Zero should be included, max boundary behavior
        assert!(tree.total_items() >= 1);
    }
}
