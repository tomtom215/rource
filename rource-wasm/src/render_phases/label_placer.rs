// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Label placement with spatial hash collision avoidance.
//!
//! This module provides the `LabelPlacer` struct which uses a grid-based spatial
//! hash to achieve O(n) average-case collision detection instead of O(n²) for
//! the naive pairwise approach.
//!
//! # Algorithm
//!
//! - Screen is divided into 128×128 pixel cells
//! - Each placed label is registered in all cells it overlaps
//! - When checking collision, only labels in overlapping cells are tested
//! - Average case: O(1) collision checks per label (labels spread across cells)
//! - Worst case: O(n) if all labels cluster in same cell
//!
//! # Generation Counter Optimization
//!
//! To achieve O(1) reset instead of O(1024) grid cell clears, we use a generation
//! counter. Each grid entry stores `(label_index, generation)`. On `reset()`, we
//! increment the generation (O(1)). When checking collisions, entries with old
//! generations are skipped. This amortizes grid cleanup into collision checks.

use rource_math::{Rect, Vec2};

use super::helpers::compute_max_labels;

/// Spatial hash cell size for label collision detection (pixels).
///
/// Chosen to balance granularity vs. overhead:
/// - Typical labels are 50-200 pixels wide, 20 pixels tall
/// - 128px cells mean most labels span 1-2 cells horizontally, 1 cell vertically
/// - Larger cells = fewer cells but more labels per cell
/// - Smaller cells = more cells but fewer collision checks per label
const LABEL_CELL_SIZE: f32 = 128.0;

/// Precomputed reciprocal of cell size for fast division.
const INV_LABEL_CELL_SIZE: f32 = 1.0 / LABEL_CELL_SIZE;

/// Grid dimensions for spatial hash (covers 4K screen with margin).
/// 4096 / 128 = 32 cells per axis.
const LABEL_GRID_SIZE: usize = 32;

/// Maximum grid index for clamping (`LABEL_GRID_SIZE - 1`).
/// Using isize to allow safe clamping from negative float→int conversions.
#[allow(clippy::cast_possible_wrap)]
const LABEL_GRID_MAX_IDX: isize = (LABEL_GRID_SIZE - 1) as isize;

/// Threshold for triggering grid compaction. When stale entries exceed this
/// count, we perform a full cleanup. Set to 2x grid size (2048) to amortize
/// cleanup cost.
const LABEL_GRID_STALE_THRESHOLD: usize = 2048;

/// Small margin for viewport bounds checking (T9).
/// Labels within this margin of the viewport edge are considered on-screen.
const VIEWPORT_MARGIN: f32 = 5.0;

/// Label placement helper for collision avoidance using spatial hashing.
///
/// Uses a grid-based spatial hash to achieve O(n) average-case collision detection
/// instead of O(n²) for the naive pairwise approach.
///
/// # Algorithm
///
/// - Screen is divided into 128×128 pixel cells (configurable via `LABEL_CELL_SIZE`)
/// - Each placed label is registered in all cells it overlaps
/// - When checking collision, only labels in overlapping cells are tested
/// - Average case: O(1) collision checks per label (labels spread across cells)
/// - Worst case: O(n) if all labels cluster in same cell (degrades gracefully)
///
/// # Generation Counter Optimization
///
/// To achieve O(1) reset instead of O(1024) grid cell clears, we use a generation
/// counter. Each grid entry stores `(label_index, generation)`. On `reset()`, we
/// increment the generation (O(1)). When checking collisions, entries with old
/// generations are skipped. This amortizes grid cleanup into collision checks.
///
/// # Viewport Bounds Checking (T9)
///
/// Labels that would extend beyond viewport edges are rejected. This prevents:
/// - Labels from being cut off at screen edges
/// - Wasted render calls for off-screen labels
/// - Visual clutter at viewport boundaries
///
/// # Memory Layout
///
/// - `placed_labels`: Stores actual label rectangles
/// - `grid`: 32×32 array of Vecs containing `(index, generation)` tuples
/// - `generation`: Current generation counter (incremented on reset)
/// - `viewport_width/height`: Current viewport dimensions for bounds checking
/// - Total overhead: ~32KB for grid structure (reused across frames)
pub struct LabelPlacer {
    /// All placed label rectangles.
    placed_labels: Vec<Rect>,
    /// Spatial hash grid: each cell contains `(label_index, generation)` tuples.
    /// Indexed as `grid[cy][cx]`. Entries with old generations are stale.
    grid: Vec<Vec<Vec<(usize, u32)>>>,
    /// Current generation. Incremented on `reset()` for O(1) invalidation.
    generation: u32,
    /// Count of stale entries across all cells.
    /// When this exceeds `LABEL_GRID_STALE_THRESHOLD`, we compact the grid.
    stale_entry_count: usize,
    /// Maximum number of labels to place.
    max_labels: usize,
    /// Viewport width for bounds checking (T9: skip off-screen labels).
    viewport_width: f32,
    /// Viewport height for bounds checking (T9: skip off-screen labels).
    viewport_height: f32,
}

impl LabelPlacer {
    /// Creates a new label placer with spatial hash grid.
    ///
    /// # Arguments
    ///
    /// * `camera_zoom` - Current camera zoom level (affects max label count)
    pub fn new(camera_zoom: f32) -> Self {
        let max_labels = compute_max_labels(camera_zoom);
        let mut grid = Vec::with_capacity(LABEL_GRID_SIZE);
        for _ in 0..LABEL_GRID_SIZE {
            let mut row = Vec::with_capacity(LABEL_GRID_SIZE);
            for _ in 0..LABEL_GRID_SIZE {
                row.push(Vec::with_capacity(4)); // Expect ~4 labels per cell
            }
            grid.push(row);
        }
        Self {
            placed_labels: Vec::with_capacity(max_labels),
            grid,
            generation: 0,
            stale_entry_count: 0,
            max_labels,
            // Default viewport (will be set properly on first reset)
            viewport_width: 1920.0,
            viewport_height: 1080.0,
        }
    }

    /// Sets the viewport dimensions for bounds checking (T9).
    ///
    /// Call this when viewport size changes or at the start of each frame
    /// before placing labels.
    #[inline]
    pub fn set_viewport(&mut self, width: f32, height: f32) {
        self.viewport_width = width;
        self.viewport_height = height;
    }

    /// Resets the placer for a new frame using O(1) generation increment.
    ///
    /// Instead of clearing all 1024 grid cells (O(1024)), we increment the
    /// generation counter (O(1)). Stale entries are skipped during collision
    /// checks. This is critical for 42,000 FPS performance targets.
    ///
    /// When stale entries accumulate beyond `LABEL_GRID_STALE_THRESHOLD`,
    /// we perform a full compaction to prevent unbounded memory growth.
    ///
    /// # Complexity
    ///
    /// - Amortized: O(1) - just increments generation and clears `placed_labels`
    /// - Worst case: O(S) where S is stale entries (occurs every ~20 frames)
    /// - Average over N frames: O(1) per frame with periodic O(S) cleanup
    #[inline]
    pub fn reset(&mut self, camera_zoom: f32) {
        // Track stale entries: each label in placed_labels created ~2 grid entries
        // (most labels span 1-2 cells)
        self.stale_entry_count += self.placed_labels.len() * 2;
        self.placed_labels.clear();

        // O(1) reset: increment generation instead of clearing 1024 cells
        self.generation = self.generation.wrapping_add(1);
        self.max_labels = compute_max_labels(camera_zoom);

        // Periodic compaction to prevent unbounded growth
        // Amortized over LABEL_GRID_STALE_THRESHOLD / (avg_labels * 2) frames
        if self.stale_entry_count > LABEL_GRID_STALE_THRESHOLD {
            self.compact_grid();
        }
    }

    /// Compacts the grid by removing all stale entries.
    ///
    /// Called periodically to prevent unbounded memory growth.
    /// Complexity: O(N) where N is total entries, but amortized O(1) per frame.
    #[cold]
    #[inline(never)]
    fn compact_grid(&mut self) {
        for row in &mut self.grid {
            for cell in row {
                cell.clear();
            }
        }
        self.stale_entry_count = 0;
    }

    /// Checks if more labels can be placed.
    #[inline]
    pub fn can_place_more(&self) -> bool {
        self.placed_labels.len() < self.max_labels
    }

    /// Returns the maximum number of labels that can be placed.
    #[inline]
    pub fn max_labels(&self) -> usize {
        self.max_labels
    }

    /// Returns the remaining capacity for labels.
    #[inline]
    pub fn remaining_capacity(&self) -> usize {
        self.max_labels.saturating_sub(self.placed_labels.len())
    }

    /// Converts screen position to grid cell coordinates.
    #[inline]
    fn pos_to_cell(x: f32, y: f32) -> (usize, usize) {
        // Handle negative coordinates by clamping to 0
        let cx = ((x * INV_LABEL_CELL_SIZE).floor() as isize).clamp(0, LABEL_GRID_MAX_IDX) as usize;
        let cy = ((y * INV_LABEL_CELL_SIZE).floor() as isize).clamp(0, LABEL_GRID_MAX_IDX) as usize;
        (cx, cy)
    }

    /// Returns the range of cells a rectangle overlaps.
    #[inline]
    fn rect_cell_range(rect: &Rect) -> ((usize, usize), (usize, usize)) {
        let (min_cx, min_cy) = Self::pos_to_cell(rect.x, rect.y);
        let (max_cx, max_cy) = Self::pos_to_cell(rect.x + rect.width, rect.y + rect.height);
        ((min_cx, min_cy), (max_cx, max_cy))
    }

    /// Tries to place a label, checking for collisions using spatial hash.
    ///
    /// Time complexity: O(k) where k is the number of labels in overlapping cells.
    /// For uniformly distributed labels, k ≈ constant → O(1) average.
    ///
    /// Stale entries (from previous generations) are skipped during collision
    /// checks, enabling O(1) reset via generation increment.
    ///
    /// # T9: Viewport Bounds Checking
    ///
    /// Labels that would extend beyond viewport edges are rejected to prevent:
    /// - Labels being cut off at screen edges
    /// - Wasted render calls for off-screen labels
    #[inline]
    pub fn try_place(&mut self, pos: Vec2, width: f32, height: f32) -> bool {
        let rect = Rect::new(pos.x, pos.y, width, height);

        // T9: Viewport bounds check - reject labels that extend off-screen
        // Allow small negative positions (partial visibility) but reject if mostly off-screen
        if rect.x + rect.width < VIEWPORT_MARGIN
            || rect.y + rect.height < VIEWPORT_MARGIN
            || rect.x > self.viewport_width - VIEWPORT_MARGIN
            || rect.y > self.viewport_height - VIEWPORT_MARGIN
        {
            return false;
        }

        let ((min_cx, min_cy), (max_cx, max_cy)) = Self::rect_cell_range(&rect);
        let current_gen = self.generation;

        // Check for collisions only with labels in overlapping cells
        // Skip stale entries (from previous generations) for O(1) reset
        for cy in min_cy..=max_cy {
            for cx in min_cx..=max_cx {
                for &(label_idx, gen) in &self.grid[cy][cx] {
                    // Skip stale entries from previous generations
                    if gen != current_gen {
                        continue;
                    }
                    if rects_intersect(&rect, &self.placed_labels[label_idx]) {
                        return false;
                    }
                }
            }
        }

        // No collision - add to placed_labels and register in grid cells
        let label_idx = self.placed_labels.len();
        self.placed_labels.push(rect);

        // Store with current generation for O(1) reset support
        for cy in min_cy..=max_cy {
            for cx in min_cx..=max_cx {
                self.grid[cy][cx].push((label_idx, current_gen));
            }
        }

        true
    }

    /// Tries to place with fallback positions.
    #[inline]
    pub fn try_place_with_fallback(
        &mut self,
        primary_pos: Vec2,
        width: f32,
        height: f32,
        anchor: Vec2,
        radius: f32,
    ) -> Option<Vec2> {
        // Try primary position
        if self.try_place(primary_pos, width, height) {
            return Some(primary_pos);
        }

        // Fallback positions
        let fallbacks = [
            Vec2::new(anchor.x - width - radius - 3.0, anchor.y - height * 0.3), // Left
            Vec2::new(anchor.x - width * 0.5, anchor.y + radius + 3.0),          // Below
            Vec2::new(anchor.x - width * 0.5, anchor.y - radius - height - 3.0), // Above
        ];

        for pos in &fallbacks {
            if self.try_place(*pos, width, height) {
                return Some(*pos);
            }
        }

        None
    }
}

/// Checks if two rectangles intersect.
#[inline]
pub fn rects_intersect(a: &Rect, b: &Rect) -> bool {
    a.x < b.x + b.width && a.x + a.width > b.x && a.y < b.y + b.height && a.y + a.height > b.y
}
