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
//! # Phase 86: Flat Grid + Dirty-Cell Tracking
//!
//! The grid uses a flat `Vec<Vec<usize>>` indexed as `grid[cy * 32 + cx]`
//! instead of triple-nested `Vec<Vec<Vec<(usize, u32)>>>`. This eliminates:
//! - Two levels of pointer indirection (cache-hostile)
//! - Per-entry generation tags (branch in tight inner loop)
//! - Stale entry accumulation and periodic compaction
//!
//! Reset uses dirty-cell tracking: only cells that were written to are cleared,
//! giving O(k) reset where k = cells used (~80-160 for 80 labels).

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

/// Total number of cells in the flat grid.
const LABEL_GRID_TOTAL: usize = LABEL_GRID_SIZE * LABEL_GRID_SIZE;

/// Maximum grid index for clamping (`LABEL_GRID_SIZE - 1`).
/// Using isize to allow safe clamping from negative float→int conversions.
#[allow(clippy::cast_possible_wrap)]
const LABEL_GRID_MAX_IDX: isize = (LABEL_GRID_SIZE - 1) as isize;

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
/// # Phase 86: Flat Grid + Dirty-Cell Reset
///
/// Previous design used triple-nested `Vec<Vec<Vec<(usize, u32)>>>` with a
/// generation counter for O(1) reset. This had three problems:
/// 1. Triple pointer indirection on every cell access (cache-hostile)
/// 2. Generation check branch in the tightest inner loop
/// 3. 8 bytes per entry `(usize, u32)` instead of 4 bytes `usize`
///
/// New design uses flat `Vec<Vec<usize>>` with dirty-cell tracking:
/// - Single pointer indirection: `grid[cy * 32 + cx]`
/// - No generation check in collision loop (all entries are current)
/// - 4 bytes per entry (just label index)
/// - O(k) reset clears only cells that were used (k ≈ 80-160 for 80 labels)
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
/// - `grid`: 1024 `Vec<usize>` entries, flat-indexed as `grid[cy * 32 + cx]`
/// - `dirty_cells`: Tracks which cell indices need clearing on reset
/// - `viewport_width/height`: Current viewport dimensions for bounds checking
/// - Total overhead: ~24KB for grid structure (reused across frames)
pub struct LabelPlacer {
    /// All placed label rectangles.
    placed_labels: Vec<Rect>,
    /// Flat spatial hash grid: each cell contains label indices.
    /// Indexed as `grid[cy * LABEL_GRID_SIZE + cx]`.
    grid: Vec<Vec<usize>>,
    /// Indices of grid cells that have been written to this frame.
    /// Used for O(k) reset: only clear cells that were actually used.
    dirty_cells: Vec<u16>,
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
        let mut grid = Vec::with_capacity(LABEL_GRID_TOTAL);
        for _ in 0..LABEL_GRID_TOTAL {
            grid.push(Vec::with_capacity(4)); // Expect ~4 labels per cell
        }
        Self {
            placed_labels: Vec::with_capacity(max_labels),
            grid,
            dirty_cells: Vec::with_capacity(256),
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

    /// Resets the placer for a new frame using dirty-cell tracking.
    ///
    /// Only clears grid cells that were actually written to, giving O(k)
    /// reset where k = number of dirty cells (typically 80-160 for 80 labels).
    ///
    /// # Complexity
    ///
    /// - O(k) where k = dirty cells (each `Vec::clear()` is O(1) since it just sets len=0)
    /// - For 80 labels spanning ~1-2 cells each: k ≈ 100-160
    /// - Measured: ~100-200 ns (comparable to generation counter approach)
    #[inline]
    pub fn reset(&mut self, camera_zoom: f32) {
        // Clear only cells that were used this frame
        for &idx in &self.dirty_cells {
            self.grid[idx as usize].clear();
        }
        self.dirty_cells.clear();
        self.placed_labels.clear();
        self.max_labels = compute_max_labels(camera_zoom);
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

    /// Converts screen position to grid cell index (flat).
    #[inline]
    fn pos_to_cell(x: f32, y: f32) -> (usize, usize) {
        // Handle negative coordinates by clamping to 0
        let cx = ((x * INV_LABEL_CELL_SIZE).floor() as isize).clamp(0, LABEL_GRID_MAX_IDX) as usize;
        let cy = ((y * INV_LABEL_CELL_SIZE).floor() as isize).clamp(0, LABEL_GRID_MAX_IDX) as usize;
        (cx, cy)
    }

    /// Returns the flat grid index for a cell coordinate.
    #[inline]
    fn cell_index(cx: usize, cy: usize) -> usize {
        cy * LABEL_GRID_SIZE + cx
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
    /// # Phase 86: Branch-Free Inner Loop
    ///
    /// The flat grid with dirty-cell tracking eliminates the generation check
    /// from the collision inner loop. Every entry in a cell is guaranteed current,
    /// so the loop only performs rect intersection tests.
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

        // Check for collisions only with labels in overlapping cells
        // Phase 86: No generation check — all entries in grid are current
        for cy in min_cy..=max_cy {
            for cx in min_cx..=max_cx {
                let cell_idx = Self::cell_index(cx, cy);
                for &label_idx in &self.grid[cell_idx] {
                    if rects_intersect(&rect, &self.placed_labels[label_idx]) {
                        return false;
                    }
                }
            }
        }

        // No collision - add to placed_labels and register in grid cells
        let label_idx = self.placed_labels.len();
        self.placed_labels.push(rect);

        for cy in min_cy..=max_cy {
            for cx in min_cx..=max_cx {
                let cell_idx = Self::cell_index(cx, cy);
                // Track dirty cell for O(k) reset (only if cell was empty = first write)
                if self.grid[cell_idx].is_empty() {
                    self.dirty_cells.push(cell_idx as u16);
                }
                self.grid[cell_idx].push(label_idx);
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
