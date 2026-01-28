// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Rendering phases for the Rource WASM visualization.
//!
//! This module splits the main render loop into focused phases for maintainability.
//! Each phase handles a specific aspect of rendering and can be tested independently.
//!
//! ## Module Structure
//!
//! - [`helpers`]: Pure computation functions (100% testable without renderer)
//! - [`label_placer`]: Spatial hash collision detection for label placement
//! - [`directories`]: Directory node and label rendering
//! - [`files`]: File node and label rendering
//! - [`users`]: User avatar and label rendering
//! - [`actions`]: Action beam rendering
//! - [`watermark`]: Watermark overlay rendering
//!
//! ## Level-of-Detail (LOD) Optimization
//!
//! To maintain high FPS regardless of repository size, we skip rendering entities
//! that would appear smaller than a certain threshold on screen. This is controlled
//! by the LOD constants imported from `rource_render::lod`.
//!
//! The screen radius of an entity is: `world_radius * camera_zoom`
//!
//! When this falls below the threshold, the entity is either:
//! - Skipped entirely (for very small entities)
//! - Rendered without labels (for medium-small entities)
//!
//! This provides significant performance gains for large repositories:
//! - At zoom=0.01 with 50,000 files, most files are sub-pixel and skipped
//! - Labels are the most expensive to render; skipping them has high impact

pub mod actions;
pub mod directories;
pub mod files;
pub mod helpers;
pub mod label_placer;
pub mod users;
pub mod watermark;

#[cfg(test)]
mod tests;

use rource_core::entity::DirId;
use rource_core::{FileId, UserId};
use rource_math::Bounds;
use rource_render::FontId;

// Re-export commonly used items for convenience
pub use actions::render_actions;
pub use directories::{render_directories, render_directory_labels};
pub use files::{render_file_labels, render_files};
#[allow(unused_imports)]
pub use helpers::*;
pub use label_placer::LabelPlacer;
pub use users::{render_user_labels, render_users};
pub use watermark::render_watermark;

// Re-export AUTO_FIT_MIN_ZOOM for external use (used by camera auto-fit)
pub use rource_render::lod::AUTO_FIT_MIN_ZOOM;

/// Monospace character width factor for Roboto Mono.
///
/// Measured value is 0.6001 (`advance_width` / `font_size`).
/// We use 0.62 to add a 3% safety margin for:
/// - Subpixel rendering differences
/// - Minor font hinting variations
/// - Rounding errors in collision detection
const MONOSPACE_WIDTH_FACTOR: f32 = 0.62;

/// Estimates text width for label placement.
///
/// This function uses the actual character count (not byte count) and the
/// measured monospace width factor for Roboto Mono.
///
/// # Accuracy
///
/// | Input Type | Accuracy |
/// |------------|----------|
/// | ASCII text | ~3% overestimate (safety margin) |
/// | UTF-8 text | ~3% overestimate (safety margin) |
/// | CJK/Emoji  | ~3% overestimate (safety margin) |
///
/// Previous approach used `text.len()` (bytes) with factor 0.75, which caused:
/// - ASCII: 25% overestimate
/// - UTF-8 accented: up to 50% overestimate
/// - CJK/Emoji: up to 400% overestimate
///
/// # Phase 68 Optimization
///
/// Changed from `text.len() * 0.75` to `text.chars().count() * 0.62`:
/// - Uses character count instead of byte count (correct for UTF-8)
/// - Uses measured font factor (0.60) + 3% safety margin (0.62)
/// - Reduces average estimation error from 74.4% to 3%
#[inline]
pub fn estimate_text_width(text: &str, font_size: f32) -> f32 {
    text.chars().count() as f32 * font_size * MONOSPACE_WIDTH_FACTOR
}

/// Context shared between rendering phases.
///
/// This struct is passed to all rendering phase functions to provide
/// shared state and configuration without needing to pass many parameters.
/// Render context containing visibility data for a single frame.
///
/// Uses borrowed slices instead of owned Vecs to enable zero-allocation
/// rendering when combined with reusable visibility buffers.
#[allow(dead_code)] // Fields may be used by future phases
pub struct RenderContext<'a> {
    /// Visible bounds in world space (for culling extensions).
    pub visible_bounds: Bounds,
    /// Camera zoom level.
    pub camera_zoom: f32,
    /// Whether to use curved branches.
    pub use_curves: bool,
    /// Visible directory IDs (borrowed from reusable buffer).
    pub visible_dirs: &'a [DirId],
    /// Visible file IDs (borrowed from reusable buffer).
    pub visible_files: &'a [FileId],
    /// Visible user IDs (borrowed from reusable buffer).
    pub visible_users: &'a [UserId],
    /// Whether labels are enabled.
    pub show_labels: bool,
    /// Font ID for text rendering.
    pub font_id: Option<FontId>,
    /// Font size for labels.
    pub font_size: f32,
    /// Opacity falloff rate for branch lines based on depth.
    /// Higher values make deep branches fade faster (0.0-1.0).
    pub branch_depth_fade: f32,
    /// Maximum opacity for directory-to-parent branch lines (0.0-1.0).
    pub branch_opacity_max: f32,
}

/// Rendering statistics (for future performance monitoring).
#[allow(dead_code)] // Reserved for future phase-level instrumentation
#[derive(Debug, Default, Clone)]
pub struct PhaseStats {
    /// Number of visible files.
    pub visible_files: usize,
    /// Number of visible users.
    pub visible_users: usize,
    /// Number of visible directories.
    pub visible_directories: usize,
    /// Number of active actions.
    pub active_actions: usize,
    /// Total entity count.
    pub total_entities: usize,
    /// Estimated draw calls.
    pub draw_calls: usize,
}
