// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Rendering phases for the Rource WASM visualization.
//!
//! This module splits the main render loop into focused phases for maintainability.
//! Each phase handles a specific aspect of rendering and can be tested independently.
//!
//! ## Level-of-Detail (LOD) Optimization
//!
//! To maintain high FPS regardless of repository size, we skip rendering entities
//! that would appear smaller than a certain threshold on screen. This is controlled
//! by the `LOD_*` constants below.
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

use rource_core::config::{WatermarkPosition, WatermarkSettings};
use rource_core::entity::DirId;
use rource_core::{FileId, UserId};
use rource_math::{Bounds, Color, Rect, Vec2};
use rource_render::{FontId, Renderer};

// Import shared LOD constants from rource-render for visual parity with CLI
use rource_render::lod::{
    MIN_DIR_LABEL_RADIUS as LOD_MIN_DIR_LABEL_RADIUS, MIN_DIR_RADIUS as LOD_MIN_DIR_RADIUS,
    MIN_FILE_LABEL_RADIUS as LOD_MIN_FILE_LABEL_RADIUS, MIN_FILE_RADIUS as LOD_MIN_FILE_RADIUS,
    MIN_USER_LABEL_RADIUS as LOD_MIN_USER_LABEL_RADIUS, MIN_USER_RADIUS as LOD_MIN_USER_RADIUS,
    MIN_ZOOM_FOR_DIR_BRANCHES as LOD_MIN_ZOOM_FOR_DIR_BRANCHES,
    MIN_ZOOM_FOR_FILE_BRANCHES as LOD_MIN_ZOOM_FOR_FILE_BRANCHES,
};

use crate::rendering::{draw_action_beam, draw_avatar_shape, draw_curved_branch};

// =============================================================================
// Pure Computation Functions (100% testable without renderer)
// =============================================================================
// These functions encapsulate all rendering logic as pure computations.
// They take input data and return computed values without side effects.

// These pure functions are extracted for unit testing. They are not called directly
// from the main render code, which uses optimized inline versions.
#[allow(dead_code)]
#[allow(clippy::wildcard_imports)]
mod helpers {
    use super::*;

    /// Precomputed reciprocal for depth factor calculation (1.0 / 6.0).
    const INV_DEPTH_MAX: f32 = 1.0 / 6.0;

    /// Computes the depth factor used for depth-based styling.
    ///
    /// The depth factor is normalized to [0.0, 1.0] where 0 is root and 1.0 is
    /// a directory at depth 6 or greater.
    ///
    /// # Arguments
    /// * `depth` - Directory depth (0 = root)
    ///
    /// # Returns
    /// Normalized depth factor in range [0.0, 1.0].
    #[inline]
    #[must_use]
    pub fn compute_depth_factor(depth: u32) -> f32 {
        (depth as f32 * INV_DEPTH_MAX).min(1.0)
    }

    /// Computes directory color based on depth.
    ///
    /// Deeper directories are rendered with lower brightness to create
    /// visual hierarchy and reduce clutter.
    ///
    /// # Arguments
    /// * `depth` - Directory depth (0 = root)
    ///
    /// # Returns
    /// Color for the directory node.
    #[inline]
    #[must_use]
    pub fn compute_directory_color(depth: u32) -> Color {
        let depth_factor = compute_depth_factor(depth);
        let base_brightness = 0.25 + 0.1 * (1.0 - depth_factor);
        Color::new(
            base_brightness * 0.9,
            base_brightness,
            base_brightness * 1.1 + 0.05,
            0.55,
        )
    }

    /// Computes branch line width based on directory depth.
    ///
    /// Deeper directories have thinner branches to reduce visual noise.
    ///
    /// # Arguments
    /// * `depth` - Directory depth (0 = root)
    ///
    /// # Returns
    /// Branch width in pixels.
    #[inline]
    #[must_use]
    pub fn compute_branch_width(depth: u32) -> f32 {
        let depth_factor = compute_depth_factor(depth);
        (1.5 - depth_factor * 0.5).max(0.8)
    }

    /// Computes branch opacity with depth-based fade.
    ///
    /// Deeper branches fade to reduce visual clutter while maintaining
    /// structure visibility.
    ///
    /// # Arguments
    /// * `depth` - Directory depth (0 = root)
    /// * `max_opacity` - Maximum opacity for branches (0.0-1.0)
    /// * `fade_rate` - How quickly opacity fades with depth (0.0-1.0)
    ///
    /// # Returns
    /// Branch opacity in range \[0.05, `max_opacity`\].
    #[inline]
    #[must_use]
    pub fn compute_branch_opacity(depth: u32, max_opacity: f32, fade_rate: f32) -> f32 {
        let depth_factor = compute_depth_factor(depth);
        max_opacity * (1.0 - depth_factor * fade_rate).max(0.05)
    }

    /// Computes branch color from directory color with opacity adjustment.
    ///
    /// # Arguments
    /// * `dir_color` - Base directory color
    /// * `opacity` - Computed branch opacity
    ///
    /// # Returns
    /// Branch color with slight brightness boost and specified opacity.
    #[inline]
    #[must_use]
    pub fn compute_branch_color(dir_color: Color, opacity: f32) -> Color {
        Color::new(
            dir_color.r * 1.1,
            dir_color.g * 1.1,
            dir_color.b * 1.2,
            opacity,
        )
    }

    /// Determines if a directory should be rendered based on LOD.
    ///
    /// Root directory (depth 0) is always rendered as it's the anchor point.
    /// Other directories are culled when their screen radius is below threshold.
    ///
    /// # Arguments
    /// * `screen_radius` - Radius in screen pixels
    /// * `depth` - Directory depth (0 = root)
    ///
    /// # Returns
    /// `true` if the directory should be rendered.
    #[inline]
    #[must_use]
    pub fn should_render_directory(screen_radius: f32, depth: u32) -> bool {
        depth == 0 || screen_radius >= LOD_MIN_DIR_RADIUS
    }

    /// Determines if a file should be rendered based on LOD.
    ///
    /// # Arguments
    /// * `screen_radius` - Radius in screen pixels
    /// * `alpha` - File alpha (0.0-1.0)
    ///
    /// # Returns
    /// `true` if the file should be rendered.
    #[inline]
    #[must_use]
    pub fn should_render_file(screen_radius: f32, alpha: f32) -> bool {
        alpha >= 0.01 && screen_radius >= LOD_MIN_FILE_RADIUS
    }

    /// Determines if a user should be rendered based on LOD.
    ///
    /// # Arguments
    /// * `screen_radius` - Radius in screen pixels
    /// * `alpha` - User alpha (0.0-1.0)
    ///
    /// # Returns
    /// `true` if the user should be rendered.
    #[inline]
    #[must_use]
    pub fn should_render_user(screen_radius: f32, alpha: f32) -> bool {
        alpha >= 0.01 && screen_radius >= LOD_MIN_USER_RADIUS
    }

    /// Determines if a directory label should be rendered based on LOD.
    ///
    /// # Arguments
    /// * `screen_radius` - Radius in screen pixels
    /// * `depth` - Directory depth
    ///
    /// # Returns
    /// `true` if the label should be rendered.
    #[inline]
    #[must_use]
    pub fn should_render_directory_label(screen_radius: f32, depth: u32) -> bool {
        depth <= 2 && screen_radius >= LOD_MIN_DIR_LABEL_RADIUS
    }

    /// Determines if a file label should be rendered based on LOD.
    ///
    /// # Arguments
    /// * `screen_radius` - Radius in screen pixels
    /// * `alpha` - File alpha
    /// * `camera_zoom` - Current camera zoom level
    ///
    /// # Returns
    /// `true` if the label should be rendered.
    #[inline]
    #[must_use]
    pub fn should_render_file_label(screen_radius: f32, alpha: f32, camera_zoom: f32) -> bool {
        alpha >= 0.3 && camera_zoom > 0.15 && screen_radius >= LOD_MIN_FILE_LABEL_RADIUS
    }

    /// Determines if a user label should be rendered based on LOD.
    ///
    /// # Arguments
    /// * `screen_radius` - Radius in screen pixels
    /// * `alpha` - User alpha
    ///
    /// # Returns
    /// `true` if the label should be rendered.
    #[inline]
    #[must_use]
    pub fn should_render_user_label(screen_radius: f32, alpha: f32) -> bool {
        alpha >= 0.01 && screen_radius >= LOD_MIN_USER_LABEL_RADIUS
    }

    /// Determines if directory-to-parent branches should be rendered.
    ///
    /// # Arguments
    /// * `camera_zoom` - Current camera zoom level
    ///
    /// # Returns
    /// `true` if branches should be rendered.
    #[inline]
    #[must_use]
    pub fn should_render_directory_branches(camera_zoom: f32) -> bool {
        camera_zoom >= LOD_MIN_ZOOM_FOR_DIR_BRANCHES
    }

    /// Determines if file-to-directory branches should be rendered.
    ///
    /// # Arguments
    /// * `camera_zoom` - Current camera zoom level
    ///
    /// # Returns
    /// `true` if branches should be rendered.
    #[inline]
    #[must_use]
    pub fn should_render_file_branches(camera_zoom: f32) -> bool {
        camera_zoom >= LOD_MIN_ZOOM_FOR_FILE_BRANCHES
    }

    /// Computes the effective render radius for a file.
    ///
    /// Files have a minimum render size to remain visible.
    ///
    /// # Arguments
    /// * `screen_radius` - Raw screen radius
    ///
    /// # Returns
    /// Effective radius (at least 2.0 pixels).
    #[inline]
    #[must_use]
    pub fn compute_file_effective_radius(screen_radius: f32) -> f32 {
        screen_radius.max(2.0)
    }

    /// Computes the effective render radius for a user.
    ///
    /// Users have a minimum render size to remain visible.
    ///
    /// # Arguments
    /// * `screen_radius` - Raw screen radius
    ///
    /// # Returns
    /// Effective radius (at least 5.0 pixels).
    #[inline]
    #[must_use]
    pub fn compute_user_effective_radius(screen_radius: f32) -> f32 {
        screen_radius.max(5.0)
    }

    /// Computes file glow intensity based on touch state.
    ///
    /// Recently touched files have a brighter glow.
    ///
    /// # Arguments
    /// * `is_touched` - Whether the file was recently modified
    ///
    /// # Returns
    /// Glow intensity multiplier.
    #[inline]
    #[must_use]
    pub fn compute_file_glow_intensity(is_touched: bool) -> f32 {
        if is_touched {
            0.25
        } else {
            0.08
        }
    }

    /// Computes file border color from main color.
    ///
    /// Border is a darker version of the main color.
    ///
    /// # Arguments
    /// * `color` - Main file color
    ///
    /// # Returns
    /// Border color (60% brightness of main).
    #[inline]
    #[must_use]
    pub fn compute_file_border_color(color: Color) -> Color {
        Color::new(color.r * 0.6, color.g * 0.6, color.b * 0.6, color.a)
    }

    /// Computes file branch color with depth-based opacity.
    ///
    /// # Arguments
    /// * `color` - File color
    /// * `alpha` - File alpha
    /// * `depth` - Parent directory depth
    /// * `branch_depth_fade` - Fade rate for depth
    ///
    /// # Returns
    /// Branch color with computed opacity.
    #[inline]
    #[must_use]
    pub fn compute_file_branch_color(
        color: Color,
        alpha: f32,
        depth: u32,
        branch_depth_fade: f32,
    ) -> Color {
        let depth_factor = compute_depth_factor(depth);
        let depth_opacity = (1.0 - depth_factor * branch_depth_fade).max(0.05);
        Color::new(
            color.r * 0.7,
            color.g * 0.7,
            color.b * 0.7,
            0.25 * alpha * depth_opacity,
        )
    }

    /// Computes label position relative to an entity.
    ///
    /// # Arguments
    /// * `screen_pos` - Entity screen position
    /// * `radius` - Entity screen radius
    /// * `font_size` - Label font size
    /// * `offset_x` - Horizontal offset from entity edge
    ///
    /// # Returns
    /// Label position.
    #[inline]
    #[must_use]
    pub fn compute_label_position(
        screen_pos: Vec2,
        radius: f32,
        font_size: f32,
        offset_x: f32,
    ) -> Vec2 {
        Vec2::new(
            screen_pos.x + radius + offset_x,
            screen_pos.y - font_size * 0.3,
        )
    }

    /// Computes file label priority for sorting.
    ///
    /// Higher priority labels are rendered first in collision avoidance.
    ///
    /// # Arguments
    /// * `radius` - File world radius
    /// * `alpha` - File alpha
    /// * `is_touched` - Whether file was recently modified
    ///
    /// # Returns
    /// Priority score (higher = more important).
    #[inline]
    #[must_use]
    pub fn compute_file_label_priority(radius: f32, alpha: f32, is_touched: bool) -> f32 {
        let activity_bonus = if is_touched { 100.0 } else { 0.0 };
        radius * alpha * 10.0 + activity_bonus
    }

    /// Computes adaptive max labels based on zoom level.
    ///
    /// At higher zoom, more labels can be displayed without clutter.
    ///
    /// # Arguments
    /// * `camera_zoom` - Current camera zoom level
    ///
    /// # Returns
    /// Maximum number of labels to render.
    #[inline]
    #[must_use]
    pub fn compute_max_labels(camera_zoom: f32) -> usize {
        if camera_zoom > 1.0 {
            200
        } else if camera_zoom > 0.5 {
            100
        } else {
            50
        }
    }

    /// Computes watermark base position based on corner placement.
    ///
    /// # Arguments
    /// * `position` - Watermark corner position
    /// * `margin` - Margin from screen edge
    /// * `text_width` - Maximum text width
    /// * `total_height` - Total height of watermark text
    /// * `screen_width` - Screen width
    /// * `screen_height` - Screen height
    ///
    /// # Returns
    /// (x, y) base position for the watermark.
    #[inline]
    #[must_use]
    pub fn compute_watermark_position(
        position: WatermarkPosition,
        margin: f32,
        text_width: f32,
        total_height: f32,
        screen_width: f32,
        screen_height: f32,
    ) -> (f32, f32) {
        match position {
            WatermarkPosition::TopLeft => (margin, margin),
            WatermarkPosition::TopRight => (screen_width - text_width - margin, margin),
            WatermarkPosition::BottomLeft => (margin, screen_height - total_height - margin),
            WatermarkPosition::BottomRight => (
                screen_width - text_width - margin,
                screen_height - total_height - margin,
            ),
        }
    }

    /// Computes watermark total height based on whether subtext is present.
    ///
    /// # Arguments
    /// * `font_size` - Primary text font size
    /// * `has_subtext` - Whether there is subtext
    ///
    /// # Returns
    /// Total height of watermark.
    #[inline]
    #[must_use]
    pub fn compute_watermark_height(font_size: f32, has_subtext: bool) -> f32 {
        if has_subtext {
            font_size * 1.2 + font_size * 0.85
        } else {
            font_size
        }
    }
}

// Re-export helpers for tests
#[allow(unused_imports)]
pub use helpers::*;

// =============================================================================
// Level-of-Detail (LOD) Constants
// =============================================================================
// LOD constants are now imported from rource_render::lod at the top of this file
// to ensure visual parity between CLI and WASM renderers. See that module for
// detailed documentation on each threshold.
//
// Re-export AUTO_FIT_MIN_ZOOM for external use (used by camera auto-fit)
pub use rource_render::lod::AUTO_FIT_MIN_ZOOM;

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

/// Renders directory nodes with enhanced styling.
///
/// Applies LOD (Level-of-Detail) optimization:
/// - Directories with screen radius < `LOD_MIN_DIR_RADIUS` are skipped
/// - Directory-to-parent branches are skipped when zoom < `LOD_MIN_ZOOM_FOR_DIR_BRANCHES`
#[inline(never)] // Prevent inlining for better profiling
pub fn render_directories<R: Renderer + ?Sized>(
    renderer: &mut R,
    ctx: &RenderContext,
    scene: &rource_core::Scene,
    camera: &rource_core::Camera,
) {
    // Pre-compute whether we should render directory branches at this zoom level
    let render_branches = should_render_directory_branches(ctx.camera_zoom);

    for dir_id in ctx.visible_dirs {
        if let Some(dir) = scene.directories().get(*dir_id) {
            if !dir.is_visible() {
                continue;
            }

            let screen_pos = camera.world_to_screen(dir.position());
            let radius = dir.radius() * ctx.camera_zoom;
            let depth = dir.depth();

            // LOD: Skip directories that are too small to be visible
            if !should_render_directory(radius, depth) {
                continue;
            }

            // Compute colors using pure functions
            let dir_color = compute_directory_color(depth);
            let glow_color = dir_color.with_alpha(0.1);
            let center_color = dir_color.with_alpha(0.4);

            // Draw soft glow behind directory node
            renderer.draw_disc(screen_pos, radius * 1.5, glow_color);

            // Draw directory as a hollow circle
            renderer.draw_circle(screen_pos, radius, 1.5, dir_color);

            // Small filled center dot
            renderer.draw_disc(screen_pos, radius * 0.25, center_color);

            // Draw connection to parent with curved branches
            if render_branches {
                if let Some(parent_pos) = dir.parent_position() {
                    let parent_screen = camera.world_to_screen(parent_pos);

                    // Compute branch properties using pure functions
                    let branch_width = compute_branch_width(depth);
                    let depth_opacity = compute_branch_opacity(
                        depth,
                        ctx.branch_opacity_max,
                        ctx.branch_depth_fade,
                    );
                    let branch_color = compute_branch_color(dir_color, depth_opacity);

                    draw_curved_branch(
                        renderer,
                        parent_screen,
                        screen_pos,
                        branch_width,
                        branch_color,
                        ctx.use_curves,
                    );
                }
            }
        }
    }
}

/// Renders directory labels (separate from nodes for layering).
///
/// Applies LOD (Level-of-Detail) optimization:
/// - Labels are skipped when screen radius < `LOD_MIN_DIR_LABEL_RADIUS`
/// - Labels are skipped for deep directories (depth > 2)
#[inline(never)]
pub fn render_directory_labels<R: Renderer + ?Sized>(
    renderer: &mut R,
    ctx: &RenderContext,
    scene: &rource_core::Scene,
    camera: &rource_core::Camera,
) {
    if !ctx.show_labels {
        return;
    }

    let Some(font_id) = ctx.font_id else { return };

    let dir_font_size = ctx.font_size * 0.75;

    for dir_id in ctx.visible_dirs {
        if let Some(dir) = scene.directories().get(*dir_id) {
            if !dir.is_visible() {
                continue;
            }

            // Only show for shallow directories (depth <= 2) to avoid clutter
            if dir.depth() > 2 {
                continue;
            }

            let name = dir.name();
            if name.is_empty() {
                continue;
            }

            let screen_pos = camera.world_to_screen(dir.position());
            let radius = dir.radius() * ctx.camera_zoom;

            // LOD: Skip labels for directories that are too small on screen
            // Labels on tiny nodes would be unreadable anyway
            if radius < LOD_MIN_DIR_LABEL_RADIUS {
                continue;
            }

            let label_pos = Vec2::new(
                screen_pos.x + radius + 4.0,
                screen_pos.y - dir_font_size * 0.3,
            );

            // Shadow for better readability
            let shadow_color = Color::new(0.0, 0.0, 0.0, 0.4);
            renderer.draw_text(
                name,
                label_pos + Vec2::new(1.0, 1.0),
                font_id,
                dir_font_size,
                shadow_color,
            );

            // Main label in soft blue-gray
            let label_color = Color::new(0.75, 0.78, 0.85, 0.7);
            renderer.draw_text(name, label_pos, font_id, dir_font_size, label_color);
        }
    }
}

/// Renders file nodes with enhanced styling.
///
/// Applies LOD (Level-of-Detail) optimization:
/// - Files with screen radius < `LOD_MIN_FILE_RADIUS` are skipped entirely
/// - File-to-directory branches are skipped when zoom < `LOD_MIN_ZOOM_FOR_FILE_BRANCHES`
#[inline(never)]
pub fn render_files<R: Renderer + ?Sized>(
    renderer: &mut R,
    ctx: &RenderContext,
    scene: &rource_core::Scene,
    camera: &rource_core::Camera,
) {
    // Pre-compute whether we should render file branches at this zoom level
    let render_branches = should_render_file_branches(ctx.camera_zoom);

    for file_id in ctx.visible_files {
        if let Some(file) = scene.get_file(*file_id) {
            let alpha = file.alpha();
            let screen_pos = camera.world_to_screen(file.position());
            let radius = file.radius() * ctx.camera_zoom;

            // LOD: Skip files that are too small or invisible
            if !should_render_file(radius, alpha) {
                continue;
            }

            let color = file.current_color().with_alpha(alpha);
            let effective_radius = compute_file_effective_radius(radius);

            // Draw connection to parent directory first (behind file)
            if render_branches {
                if let Some(dir) = scene.directories().get(file.directory()) {
                    let dir_screen = camera.world_to_screen(dir.position());
                    let branch_color =
                        compute_file_branch_color(color, alpha, dir.depth(), ctx.branch_depth_fade);

                    draw_curved_branch(
                        renderer,
                        dir_screen,
                        screen_pos,
                        0.8,
                        branch_color,
                        ctx.use_curves,
                    );
                }
            }

            // Draw soft glow behind file ONLY for touched files
            // Optimization: Skip glow for inactive files (~97% of files)
            let is_touched = file.touch_time() > 0.0;
            if is_touched {
                let glow_color = color.with_alpha(0.25 * alpha);
                renderer.draw_disc(screen_pos, effective_radius * 2.0, glow_color);
            }

            // Outer ring (darker border)
            let border_color = compute_file_border_color(color);
            renderer.draw_disc(screen_pos, effective_radius + 0.5, border_color);

            // Main file icon/disc - use file icons if available, otherwise colored disc
            let icon_size = effective_radius * 2.0;
            if let Some(ext) = file.extension() {
                renderer.draw_file_icon(screen_pos, icon_size, ext, color);
            } else {
                renderer.draw_disc(screen_pos, effective_radius, color);
            }

            // Bright highlight for active/touched files
            if is_touched {
                let highlight = Color::new(1.0, 1.0, 1.0, 0.3 * alpha);
                renderer.draw_disc(screen_pos, effective_radius * 0.5, highlight);
            }
        }
    }
}

/// Maximum number of concurrent action beams to render.
///
/// # V1: Beam Animation Choreography
///
/// Limiting concurrent beams prevents visual chaos when many files are
/// modified simultaneously. The limit is chosen to:
/// - Keep the visualization readable (not overwhelming)
/// - Show enough activity to convey repository activity
/// - Prioritize active user's actions
const MAX_CONCURRENT_BEAMS: usize = 15;

/// Renders action beams from users to files.
///
/// # V1: Beam Animation Choreography
///
/// To prevent visual chaos when many files are modified simultaneously,
/// beams are:
/// 1. Limited to `MAX_CONCURRENT_BEAMS` (15) at a time
/// 2. Sorted by priority (newer actions first, as they're more visually important)
/// 3. The natural stagger comes from actions starting at different simulation times
///
/// This creates a more pleasing visual effect where beams appear in waves
/// rather than all at once.
#[inline(never)]
pub fn render_actions<R: Renderer + ?Sized>(
    renderer: &mut R,
    ctx: &RenderContext,
    scene: &rource_core::Scene,
    camera: &rource_core::Camera,
) {
    // Collect active actions with their indices
    // V1: We'll prioritize by progress (newer beams = lower progress first)
    let mut active_indices: Vec<(usize, f32)> = scene
        .actions()
        .iter()
        .enumerate()
        .filter(|(_, a)| !a.is_complete())
        .map(|(i, a)| (i, a.progress()))
        .collect();

    // V1: Limit concurrent beams to prevent visual chaos
    // OPTIMIZATION: Use select_nth_unstable for O(n) partial selection instead of O(n log n) sort
    // This partitions the array so elements [0..beam_limit] are the smallest (unordered)
    let beam_limit = MAX_CONCURRENT_BEAMS.min(active_indices.len());
    if beam_limit > 0 && beam_limit < active_indices.len() {
        // Partial sort: only need the smallest `beam_limit` elements
        active_indices.select_nth_unstable_by(beam_limit - 1, |a, b| {
            a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal)
        });
    }
    let actions_slice = scene.actions();

    for (idx, _progress) in active_indices.into_iter().take(beam_limit) {
        let action = &actions_slice[idx];
        let user_opt = scene.get_user(action.user());
        let file_opt = scene.get_file(action.file());

        if let (Some(user), Some(file)) = (user_opt, file_opt) {
            let user_screen = camera.world_to_screen(user.position());
            let file_screen = camera.world_to_screen(file.position());
            let beam_color = action.beam_color();

            draw_action_beam(
                renderer,
                user_screen,
                file_screen,
                action.progress(),
                beam_color,
                ctx.camera_zoom,
            );
        }
    }
}

/// Renders user avatar shapes.
///
/// Applies LOD (Level-of-Detail) optimization:
/// - Users with screen radius < `LOD_MIN_USER_RADIUS` are skipped
/// - Users are important visual landmarks, so threshold is kept low
#[inline(never)]
pub fn render_users<R: Renderer + ?Sized>(
    renderer: &mut R,
    ctx: &RenderContext,
    scene: &rource_core::Scene,
    camera: &rource_core::Camera,
) {
    for user_id in ctx.visible_users {
        if let Some(user) = scene.get_user(*user_id) {
            let alpha = user.alpha();
            let screen_pos = camera.world_to_screen(user.position());
            let raw_radius = user.radius() * ctx.camera_zoom;

            // LOD: Skip users that are too small or invisible
            if !should_render_user(raw_radius, alpha) {
                continue;
            }

            let radius = compute_user_effective_radius(raw_radius);
            let color = user.display_color();

            draw_avatar_shape(renderer, screen_pos, radius, color, user.is_active(), alpha);
        }
    }
}

/// Renders user name labels.
///
/// Renders user labels with collision detection.
///
/// # T1/T5: Label Collision Detection
///
/// User labels now use the same `LabelPlacer` as file labels to prevent
/// overlapping text. Labels are placed using `try_place_with_fallback` which
/// tries multiple positions (right, left, above, below) if the primary position
/// is blocked.
///
/// # Priority
///
/// Users are sorted by radius * alpha (visibility) so that prominent users
/// get their labels placed first. Smaller/faded users may have labels skipped
/// if there's no room.
///
/// # Arguments
///
/// * `label_candidates` - Reusable buffer for label candidates (avoids per-frame allocation).
///   Will be cleared and repopulated each frame.
/// * `label_placer` - Reusable label placer for collision avoidance.
///   Should be reset before calling this function if starting a new frame.
///   Pass the same placer to `render_file_labels` to ensure user and file
///   labels don't overlap.
///
/// # LOD Optimization
///
/// Labels are skipped when screen radius < `LOD_MIN_USER_LABEL_RADIUS`
#[inline(never)]
pub fn render_user_labels<R: Renderer + ?Sized>(
    renderer: &mut R,
    ctx: &RenderContext,
    scene: &rource_core::Scene,
    camera: &rource_core::Camera,
    label_candidates: &mut Vec<(UserId, Vec2, f32, f32, f32)>,
    label_placer: &mut LabelPlacer,
) {
    if !ctx.show_labels {
        return;
    }

    let Some(font_id) = ctx.font_id else { return };

    // Collect user label candidates with priority (reuses buffer to avoid per-frame allocation)
    // Higher priority users get their labels placed first
    label_candidates.clear();

    for user_id in ctx.visible_users {
        if let Some(user) = scene.get_user(*user_id) {
            let alpha = user.alpha();
            let screen_pos = camera.world_to_screen(user.position());
            let raw_radius = user.radius() * ctx.camera_zoom;

            // LOD: Skip labels for users that are too small or invisible
            if !should_render_user_label(raw_radius, alpha) {
                continue;
            }

            let radius = compute_user_effective_radius(raw_radius);
            // Priority based on visibility (larger, more visible users first)
            let priority = radius * alpha;

            label_candidates.push((*user_id, screen_pos, radius, alpha, priority));
        }
    }

    // OPTIMIZATION: Use select_nth_unstable for O(n) partial selection instead of O(n log n) sort
    // We only need the top max_labels candidates, not a fully sorted list.
    // The selected candidates are not in sorted order, but this is acceptable
    // since spatial hash collision detection handles label placement priority.
    let max_labels = label_placer.max_labels();
    let select_count = max_labels.min(label_candidates.len());
    if select_count > 0 && select_count < label_candidates.len() {
        // Partition so [0..select_count] contains highest priority (unordered)
        // Note: select_nth_unstable_by finds nth smallest, so we use reversed comparison
        label_candidates.select_nth_unstable_by(select_count - 1, |a, b| {
            b.4.partial_cmp(&a.4).unwrap_or(std::cmp::Ordering::Equal)
        });
    }

    for &(user_id, screen_pos, radius, alpha, _priority) in
        label_candidates.iter().take(select_count)
    {
        if !label_placer.can_place_more() {
            break;
        }

        let Some(user) = scene.get_user(user_id) else {
            continue;
        };
        let name = user.name();

        // Calculate label dimensions
        let text_width = estimate_text_width(name, ctx.font_size);
        let text_height = ctx.font_size;

        // Primary position: right of the user avatar
        let primary_pos = Vec2::new(
            screen_pos.x + radius + 5.0,
            screen_pos.y - ctx.font_size * 0.3,
        );

        // T1/T5: Try to place with fallback positions (right, left, above, below)
        if let Some(label_pos) = label_placer.try_place_with_fallback(
            primary_pos,
            text_width,
            text_height,
            screen_pos,
            radius,
        ) {
            // Shadow for better readability
            let shadow_color = Color::new(0.0, 0.0, 0.0, 0.5 * alpha);
            renderer.draw_text(
                name,
                label_pos + Vec2::new(1.0, 1.0),
                font_id,
                ctx.font_size,
                shadow_color,
            );

            let label_color = Color::new(1.0, 1.0, 1.0, 0.9 * alpha);
            renderer.draw_text(name, label_pos, font_id, ctx.font_size, label_color);
        }
    }
}

/// Estimates text width for label placement.
///
/// Uses a conservative factor of 0.75 to account for:
/// - Wide characters (M, W, m, w)
/// - Variable-width fonts
/// - Unicode characters that may render wider
///
/// The factor is intentionally larger than typical monospace (0.5-0.6)
/// to reduce label collision false negatives (overlap despite detection).
#[inline]
fn estimate_text_width(text: &str, font_size: f32) -> f32 {
    text.len() as f32 * font_size * 0.75
}

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
fn rects_intersect(a: &Rect, b: &Rect) -> bool {
    a.x < b.x + b.width && a.x + a.width > b.x && a.y < b.y + b.height && a.y + a.height > b.y
}

/// Renders file name labels with collision avoidance.
///
/// # T1/T5: Label Collision Detection
///
/// File labels use the shared `LabelPlacer` which may already contain user labels.
/// This ensures file labels don't overlap user labels. The placer should be reset
/// BEFORE `render_user_labels` is called, not here.
///
/// Applies LOD (Level-of-Detail) optimization:
/// - Labels are skipped when camera zoom is too low (< 0.15)
/// - Labels are skipped for files with screen radius < `LOD_MIN_FILE_LABEL_RADIUS`
/// - Label collision avoidance limits total labels rendered
///
/// # Arguments
///
/// * `label_candidates` - Reusable buffer for label candidates (avoids per-frame allocation).
///   Will be cleared and repopulated each frame.
/// * `label_placer` - Reusable label placer for collision avoidance (avoids per-frame Vec allocation).
///   Should be reset by the caller before rendering the first labels of the frame.
///   Do NOT reset here - user labels may already be placed.
#[inline(never)]
pub fn render_file_labels<R: Renderer + ?Sized>(
    renderer: &mut R,
    ctx: &RenderContext,
    scene: &rource_core::Scene,
    camera: &rource_core::Camera,
    label_candidates: &mut Vec<(FileId, Vec2, f32, f32, f32)>,
    label_placer: &mut LabelPlacer,
) {
    if !ctx.show_labels || ctx.camera_zoom <= 0.15 {
        return;
    }

    let Some(font_id) = ctx.font_id else { return };

    let file_font_size = ctx.font_size * 0.8;

    // Collect label candidates with priority (reuses buffer to avoid per-frame allocation)
    // LOD: Only consider files large enough on screen for readable labels
    label_candidates.clear();
    for file_id in ctx.visible_files {
        if let Some(file) = scene.get_file(*file_id) {
            if file.alpha() < 0.3 {
                continue;
            }

            let screen_pos = camera.world_to_screen(file.position());
            let raw_radius = file.radius() * ctx.camera_zoom;

            // LOD: Skip labels for files that are too small on screen
            // Labels would be unreadable at this size anyway
            if raw_radius < LOD_MIN_FILE_LABEL_RADIUS {
                continue;
            }

            let radius = raw_radius.max(2.0);
            let is_touched = file.touch_time() > 0.0;

            // Priority based on visibility and activity
            let activity_bonus = if is_touched { 100.0 } else { 0.0 };
            let priority = file.radius() * file.alpha() * 10.0 + activity_bonus;

            // Store FileId instead of &str to allow buffer reuse across frames
            label_candidates.push((*file_id, screen_pos, radius, file.alpha(), priority));
        }
    }

    // OPTIMIZATION: Use select_nth_unstable for O(n) partial selection instead of O(n log n) sort
    // We only need candidates up to remaining label capacity (max_labels - already_placed).
    // Note: label_placer is NOT reset here - user labels may already be placed.
    let remaining_capacity = label_placer.remaining_capacity();
    let select_count = remaining_capacity.min(label_candidates.len());
    if select_count > 0 && select_count < label_candidates.len() {
        // Partition so [0..select_count] contains highest priority (unordered)
        label_candidates.select_nth_unstable_by(select_count - 1, |a, b| {
            b.4.partial_cmp(&a.4).unwrap_or(std::cmp::Ordering::Equal)
        });
    }

    for (file_id, screen_pos, radius, alpha, _priority) in
        label_candidates.iter().take(select_count)
    {
        if !label_placer.can_place_more() {
            break;
        }

        // Look up file name (O(1) HashMap lookup - trade-off for avoiding per-frame Vec allocation)
        let Some(file) = scene.get_file(*file_id) else {
            continue;
        };
        let name = file.name();

        // Calculate label dimensions
        let text_width = estimate_text_width(name, file_font_size);
        let text_height = file_font_size;

        // Primary position: right of the file
        let primary_pos = Vec2::new(
            screen_pos.x + radius + 3.0,
            screen_pos.y - file_font_size * 0.3,
        );

        // Try to place with fallback positions
        if let Some(label_pos) = label_placer.try_place_with_fallback(
            primary_pos,
            text_width,
            text_height,
            *screen_pos,
            *radius,
        ) {
            // Shadow for better readability
            let shadow_color = Color::new(0.0, 0.0, 0.0, 0.5 * alpha);
            renderer.draw_text(
                name,
                label_pos + Vec2::new(1.0, 1.0),
                font_id,
                file_font_size,
                shadow_color,
            );

            let label_color = Color::new(0.95, 0.95, 0.95, 0.8 * alpha);
            renderer.draw_text(name, label_pos, font_id, file_font_size, label_color);
        }
    }
}

/// Renders the watermark overlay.
///
/// The watermark is positioned based on the `WatermarkSettings` and rendered
/// with the specified opacity and font size. It supports primary and secondary
/// text lines and can be placed in any corner of the screen.
#[inline(never)]
pub fn render_watermark<R: Renderer + ?Sized>(
    renderer: &mut R,
    watermark: &WatermarkSettings,
    font_id: Option<FontId>,
    width: f32,
    height: f32,
) {
    // Early out if watermark is disabled or has no text
    if !watermark.enabled || !watermark.has_text() {
        return;
    }

    let Some(font_id) = font_id else { return };

    let font_size = watermark.font_size;
    let margin = watermark.margin;
    let color = watermark.effective_color();

    // Estimate text widths for positioning
    let text_width = estimate_text_width(&watermark.text, font_size);
    let subtext_width = watermark
        .subtext
        .as_ref()
        .map_or(0.0, |s| estimate_text_width(s, font_size * 0.85));
    let max_text_width = text_width.max(subtext_width);

    // Calculate total height using pure function
    let has_subtext = watermark.subtext.is_some();
    let total_height = compute_watermark_height(font_size, has_subtext);
    let line_height = font_size * 1.2;
    let subtext_size = font_size * 0.85;

    // Calculate base position using pure function
    let (base_x, base_y) = compute_watermark_position(
        watermark.position,
        margin,
        max_text_width,
        total_height,
        width,
        height,
    );

    // Draw shadow for better readability
    let shadow_color = Color::new(0.0, 0.0, 0.0, color.a * 0.5);
    let shadow_offset = Vec2::new(1.0, 1.0);

    // Draw primary text
    if !watermark.text.is_empty() {
        let text_pos = Vec2::new(base_x, base_y);

        // Shadow
        renderer.draw_text(
            &watermark.text,
            text_pos + shadow_offset,
            font_id,
            font_size,
            shadow_color,
        );

        // Main text
        renderer.draw_text(&watermark.text, text_pos, font_id, font_size, color);
    }

    // Draw subtext if present
    if let Some(subtext) = &watermark.subtext {
        let subtext_y = base_y + line_height;
        let subtext_pos = Vec2::new(base_x, subtext_y);
        let subtext_color = color.with_alpha(color.a * 0.85);
        let subtext_shadow = shadow_color.with_alpha(shadow_color.a * 0.85);

        // Shadow
        renderer.draw_text(
            subtext,
            subtext_pos + shadow_offset,
            font_id,
            subtext_size,
            subtext_shadow,
        );

        // Main text
        renderer.draw_text(subtext, subtext_pos, font_id, subtext_size, subtext_color);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // Pure Computation Function Tests
    // =========================================================================

    // -------------------------------------------------------------------------
    // Depth Factor Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_depth_factor_root() {
        let factor = compute_depth_factor(0);
        assert!((factor - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_depth_factor_mid() {
        let factor = compute_depth_factor(3);
        assert!((factor - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_compute_depth_factor_deep() {
        let factor = compute_depth_factor(6);
        assert!((factor - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_depth_factor_capped_at_1() {
        let factor = compute_depth_factor(12);
        assert!((factor - 1.0).abs() < 0.001);
    }

    // -------------------------------------------------------------------------
    // Directory Color Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_directory_color_root_brightest() {
        let root_color = compute_directory_color(0);
        let deep_color = compute_directory_color(6);
        // Root should be brighter than deep
        assert!(root_color.r > deep_color.r);
        assert!(root_color.g > deep_color.g);
    }

    #[test]
    fn test_compute_directory_color_has_valid_alpha() {
        let color = compute_directory_color(0);
        assert!((color.a - 0.55).abs() < 0.001);
    }

    #[test]
    fn test_compute_directory_color_blue_tint() {
        // Color should have slight blue tint (b > g)
        let color = compute_directory_color(0);
        assert!(color.b > color.g);
    }

    // -------------------------------------------------------------------------
    // Branch Width Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_branch_width_root() {
        let width = compute_branch_width(0);
        assert!((width - 1.5).abs() < 0.001);
    }

    #[test]
    fn test_compute_branch_width_deep() {
        let width = compute_branch_width(6);
        assert!((width - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_branch_width_minimum() {
        let width = compute_branch_width(100);
        assert!(width >= 0.8);
    }

    #[test]
    fn test_compute_branch_width_decreases_with_depth() {
        let shallow = compute_branch_width(1);
        let deep = compute_branch_width(5);
        assert!(shallow > deep);
    }

    // -------------------------------------------------------------------------
    // Branch Opacity Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_branch_opacity_root_full() {
        let opacity = compute_branch_opacity(0, 0.35, 0.3);
        assert!((opacity - 0.35).abs() < 0.001);
    }

    #[test]
    fn test_compute_branch_opacity_fades_with_depth() {
        let shallow = compute_branch_opacity(0, 0.35, 0.3);
        let deep = compute_branch_opacity(6, 0.35, 0.3);
        assert!(shallow > deep);
    }

    #[test]
    fn test_compute_branch_opacity_minimum() {
        let opacity = compute_branch_opacity(100, 0.35, 1.0);
        assert!(opacity >= 0.05 * 0.35);
    }

    #[test]
    fn test_compute_branch_opacity_respects_max() {
        let opacity = compute_branch_opacity(0, 0.5, 0.3);
        assert!((opacity - 0.5).abs() < 0.001);
    }

    // -------------------------------------------------------------------------
    // Branch Color Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_branch_color_brightens() {
        let dir_color = Color::new(0.5, 0.5, 0.5, 0.5);
        let branch_color = compute_branch_color(dir_color, 0.3);
        assert!(branch_color.r > dir_color.r);
        assert!(branch_color.g > dir_color.g);
        assert!(branch_color.b > dir_color.b);
    }

    #[test]
    fn test_compute_branch_color_uses_opacity() {
        let dir_color = Color::new(0.5, 0.5, 0.5, 0.5);
        let branch_color = compute_branch_color(dir_color, 0.25);
        assert!((branch_color.a - 0.25).abs() < 0.001);
    }

    // -------------------------------------------------------------------------
    // LOD Decision Tests - Directories
    // -------------------------------------------------------------------------

    #[test]
    fn test_should_render_directory_root_always() {
        // Root should always render even at tiny size
        assert!(should_render_directory(0.001, 0));
        assert!(should_render_directory(0.0, 0));
    }

    #[test]
    fn test_should_render_directory_non_root_threshold() {
        assert!(!should_render_directory(0.01, 1));
        assert!(should_render_directory(0.1, 1));
    }

    // -------------------------------------------------------------------------
    // LOD Decision Tests - Files
    // -------------------------------------------------------------------------

    #[test]
    fn test_should_render_file_visible() {
        assert!(should_render_file(1.0, 1.0));
    }

    #[test]
    fn test_should_render_file_too_small() {
        assert!(!should_render_file(0.05, 1.0));
    }

    #[test]
    fn test_should_render_file_invisible() {
        assert!(!should_render_file(1.0, 0.005));
    }

    // -------------------------------------------------------------------------
    // LOD Decision Tests - Users
    // -------------------------------------------------------------------------

    #[test]
    fn test_should_render_user_visible() {
        assert!(should_render_user(5.0, 1.0));
    }

    #[test]
    fn test_should_render_user_too_small() {
        assert!(!should_render_user(0.1, 1.0));
    }

    #[test]
    fn test_should_render_user_invisible() {
        assert!(!should_render_user(5.0, 0.005));
    }

    // -------------------------------------------------------------------------
    // LOD Decision Tests - Labels
    // -------------------------------------------------------------------------

    #[test]
    fn test_should_render_directory_label_shallow() {
        assert!(should_render_directory_label(5.0, 0));
        assert!(should_render_directory_label(5.0, 1));
        assert!(should_render_directory_label(5.0, 2));
    }

    #[test]
    fn test_should_render_directory_label_deep() {
        assert!(!should_render_directory_label(5.0, 3));
        assert!(!should_render_directory_label(5.0, 10));
    }

    #[test]
    fn test_should_render_directory_label_too_small() {
        assert!(!should_render_directory_label(3.0, 0));
    }

    #[test]
    fn test_should_render_file_label_visible() {
        assert!(should_render_file_label(5.0, 0.5, 0.5));
    }

    #[test]
    fn test_should_render_file_label_low_zoom() {
        assert!(!should_render_file_label(5.0, 0.5, 0.1));
    }

    #[test]
    fn test_should_render_file_label_low_alpha() {
        assert!(!should_render_file_label(5.0, 0.2, 0.5));
    }

    #[test]
    fn test_should_render_file_label_small_radius() {
        assert!(!should_render_file_label(2.0, 0.5, 0.5));
    }

    #[test]
    fn test_should_render_user_label_visible() {
        assert!(should_render_user_label(10.0, 0.5));
    }

    #[test]
    fn test_should_render_user_label_too_small() {
        assert!(!should_render_user_label(3.0, 0.5));
    }

    // -------------------------------------------------------------------------
    // LOD Decision Tests - Branches
    // -------------------------------------------------------------------------

    #[test]
    fn test_should_render_directory_branches_normal_zoom() {
        assert!(should_render_directory_branches(1.0));
        assert!(should_render_directory_branches(0.5));
    }

    #[test]
    fn test_should_render_directory_branches_low_zoom() {
        assert!(!should_render_directory_branches(0.005));
    }

    #[test]
    fn test_should_render_file_branches_normal_zoom() {
        assert!(should_render_file_branches(1.0));
        assert!(should_render_file_branches(0.1));
    }

    #[test]
    fn test_should_render_file_branches_low_zoom() {
        assert!(!should_render_file_branches(0.01));
    }

    // -------------------------------------------------------------------------
    // Effective Radius Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_file_effective_radius_small() {
        assert!((compute_file_effective_radius(0.5) - 2.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_file_effective_radius_large() {
        assert!((compute_file_effective_radius(5.0) - 5.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_user_effective_radius_small() {
        assert!((compute_user_effective_radius(2.0) - 5.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_user_effective_radius_large() {
        assert!((compute_user_effective_radius(10.0) - 10.0).abs() < 0.001);
    }

    // -------------------------------------------------------------------------
    // File Glow Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_file_glow_intensity_touched() {
        let glow = compute_file_glow_intensity(true);
        assert!((glow - 0.25).abs() < 0.001);
    }

    #[test]
    fn test_compute_file_glow_intensity_normal() {
        let glow = compute_file_glow_intensity(false);
        assert!((glow - 0.08).abs() < 0.001);
    }

    // -------------------------------------------------------------------------
    // File Border Color Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_file_border_color_darker() {
        let color = Color::new(1.0, 1.0, 1.0, 1.0);
        let border = compute_file_border_color(color);
        assert!((border.r - 0.6).abs() < 0.001);
        assert!((border.g - 0.6).abs() < 0.001);
        assert!((border.b - 0.6).abs() < 0.001);
        assert!((border.a - 1.0).abs() < 0.001);
    }

    // -------------------------------------------------------------------------
    // File Branch Color Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_file_branch_color_uses_depth_fade() {
        let color = Color::new(1.0, 0.5, 0.0, 1.0);
        let shallow = compute_file_branch_color(color, 1.0, 0, 0.3);
        let deep = compute_file_branch_color(color, 1.0, 6, 0.3);
        assert!(shallow.a > deep.a);
    }

    #[test]
    fn test_compute_file_branch_color_uses_alpha() {
        let color = Color::new(1.0, 0.5, 0.0, 1.0);
        let full = compute_file_branch_color(color, 1.0, 0, 0.3);
        let half = compute_file_branch_color(color, 0.5, 0, 0.3);
        assert!(full.a > half.a);
    }

    // -------------------------------------------------------------------------
    // Label Position Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_label_position_offset() {
        let pos = compute_label_position(Vec2::new(100.0, 100.0), 10.0, 12.0, 5.0);
        assert!((pos.x - 115.0).abs() < 0.001); // 100 + 10 + 5
        assert!((pos.y - 96.4).abs() < 0.001); // 100 - 12 * 0.3
    }

    // -------------------------------------------------------------------------
    // Label Priority Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_file_label_priority_touched_bonus() {
        let normal = compute_file_label_priority(5.0, 1.0, false);
        let touched = compute_file_label_priority(5.0, 1.0, true);
        assert!(touched > normal);
        assert!((touched - normal - 100.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_file_label_priority_larger_files() {
        let small = compute_file_label_priority(2.0, 1.0, false);
        let large = compute_file_label_priority(10.0, 1.0, false);
        assert!(large > small);
    }

    // -------------------------------------------------------------------------
    // Max Labels Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_max_labels_high_zoom() {
        assert_eq!(compute_max_labels(2.0), 200);
    }

    #[test]
    fn test_compute_max_labels_medium_zoom() {
        assert_eq!(compute_max_labels(0.75), 100);
    }

    #[test]
    fn test_compute_max_labels_low_zoom() {
        assert_eq!(compute_max_labels(0.25), 50);
    }

    // -------------------------------------------------------------------------
    // Watermark Position Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_watermark_position_top_left() {
        let (x, y) = compute_watermark_position(
            WatermarkPosition::TopLeft,
            10.0,  // margin
            100.0, // text_width
            20.0,  // total_height
            800.0, // screen_width
            600.0, // screen_height
        );
        assert!((x - 10.0).abs() < 0.001);
        assert!((y - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_watermark_position_top_right() {
        let (x, y) = compute_watermark_position(
            WatermarkPosition::TopRight,
            10.0,
            100.0,
            20.0,
            800.0,
            600.0,
        );
        assert!((x - 690.0).abs() < 0.001); // 800 - 100 - 10
        assert!((y - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_watermark_position_bottom_left() {
        let (x, y) = compute_watermark_position(
            WatermarkPosition::BottomLeft,
            10.0,
            100.0,
            20.0,
            800.0,
            600.0,
        );
        assert!((x - 10.0).abs() < 0.001);
        assert!((y - 570.0).abs() < 0.001); // 600 - 20 - 10
    }

    #[test]
    fn test_compute_watermark_position_bottom_right() {
        let (x, y) = compute_watermark_position(
            WatermarkPosition::BottomRight,
            10.0,
            100.0,
            20.0,
            800.0,
            600.0,
        );
        assert!((x - 690.0).abs() < 0.001); // 800 - 100 - 10
        assert!((y - 570.0).abs() < 0.001); // 600 - 20 - 10
    }

    // -------------------------------------------------------------------------
    // Watermark Height Tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_compute_watermark_height_no_subtext() {
        let height = compute_watermark_height(12.0, false);
        assert!((height - 12.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_watermark_height_with_subtext() {
        let height = compute_watermark_height(12.0, true);
        // 12.0 * 1.2 + 12.0 * 0.85 = 14.4 + 10.2 = 24.6
        assert!((height - 24.6).abs() < 0.001);
    }

    // =========================================================================
    // Existing Tests (Label Placer, LOD Constants, etc.)
    // =========================================================================

    #[test]
    fn test_label_placer_basic() {
        let mut placer = LabelPlacer::new(1.0);
        assert!(placer.can_place_more());

        // First label should always succeed
        assert!(placer.try_place(Vec2::new(0.0, 0.0), 50.0, 20.0));

        // Overlapping label should fail
        assert!(!placer.try_place(Vec2::new(10.0, 5.0), 50.0, 20.0));

        // Non-overlapping label should succeed
        assert!(placer.try_place(Vec2::new(100.0, 0.0), 50.0, 20.0));
    }

    #[test]
    fn test_label_placer_fallback() {
        let mut placer = LabelPlacer::new(1.0);
        // T9: Set viewport for test to allow fallback positions
        placer.set_viewport(800.0, 600.0);

        // Place at primary position (center of viewport to allow fallbacks in all directions)
        placer.try_place(Vec2::new(300.0, 300.0), 50.0, 20.0);

        // Try to place overlapping - should use fallback
        let result = placer.try_place_with_fallback(
            Vec2::new(300.0, 300.0),
            50.0,
            20.0,
            Vec2::new(300.0, 310.0),
            5.0,
        );
        // Should find a fallback position
        assert!(result.is_some());
    }

    #[test]
    fn test_rects_intersect() {
        let a = Rect::new(0.0, 0.0, 10.0, 10.0);
        let b = Rect::new(5.0, 5.0, 10.0, 10.0);
        let c = Rect::new(20.0, 20.0, 10.0, 10.0);

        assert!(rects_intersect(&a, &b));
        assert!(!rects_intersect(&a, &c));
    }

    #[test]
    fn test_estimate_text_width() {
        let width = estimate_text_width("test", 12.0);
        assert!(width > 0.0);
        assert!(width < 100.0);
    }

    // =============================================================================
    // Level-of-Detail (LOD) Tests
    // =============================================================================

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn test_lod_constants_are_reasonable() {
        // Verify LOD constants are in sensible ranges for pixel-based thresholds

        // File radius threshold should be sub-pixel (< 1.0)
        assert!(
            LOD_MIN_FILE_RADIUS > 0.0,
            "File radius threshold must be positive"
        );
        assert!(
            LOD_MIN_FILE_RADIUS < 1.0,
            "File radius threshold should be sub-pixel"
        );

        // Directory radius threshold should be very small
        assert!(
            LOD_MIN_DIR_RADIUS > 0.0,
            "Dir radius threshold must be positive"
        );
        assert!(
            LOD_MIN_DIR_RADIUS < 1.0,
            "Dir radius threshold should be sub-pixel"
        );

        // Label thresholds should be larger than entity thresholds
        assert!(
            LOD_MIN_FILE_LABEL_RADIUS > LOD_MIN_FILE_RADIUS,
            "File label threshold should be larger than file threshold"
        );
        assert!(
            LOD_MIN_DIR_LABEL_RADIUS > LOD_MIN_DIR_RADIUS,
            "Dir label threshold should be larger than dir threshold"
        );
        assert!(
            LOD_MIN_USER_LABEL_RADIUS > LOD_MIN_USER_RADIUS,
            "User label threshold should be larger than user threshold"
        );

        // Label thresholds should be readable sizes (at least a few pixels)
        assert!(
            LOD_MIN_FILE_LABEL_RADIUS >= 2.0,
            "File labels should be at least 2px"
        );
        assert!(
            LOD_MIN_DIR_LABEL_RADIUS >= 2.0,
            "Dir labels should be at least 2px"
        );
        assert!(
            LOD_MIN_USER_LABEL_RADIUS >= 2.0,
            "User labels should be at least 2px"
        );

        // Zoom thresholds should be positive and less than 1.0
        assert!(
            LOD_MIN_ZOOM_FOR_FILE_BRANCHES > 0.0,
            "Branch zoom threshold must be positive"
        );
        assert!(
            LOD_MIN_ZOOM_FOR_FILE_BRANCHES < 1.0,
            "Branch zoom threshold should be less than 1.0"
        );
        assert!(
            LOD_MIN_ZOOM_FOR_DIR_BRANCHES > 0.0,
            "Dir branch zoom threshold must be positive"
        );
        assert!(
            LOD_MIN_ZOOM_FOR_DIR_BRANCHES < 1.0,
            "Dir branch zoom threshold should be less than 1.0"
        );
    }

    #[test]
    fn test_lod_file_visibility_at_various_zoom_levels() {
        // Simulate LOD behavior at different zoom levels
        let file_world_radius = 5.0; // Typical file radius in world units

        // At zoom = 1.0, file should be visible (5px > 0.5px threshold)
        let zoom_normal = 1.0;
        let screen_radius_normal = file_world_radius * zoom_normal;
        assert!(
            screen_radius_normal >= LOD_MIN_FILE_RADIUS,
            "File visible at normal zoom"
        );

        // At zoom = 0.01, file should be invisible (0.05px < 0.5px threshold)
        let zoom_far = 0.01;
        let screen_radius_far = file_world_radius * zoom_far;
        assert!(
            screen_radius_far < LOD_MIN_FILE_RADIUS,
            "File culled at far zoom"
        );

        // At zoom = 0.1, file should be visible (0.5px = threshold)
        let zoom_threshold = LOD_MIN_FILE_RADIUS / file_world_radius;
        let screen_radius_threshold = file_world_radius * zoom_threshold;
        assert!(
            (screen_radius_threshold - LOD_MIN_FILE_RADIUS).abs() < 0.001,
            "File at exact threshold"
        );
    }

    #[test]
    fn test_lod_label_visibility_separate_from_entity() {
        // Labels should disappear before entities
        let file_world_radius = 5.0;

        // Find zoom where file is visible but label is not
        let zoom_file_visible_label_hidden = LOD_MIN_FILE_LABEL_RADIUS / file_world_radius - 0.1;
        let screen_radius = file_world_radius * zoom_file_visible_label_hidden.max(0.0);

        // At this zoom, the file entity would be visible but label would be skipped
        // (assuming zoom is not too low)
        if zoom_file_visible_label_hidden > LOD_MIN_FILE_RADIUS / file_world_radius {
            assert!(
                screen_radius < LOD_MIN_FILE_LABEL_RADIUS,
                "Label should be hidden"
            );
            assert!(
                screen_radius >= LOD_MIN_FILE_RADIUS,
                "File should still be visible"
            );
        }
    }

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn test_lod_branch_rendering_zoom_thresholds() {
        // Verify branch rendering is controlled by zoom thresholds

        // File branches should render at normal zoom
        assert!(
            1.0 >= LOD_MIN_ZOOM_FOR_FILE_BRANCHES,
            "File branches at normal zoom"
        );

        // File branches should not render at very low zoom
        assert!(
            0.01 < LOD_MIN_ZOOM_FOR_FILE_BRANCHES,
            "File branches culled at very low zoom"
        );

        // Directory branches have lower threshold (more important structure)
        assert!(
            LOD_MIN_ZOOM_FOR_DIR_BRANCHES <= LOD_MIN_ZOOM_FOR_FILE_BRANCHES,
            "Dir branches have lower (or equal) threshold than file branches"
        );
    }

    // =========================================================================
    // Performance Benchmark Tests
    // =========================================================================
    //
    // These tests measure the performance impact of label collision detection
    // and beam limiting. They use std::time::Instant for timing.
    //
    // Run with: cargo test -p rource-wasm bench_ --release -- --nocapture

    #[test]
    fn bench_label_placer_new() {
        use std::time::Instant;

        const ITERATIONS: u32 = 10_000;
        let start = Instant::now();

        for _ in 0..ITERATIONS {
            let _ = std::hint::black_box(LabelPlacer::new(1.0));
        }

        let elapsed = start.elapsed();
        let per_op = elapsed.as_nanos() / ITERATIONS as u128;
        println!(
            "\nLabelPlacer::new(): {} iterations in {:?} ({} ns/op)",
            ITERATIONS, elapsed, per_op
        );

        // Note: LabelPlacer::new() is a ONE-TIME startup cost, not per-frame.
        // The per-frame cost is reset() which is ~250ns.
        // Assertion: creation should be < 100µs (100,000 ns) - acceptable startup cost
        // (Relaxed from 50µs to account for CI runner variability)
        assert!(
            per_op < 100_000,
            "LabelPlacer::new() too slow: {} ns/op (one-time startup cost)",
            per_op
        );
    }

    #[test]
    fn bench_label_placer_reset() {
        use std::time::Instant;

        const ITERATIONS: u32 = 100_000;
        let mut placer = LabelPlacer::new(1.0);

        // Pre-populate with some labels to make reset realistic
        for i in 0..50 {
            placer.try_place(Vec2::new(i as f32 * 100.0, 0.0), 50.0, 20.0);
        }

        let start = Instant::now();

        for _ in 0..ITERATIONS {
            placer.reset(1.0);
            // Add a label to make reset non-trivial
            placer.try_place(Vec2::new(0.0, 0.0), 50.0, 20.0);
        }

        let elapsed = start.elapsed();
        let per_op = elapsed.as_nanos() / ITERATIONS as u128;
        println!(
            "\nLabelPlacer::reset(): {} iterations in {:?} ({} ns/op)",
            ITERATIONS, elapsed, per_op
        );

        // Assertion: reset should be < 1µs (1,000 ns)
        assert!(
            per_op < 1_000,
            "LabelPlacer::reset() too slow: {} ns/op",
            per_op
        );
    }

    #[test]
    fn bench_label_placer_try_place() {
        use std::time::Instant;

        const ITERATIONS: u32 = 100_000;
        let mut placer = LabelPlacer::new(1.0);

        let start = Instant::now();

        for i in 0..ITERATIONS {
            // Spread labels across grid to avoid collision checks
            let x = (i % 100) as f32 * 60.0;
            let y = (i / 100) as f32 * 30.0;
            placer.try_place(Vec2::new(x, y), 50.0, 20.0);

            // Reset periodically to avoid filling up
            if i % 1000 == 999 {
                placer.reset(1.0);
            }
        }

        let elapsed = start.elapsed();
        let per_op = elapsed.as_nanos() / ITERATIONS as u128;
        println!(
            "\nLabelPlacer::try_place() (no collision): {} iterations in {:?} ({} ns/op)",
            ITERATIONS, elapsed, per_op
        );

        // Assertion: try_place should be < 500ns
        assert!(
            per_op < 500,
            "LabelPlacer::try_place() too slow: {} ns/op",
            per_op
        );
    }

    #[test]
    fn bench_label_placer_try_place_with_fallback() {
        use std::time::Instant;

        const ITERATIONS: u32 = 50_000;
        let mut placer = LabelPlacer::new(1.0);

        // Pre-populate with labels to force fallback checks
        for i in 0..20 {
            placer.try_place(Vec2::new(i as f32 * 60.0, 0.0), 50.0, 20.0);
        }

        let start = Instant::now();

        for i in 0..ITERATIONS {
            let x = (i % 20) as f32 * 60.0;
            let _ = placer.try_place_with_fallback(
                Vec2::new(x, 0.0), // Will collide with existing
                50.0,
                20.0,
                Vec2::new(x, 25.0),
                5.0,
            );

            if i % 500 == 499 {
                placer.reset(1.0);
                for j in 0..20 {
                    placer.try_place(Vec2::new(j as f32 * 60.0, 0.0), 50.0, 20.0);
                }
            }
        }

        let elapsed = start.elapsed();
        let per_op = elapsed.as_nanos() / ITERATIONS as u128;
        println!(
            "\nLabelPlacer::try_place_with_fallback(): {} iterations in {:?} ({} ns/op)",
            ITERATIONS, elapsed, per_op
        );

        // Assertion: try_place_with_fallback should be < 2µs (may need 4 collision checks)
        assert!(
            per_op < 2_000,
            "LabelPlacer::try_place_with_fallback() too slow: {} ns/op",
            per_op
        );
    }

    #[test]
    fn bench_beam_sorting() {
        use std::time::Instant;

        const ITERATIONS: u32 = 10_000;

        // Simulate 100 active actions with progress values
        let actions: Vec<(usize, f32)> = (0..100).map(|i| (i, (i as f32) / 100.0)).collect();

        let start = Instant::now();

        for _ in 0..ITERATIONS {
            let mut active = actions.clone();
            active.sort_unstable_by(|a, b| {
                a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal)
            });
            let _limited: Vec<_> = std::hint::black_box(active.into_iter().take(15).collect());
        }

        let elapsed = start.elapsed();
        let per_op = elapsed.as_nanos() / ITERATIONS as u128;
        println!(
            "\nBeam sorting (100 actions, take 15): {} iterations in {:?} ({} ns/op)",
            ITERATIONS, elapsed, per_op
        );

        // Assertion: sorting 100 items should be < 5µs
        assert!(per_op < 5_000, "Beam sorting too slow: {} ns/op", per_op);
    }

    #[test]
    fn bench_user_label_sorting() {
        use std::time::Instant;

        const ITERATIONS: u32 = 10_000;

        // Simulate 50 user candidates with priority values
        let candidates: Vec<(usize, Vec2, f32, f32, f32)> = (0..50)
            .map(|i| (i, Vec2::new(i as f32 * 10.0, 0.0), 5.0, 1.0, i as f32))
            .collect();

        let start = Instant::now();

        for _ in 0..ITERATIONS {
            let mut users = candidates.clone();
            // Sort by priority (last field) descending
            users.sort_unstable_by(|a, b| {
                b.4.partial_cmp(&a.4).unwrap_or(std::cmp::Ordering::Equal)
            });
            let _ = std::hint::black_box(users);
        }

        let elapsed = start.elapsed();
        let per_op = elapsed.as_nanos() / ITERATIONS as u128;
        println!(
            "\nUser label sorting (50 users): {} iterations in {:?} ({} ns/op)",
            ITERATIONS, elapsed, per_op
        );

        // Assertion: sorting 50 items should be < 3µs
        assert!(
            per_op < 3_000,
            "User label sorting too slow: {} ns/op",
            per_op
        );
    }

    #[test]
    fn bench_full_label_placement_scenario() {
        use std::time::Instant;

        const ITERATIONS: u32 = 1_000;

        // Simulate realistic scenario: 30 user labels + 50 file labels per frame
        let start = Instant::now();

        for _ in 0..ITERATIONS {
            let mut placer = LabelPlacer::new(1.0);

            // Place user labels (high priority, spread across screen)
            for i in 0..30 {
                let x = (i % 10) as f32 * 150.0;
                let y = (i / 10) as f32 * 200.0;
                placer.try_place_with_fallback(
                    Vec2::new(x + 20.0, y),
                    60.0,
                    18.0,
                    Vec2::new(x, y + 10.0),
                    15.0,
                );
            }

            // Place file labels (lower priority, denser)
            for i in 0..50 {
                let x = (i % 15) as f32 * 100.0;
                let y = (i / 15) as f32 * 150.0 + 50.0;
                placer.try_place_with_fallback(
                    Vec2::new(x + 10.0, y),
                    50.0,
                    14.0,
                    Vec2::new(x, y + 5.0),
                    8.0,
                );
            }
        }

        let elapsed = start.elapsed();
        let per_frame = elapsed.as_micros() / ITERATIONS as u128;
        println!(
            "\nFull label placement (30 users + 50 files): {} frames in {:?} ({} µs/frame)",
            ITERATIONS, elapsed, per_frame
        );

        // Assertion: full frame should be < 250µs (well within 16.67ms budget)
        // (Relaxed from 100µs to account for CI runner variability)
        assert!(
            per_frame < 250,
            "Full label placement too slow: {} µs/frame",
            per_frame
        );

        // Note: 250µs is 1.5% of a 16.67ms frame budget at 60fps
        // This is acceptable overhead for collision-free labels
    }
}
