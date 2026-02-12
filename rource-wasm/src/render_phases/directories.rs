// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Directory rendering phases.
//!
//! Renders directory nodes and labels with LOD (Level-of-Detail) optimization.

use rource_math::{Color, Vec2};
use rource_render::lod::MIN_DIR_LABEL_RADIUS as LOD_MIN_DIR_LABEL_RADIUS;
use rource_render::Renderer;

use super::helpers::{
    compute_branch_color, compute_branch_opacity, compute_branch_width, compute_directory_color,
    should_render_directory, should_render_directory_branches,
};
use super::RenderContext;
use crate::rendering::draw_curved_branch_buffered;

// =============================================================================
// Tracing Infrastructure (OP-1: Production Telemetry)
// =============================================================================

/// Creates a tracing span for a render phase (no-op when tracing is disabled).
#[cfg(feature = "tracing")]
macro_rules! trace_span {
    ($name:expr) => {
        let _span = tracing::info_span!($name).entered();
    };
    ($name:expr, $($field:tt)*) => {
        let _span = tracing::info_span!($name, $($field)*).entered();
    };
}

#[cfg(not(feature = "tracing"))]
macro_rules! trace_span {
    ($name:expr) => {};
    ($name:expr, $($field:tt)*) => {};
}

/// Renders directory nodes with enhanced styling.
///
/// Applies LOD (Level-of-Detail) optimization:
/// - Directories with screen radius < `LOD_MIN_DIR_RADIUS` are skipped
/// - Directory-to-parent branches are skipped when zoom < `LOD_MIN_ZOOM_FOR_DIR_BRANCHES`
///
/// # Phase 87: Zero-Allocation Branch Drawing
///
/// The `curve_buf` parameter is a reusable buffer for branch curve points,
/// shared with `render_files`. Eliminates per-directory heap allocations
/// for branch curves.
#[inline(never)] // Prevent inlining for better profiling
pub fn render_directories<R: Renderer + ?Sized>(
    renderer: &mut R,
    ctx: &RenderContext,
    scene: &rource_core::Scene,
    camera: &rource_core::Camera,
    curve_buf: &mut Vec<rource_math::Vec2>,
) {
    trace_span!("render_directories", count = ctx.visible_dirs.len());

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

                    draw_curved_branch_buffered(
                        renderer,
                        parent_screen,
                        screen_pos,
                        branch_width,
                        branch_color,
                        ctx.use_curves,
                        curve_buf,
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
    trace_span!("render_directory_labels");

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
