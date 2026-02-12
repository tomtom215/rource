// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! File rendering phases.
//!
//! Renders file nodes and labels with LOD (Level-of-Detail) optimization.

use rource_core::FileId;
use rource_math::{Color, Vec2};
use rource_render::lod::MIN_FILE_LABEL_RADIUS as LOD_MIN_FILE_LABEL_RADIUS;
use rource_render::Renderer;

use super::helpers::{
    compute_file_border_color, compute_file_branch_color, compute_file_effective_radius,
    should_render_file, should_render_file_branches,
};
use super::label_placer::LabelPlacer;
use super::{estimate_text_width, RenderContext};
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

/// Renders file nodes with enhanced styling.
///
/// Applies LOD (Level-of-Detail) optimization:
/// - Files with screen radius < `LOD_MIN_FILE_RADIUS` are skipped entirely
/// - File-to-directory branches are skipped when zoom < `LOD_MIN_ZOOM_FOR_FILE_BRANCHES`
///
/// # Phase 87: Zero-Allocation Branch Drawing
///
/// The `curve_buf` parameter is a reusable buffer for branch curve points.
/// Previously, `draw_curved_branch` allocated a new `Vec<Vec2>` (~31 points)
/// for every file branch, causing ~200 heap allocations per frame.
/// Now uses `draw_curved_branch_buffered` which reuses the caller-owned buffer.
///
/// Additionally, short branches (< ~50px on screen) use straight lines
/// instead of Catmull-Rom splines, and the nearly-invisible branch glow
/// pass (alpha * 0.15) is removed.
#[inline(never)]
pub fn render_files<R: Renderer + ?Sized>(
    renderer: &mut R,
    ctx: &RenderContext,
    scene: &rource_core::Scene,
    camera: &rource_core::Camera,
    curve_buf: &mut Vec<rource_math::Vec2>,
) {
    trace_span!("render_files", count = ctx.visible_files.len());

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
            // Phase 87: Uses zero-allocation buffered version with LOD simplification
            if render_branches {
                if let Some(dir) = scene.directories().get(file.directory()) {
                    let dir_screen = camera.world_to_screen(dir.position());
                    let branch_color =
                        compute_file_branch_color(color, alpha, dir.depth(), ctx.branch_depth_fade);

                    draw_curved_branch_buffered(
                        renderer,
                        dir_screen,
                        screen_pos,
                        0.8,
                        branch_color,
                        ctx.use_curves,
                        curve_buf,
                    );
                }
            }

            // Draw soft glow behind file ONLY for touched files AND large enough to be visible
            // Phase 59: Skip glow for inactive files (~97% of files)
            // Phase 70: LOD culling - skip glow when effective_radius < 3.0 (glow imperceptible)
            //           Reduced glow radius from 2.0x to 1.5x (-44% pixel area: 4.0x -> 2.25x)
            let is_touched = file.touch_time() > 0.0;
            if is_touched && effective_radius >= 3.0 {
                let glow_color = color.with_alpha(0.25 * alpha);
                renderer.draw_disc(screen_pos, effective_radius * 1.5, glow_color);
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
    trace_span!("render_file_labels");

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
