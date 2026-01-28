// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! User rendering phases.
//!
//! Renders user avatars and labels with LOD (Level-of-Detail) optimization.

use rource_core::UserId;
use rource_math::{Color, Vec2};
use rource_render::Renderer;

use super::helpers::{compute_user_effective_radius, should_render_user, should_render_user_label};
use super::label_placer::LabelPlacer;
use super::{estimate_text_width, RenderContext};
use crate::rendering::draw_avatar_shape;

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
    trace_span!("render_users", count = ctx.visible_users.len());

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
    trace_span!("render_user_labels");

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
