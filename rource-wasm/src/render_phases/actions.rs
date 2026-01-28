// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Action beam rendering phase.
//!
//! Renders animated beams from users to files during modifications.

use rource_render::Renderer;

use super::RenderContext;
use crate::rendering::draw_action_beam;

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
    trace_span!("render_actions");

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
