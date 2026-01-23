// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Rendering logic for the Rource CLI windowed mode.
//!
//! This module provides frame rendering for the interactive windowed
//! visualization mode with enhanced visuals including stylized avatars
//! and curved tree branches.
//!
//! ## Shared Rendering Code
//!
//! Core visual utilities (spline interpolation, avatar drawing, beam effects,
//! curved branches) are defined in `rource_render::visual` and shared between
//! CLI and WASM builds to ensure visual parity.
//!
//! ## Level-of-Detail (LOD) Optimization
//!
//! To maintain high FPS regardless of repository size, we skip rendering entities
//! that would appear smaller than a certain threshold on screen. See the `LOD_*`
//! constants below for configuration.

use rource_core::camera::Camera;
use rource_core::config::{WatermarkPosition, WatermarkSettings};
use rource_core::scene::{FileNode, Scene};
use rource_core::{DirId, FileId, UserId};
use rource_math::{Bounds, Color, Vec2};
use rource_render::effects::{BloomEffect, ShadowEffect};
use rource_render::visual::{draw_action_beam, draw_avatar_shape, draw_curved_branch};
use rource_render::{
    estimate_text_width, FontId, LabelPlacer, Renderer, SoftwareRenderer, TextureId,
};
use rource_vcs::Commit;

use crate::app::{App, PlaybackState};
use crate::args::Args;
use crate::avatar::AvatarRegistry;
use crate::helpers::get_initials;

// =============================================================================
// Level-of-Detail (LOD) Constants
// =============================================================================
// These thresholds control when entities are skipped for performance.
// Values are in screen pixels. These match the WASM renderer for visual parity.

/// Minimum screen radius for a file to be rendered at all.
/// Set low (0.1px) because we enforce a minimum render size of 2px anyway.
const LOD_MIN_FILE_RADIUS: f32 = 0.1;

/// Minimum screen radius for a directory node to be rendered.
/// Directories are important landmarks, so we use a very low threshold.
const LOD_MIN_DIR_RADIUS: f32 = 0.05;

/// Minimum screen radius for file labels to be rendered.
const LOD_MIN_FILE_LABEL_RADIUS: f32 = 3.0;

/// Minimum screen radius for directory labels to be rendered.
const LOD_MIN_DIR_LABEL_RADIUS: f32 = 4.0;

/// Minimum screen radius for user avatars to be rendered.
/// Set low (0.3px) because we enforce a minimum render size of 5px anyway.
const LOD_MIN_USER_RADIUS: f32 = 0.3;

/// Minimum screen radius for user labels to be rendered.
const LOD_MIN_USER_LABEL_RADIUS: f32 = 5.0;

/// Minimum zoom level for rendering file-to-directory connections.
const LOD_MIN_ZOOM_FOR_FILE_BRANCHES: f32 = 0.02;

/// Minimum zoom level for rendering directory-to-parent connections.
const LOD_MIN_ZOOM_FOR_DIR_BRANCHES: f32 = 0.01;

// =============================================================================
// Pure Helper Functions (testable without renderer)
// =============================================================================

// These pure functions are extracted for unit testing. They are not called directly
// from the main rendering code, which uses optimized inline versions.
#[allow(dead_code)]
#[allow(clippy::wildcard_imports)]
mod helpers {
    use super::*;

    // ---- Directory Rendering Helpers ----

    /// Computes the depth factor for a directory (0.0 to 1.0).
    ///
    /// Deeper directories have higher values, capped at depth 6.
    #[inline]
    #[must_use]
    pub fn compute_dir_depth_factor(depth: u32) -> f32 {
        (depth as f32 / 6.0).min(1.0)
    }

    /// Computes the base brightness for directory coloring.
    ///
    /// Shallower directories are brighter.
    #[inline]
    #[must_use]
    pub fn compute_dir_base_brightness(depth_factor: f32) -> f32 {
        0.25 + 0.1 * (1.0 - depth_factor)
    }

    /// Computes the directory node color based on depth.
    ///
    /// Returns a slightly blue-tinted color that gets darker with depth.
    #[inline]
    #[must_use]
    pub fn compute_dir_color(depth: u32) -> Color {
        let depth_factor = compute_dir_depth_factor(depth);
        let base_brightness = compute_dir_base_brightness(depth_factor);
        Color::new(
            base_brightness * 0.9,
            base_brightness,
            base_brightness * 1.1 + 0.05,
            0.55,
        )
    }

    /// Computes the glow color for directory background effect.
    #[inline]
    #[must_use]
    pub fn compute_dir_glow_color(dir_color: Color) -> Color {
        dir_color.with_alpha(0.1)
    }

    /// Computes the center dot color for directory nodes.
    #[inline]
    #[must_use]
    pub fn compute_dir_center_color(dir_color: Color) -> Color {
        dir_color.with_alpha(0.4)
    }

    /// Computes the branch width based on depth.
    ///
    /// Branches are thicker near the root.
    #[inline]
    #[must_use]
    pub fn compute_branch_width(depth_factor: f32) -> f32 {
        (1.5 - depth_factor * 0.5).max(0.8)
    }

    /// Computes the branch color for directory connections.
    #[inline]
    #[must_use]
    pub fn compute_dir_branch_color(dir_color: Color) -> Color {
        Color::new(
            dir_color.r * 1.1,
            dir_color.g * 1.1,
            dir_color.b * 1.2,
            0.35,
        )
    }

    /// Determines if a directory should be rendered based on LOD.
    ///
    /// Root directory (depth 0) is always rendered.
    #[inline]
    #[must_use]
    pub fn should_render_dir(radius: f32, depth: u32) -> bool {
        depth == 0 || radius >= LOD_MIN_DIR_RADIUS
    }

    /// Determines if directory branches should be rendered at this zoom level.
    #[inline]
    #[must_use]
    pub fn should_render_dir_branches(zoom: f32, hide_tree: bool) -> bool {
        !hide_tree && zoom >= LOD_MIN_ZOOM_FOR_DIR_BRANCHES
    }

    /// Determines if a directory label should be rendered.
    #[inline]
    #[must_use]
    pub fn should_render_dir_label(
        hide_dirnames: bool,
        depth: u32,
        dir_name_depth: u32,
        radius: f32,
    ) -> bool {
        !hide_dirnames && depth <= dir_name_depth && radius >= LOD_MIN_DIR_LABEL_RADIUS
    }

    /// Computes the label position for a directory.
    #[inline]
    #[must_use]
    pub fn compute_dir_label_position(screen_pos: Vec2, radius: f32, font_size: f32) -> Vec2 {
        Vec2::new(screen_pos.x + radius + 4.0, screen_pos.y - font_size * 0.3)
    }

    // ---- File Rendering Helpers ----

    /// Computes the effective file radius with minimum size enforcement.
    #[inline]
    #[must_use]
    pub fn compute_effective_file_radius(radius: f32) -> f32 {
        radius.max(2.0)
    }

    /// Computes the glow intensity based on whether file is touched.
    #[inline]
    #[must_use]
    pub fn compute_file_glow_intensity(is_touched: bool) -> f32 {
        if is_touched {
            0.25
        } else {
            0.08
        }
    }

    /// Computes the file glow color.
    #[inline]
    #[must_use]
    pub fn compute_file_glow_color(color: Color, glow_intensity: f32, alpha: f32) -> Color {
        color.with_alpha(glow_intensity * alpha)
    }

    /// Computes the file border color (darker version of the file color).
    #[inline]
    #[must_use]
    pub fn compute_file_border_color(color: Color) -> Color {
        Color::new(color.r * 0.6, color.g * 0.6, color.b * 0.6, color.a)
    }

    /// Computes label priority for a file (higher = more important).
    #[inline]
    #[must_use]
    pub fn compute_file_label_priority(radius: f32, alpha: f32, is_touched: bool) -> f32 {
        let activity_bonus = if is_touched { 100.0 } else { 0.0 };
        radius * alpha * 10.0 + activity_bonus
    }

    /// Determines if a file should be rendered based on LOD.
    #[inline]
    #[must_use]
    pub fn should_render_file(radius: f32) -> bool {
        radius >= LOD_MIN_FILE_RADIUS
    }

    /// Determines if file branches should be rendered at this zoom level.
    #[inline]
    #[must_use]
    pub fn should_render_file_branches(zoom: f32, hide_tree: bool) -> bool {
        !hide_tree && zoom >= LOD_MIN_ZOOM_FOR_FILE_BRANCHES
    }

    /// Determines if a file should have its label collected for rendering.
    #[inline]
    #[must_use]
    pub fn should_add_file_label(show_filenames: bool, alpha: f32, zoom: f32, radius: f32) -> bool {
        show_filenames && alpha > 0.3 && zoom > 0.15 && radius >= LOD_MIN_FILE_LABEL_RADIUS
    }

    /// Computes the file branch color (matches file color but semi-transparent).
    #[inline]
    #[must_use]
    pub fn compute_file_branch_color(color: Color, alpha: f32) -> Color {
        Color::new(color.r * 0.7, color.g * 0.7, color.b * 0.7, 0.25 * alpha)
    }

    // ---- User Rendering Helpers ----

    /// Computes the effective user radius with minimum size enforcement.
    #[inline]
    #[must_use]
    pub fn compute_effective_user_radius(radius: f32) -> f32 {
        radius.max(5.0)
    }

    /// Computes the user border color.
    #[inline]
    #[must_use]
    pub fn compute_user_border_color(color: Color, alpha: f32) -> Color {
        Color::new(color.r * 0.5, color.g * 0.5, color.b * 0.5, alpha)
    }

    /// Computes the glow radius for a specific glow layer.
    #[inline]
    #[must_use]
    pub fn compute_user_glow_radius(effective_radius: f32, layer: u32) -> f32 {
        effective_radius * (1.3 + layer as f32 * 0.15)
    }

    /// Computes the glow alpha for a specific glow layer.
    #[inline]
    #[must_use]
    pub fn compute_user_glow_alpha(alpha: f32, layer: u32) -> f32 {
        alpha * 0.15 * (1.0 - layer as f32 * 0.25)
    }

    /// Computes the font size for user initials.
    #[inline]
    #[must_use]
    pub fn compute_initials_font_size(effective_radius: f32) -> f32 {
        (effective_radius * 0.55).clamp(8.0, 18.0)
    }

    /// Computes the text width estimate for initials.
    #[inline]
    #[must_use]
    pub fn compute_initials_text_width(initials_len: usize, font_size: f32) -> f32 {
        initials_len as f32 * font_size * 0.5
    }

    /// Computes the position for user initials (in body area).
    #[inline]
    #[must_use]
    pub fn compute_initials_position(
        screen_pos: Vec2,
        effective_radius: f32,
        text_width: f32,
    ) -> Vec2 {
        Vec2::new(
            screen_pos.x - text_width * 0.5,
            screen_pos.y + effective_radius * 0.15,
        )
    }

    /// Determines if a user should be rendered based on LOD.
    #[inline]
    #[must_use]
    pub fn should_render_user(radius: f32) -> bool {
        radius >= LOD_MIN_USER_RADIUS
    }

    /// Determines if a user label should be rendered based on LOD.
    #[inline]
    #[must_use]
    pub fn should_render_user_label(show_usernames: bool, radius: f32) -> bool {
        show_usernames && radius >= LOD_MIN_USER_LABEL_RADIUS
    }

    /// Determines if user initials should be rendered (for avatars without textures).
    #[inline]
    #[must_use]
    pub fn should_render_initials(effective_radius: f32) -> bool {
        effective_radius > 14.0
    }

    /// Computes the user label position.
    #[inline]
    #[must_use]
    pub fn compute_user_label_position(
        screen_pos: Vec2,
        effective_radius: f32,
        font_size: f32,
    ) -> Vec2 {
        Vec2::new(
            screen_pos.x + effective_radius + 5.0,
            screen_pos.y - font_size * 0.3,
        )
    }

    // ---- Progress Bar Helpers ----

    /// Computes the progress ratio (0.0 to 1.0).
    #[inline]
    #[must_use]
    pub fn compute_progress(current_commit: usize, total_commits: usize) -> f32 {
        current_commit as f32 / total_commits.max(1) as f32
    }

    // ---- Stats Indicator Helpers ----

    /// Computes the file count indicator bar width (logarithmic scale).
    #[inline]
    #[must_use]
    pub fn compute_file_indicator_bar(file_count: usize) -> f32 {
        if file_count > 0 {
            ((file_count as f32).ln() / 10.0).min(1.0)
        } else {
            0.0
        }
    }

    /// Computes the user count indicator bar width (logarithmic scale).
    #[inline]
    #[must_use]
    pub fn compute_user_indicator_bar(user_count: usize) -> f32 {
        if user_count > 0 {
            ((user_count as f32).ln() / 5.0).min(1.0)
        } else {
            0.0
        }
    }

    // ---- Title/Text Helpers ----

    /// Computes the X position for a centered title.
    #[inline]
    #[must_use]
    pub fn compute_title_x_position(width: f32, title_len: usize, title_size: f32) -> f32 {
        ((width / 2.0) - (title_len as f32 * title_size * 0.3)).max(10.0)
    }

    /// Determines if a speed indicator should be displayed.
    #[inline]
    #[must_use]
    pub fn should_show_speed_indicator(speed: f32) -> bool {
        (speed - 1.0).abs() > 0.01
    }

    /// Formats the stats text for display.
    #[inline]
    #[must_use]
    pub fn format_stats_text(
        current_commit: usize,
        total_commits: usize,
        file_count: usize,
        user_count: usize,
    ) -> String {
        format!(
            "{current_commit}/{total_commits} commits | {file_count} files | {user_count} users"
        )
    }

    // ---- Legend Helpers ----

    /// Computes the legend height based on number of entries.
    #[inline]
    #[must_use]
    pub fn compute_legend_height(entry_count: usize, entry_height: f32, padding: f32) -> f32 {
        entry_count as f32 * entry_height + padding * 2.0
    }

    /// Computes the legend position (bottom-right corner).
    #[inline]
    #[must_use]
    pub fn compute_legend_position(
        screen_width: f32,
        screen_height: f32,
        legend_width: f32,
        legend_height: f32,
        padding: f32,
    ) -> (f32, f32) {
        let x = screen_width - legend_width - padding;
        let y = screen_height - legend_height - 20.0;
        (x, y)
    }

    /// Truncates an extension name for display (max 8 chars).
    #[inline]
    #[must_use]
    pub fn truncate_extension(ext: &str) -> String {
        if ext.len() > 8 {
            format!("{}..", &ext[..6])
        } else {
            ext.to_string()
        }
    }

    // ---- Watermark Helpers ----

    /// Computes the total height for watermark text block.
    #[inline]
    #[must_use]
    pub fn compute_watermark_total_height(has_subtext: bool, line_height: f32) -> f32 {
        if has_subtext {
            line_height * 2.0
        } else {
            line_height
        }
    }

    /// Computes the watermark position based on corner setting.
    #[inline]
    #[must_use]
    pub fn compute_watermark_position_cli(
        position: WatermarkPosition,
        margin: f32,
        max_width: f32,
        total_height: f32,
        screen_width: f32,
        screen_height: f32,
    ) -> (f32, f32) {
        match position {
            WatermarkPosition::TopLeft => (margin, margin),
            WatermarkPosition::TopRight => (screen_width - max_width - margin, margin),
            WatermarkPosition::BottomLeft => (margin, screen_height - total_height - margin),
            WatermarkPosition::BottomRight => (
                screen_width - max_width - margin,
                screen_height - total_height - margin,
            ),
        }
    }

    /// Computes the X position for subtext (right-aligned for right corners).
    #[inline]
    #[must_use]
    pub fn compute_subtext_x(
        position: WatermarkPosition,
        x: f32,
        max_width: f32,
        subtext_width: f32,
    ) -> f32 {
        match position {
            WatermarkPosition::TopLeft | WatermarkPosition::BottomLeft => x,
            WatermarkPosition::TopRight | WatermarkPosition::BottomRight => {
                x + (max_width - subtext_width)
            }
        }
    }

    // ---- Label Shadow Helpers ----

    /// Standard shadow color for labels.
    pub const LABEL_SHADOW_COLOR: Color = Color {
        r: 0.0,
        g: 0.0,
        b: 0.0,
        a: 0.5,
    };

    /// Shadow offset for labels (1 pixel diagonal).
    pub const LABEL_SHADOW_OFFSET: Vec2 = Vec2 { x: 1.0, y: 1.0 };

    /// Computes the shadow color with adjusted alpha.
    #[inline]
    #[must_use]
    pub fn compute_label_shadow_color(alpha: f32) -> Color {
        Color::new(0.0, 0.0, 0.0, 0.5 * alpha)
    }

    /// Computes the file label color.
    #[inline]
    #[must_use]
    pub fn compute_file_label_color(alpha: f32) -> Color {
        Color::new(0.95, 0.95, 0.95, 0.8 * alpha)
    }

    /// Computes the user label color.
    #[inline]
    #[must_use]
    pub fn compute_user_label_color(alpha: f32) -> Color {
        Color::new(1.0, 1.0, 1.0, 0.9 * alpha)
    }

    /// Computes the directory label shadow color.
    #[inline]
    #[must_use]
    pub fn compute_dir_label_shadow_color() -> Color {
        Color::new(0.0, 0.0, 0.0, 0.4)
    }

    /// Computes the directory label color.
    #[inline]
    #[must_use]
    pub fn compute_dir_label_color() -> Color {
        Color::new(0.75, 0.78, 0.85, 0.7)
    }
}

// Re-export helpers for tests
#[allow(unused_imports)]
pub use helpers::*;

// =============================================================================
// Render Functions
// =============================================================================

/// Render a frame in windowed mode.
///
/// This function renders all scene entities, UI overlays, and applies
/// post-processing effects.
#[allow(clippy::too_many_lines)]
pub fn render_frame(app: &mut App) {
    let Some(renderer) = &mut app.renderer else {
        return;
    };

    renderer.begin_frame();

    // Clear to background color
    let bg_color = app.args.parse_background_color();
    renderer.clear(bg_color);

    // Draw background image if available
    if let Some(bg_texture) = app.background_texture {
        let viewport_bounds = Bounds::new(
            Vec2::ZERO,
            Vec2::new(renderer.width() as f32, renderer.height() as f32),
        );
        renderer.draw_quad(viewport_bounds, Some(bg_texture), Color::WHITE);
    }

    // Get camera's visible bounds for frustum culling
    let visible_bounds = app.camera.visible_bounds();
    let culling_bounds = Scene::expand_bounds_for_visibility(&visible_bounds, 100.0);

    // Query visible entities using spatial index (zero-allocation: reuses pre-allocated buffers)
    app.scene.visible_entities_into(
        &culling_bounds,
        &mut app.visible_dirs_buffer,
        &mut app.visible_files_buffer,
        &mut app.visible_users_buffer,
    );

    // Render directories
    render_directories(
        renderer,
        &app.scene,
        &app.camera,
        &app.visible_dirs_buffer,
        &app.args,
        app.default_font,
        app.dir_name_depth,
    );

    // Render files (uses reusable label candidates buffer to avoid per-frame allocations)
    render_files(
        renderer,
        &app.scene,
        &app.camera,
        &app.visible_files_buffer,
        &app.args,
        app.default_font,
        &mut app.file_label_candidates_buffer,
    );

    // Render actions (beams)
    render_actions(renderer, &app.scene, &app.camera);

    // Render users
    render_users(
        renderer,
        &app.scene,
        &app.camera,
        &app.visible_users_buffer,
        &app.args,
        app.default_font,
        &app.avatar_registry,
    );

    // Render UI overlays
    render_overlays(
        renderer,
        &app.playback,
        &app.args,
        app.default_font,
        &app.commits,
        app.current_commit,
        &mut app.scene,
        app.logo_texture,
        app.logo_dimensions,
        app.logo_offset,
        &app.watermark,
    );

    renderer.end_frame();

    // Apply post-processing effects (both effects use pre-allocated buffers for zero allocation)
    apply_effects(
        renderer,
        app.shadow.as_mut(),
        app.bloom.as_mut(),
        app.args.hide_bloom,
    );
}

/// Render directory entities with enhanced visual styling and LOD optimization.
fn render_directories(
    renderer: &mut SoftwareRenderer,
    scene: &Scene,
    camera: &Camera,
    visible_ids: &[DirId],
    args: &Args,
    font_id: Option<FontId>,
    dir_name_depth: u32,
) {
    let hide_root = args.hide_root;
    let hide_tree = args.hide_tree;
    let hide_dirnames = args.hide_dirnames;
    let dir_font_size = args.font_size * 0.75;
    let zoom = camera.zoom();

    // Use curves for zoomed-out views (performance-friendly)
    let use_curves = zoom < 0.8;

    // LOD: Pre-compute whether we should render directory branches at this zoom level
    let render_branches = !hide_tree && zoom >= LOD_MIN_ZOOM_FOR_DIR_BRANCHES;

    for &dir_id in visible_ids {
        let Some(dir) = scene.directories().get(dir_id) else {
            continue;
        };

        if !dir.is_visible() {
            continue;
        }

        // Skip root directory if hide_root is set
        if hide_root && dir.depth() == 0 {
            continue;
        }

        let screen_pos = camera.world_to_screen(dir.position());
        let radius = dir.radius() * zoom;

        // LOD: Skip directories that are too small to be visible
        // Root directory (depth 0) is always rendered as it's the anchor point
        if radius < LOD_MIN_DIR_RADIUS && dir.depth() > 0 {
            continue;
        }

        // Enhanced directory styling based on depth
        let depth = dir.depth() as f32;
        let depth_factor = (depth / 6.0).min(1.0);

        // Gradient color: slightly blue for depth, warmer for shallower
        let base_brightness = 0.25 + 0.1 * (1.0 - depth_factor);
        let dir_color = Color::new(
            base_brightness * 0.9,
            base_brightness,
            base_brightness * 1.1 + 0.05,
            0.55,
        );

        // Draw soft glow behind directory node
        let glow_color = dir_color.with_alpha(0.1);
        renderer.draw_disc(screen_pos, radius * 1.5, glow_color);

        // Draw directory as a hollow circle with better styling
        renderer.draw_circle(screen_pos, radius, 1.5, dir_color);

        // Small filled center dot
        let center_color = dir_color.with_alpha(0.4);
        renderer.draw_disc(screen_pos, radius * 0.25, center_color);

        // Draw connection to parent with curved branches
        // LOD: Skip branches at very low zoom levels
        if render_branches {
            if let Some(parent_pos) = dir.parent_position() {
                let parent_screen = camera.world_to_screen(parent_pos);

                // Branch width based on depth (thicker near root)
                let branch_width = (1.5 - depth_factor * 0.5).max(0.8);

                // Branch color with gradient effect
                let branch_color = Color::new(
                    dir_color.r * 1.1,
                    dir_color.g * 1.1,
                    dir_color.b * 1.2,
                    0.35,
                );

                draw_curved_branch(
                    renderer,
                    parent_screen,
                    screen_pos,
                    branch_width,
                    branch_color,
                    use_curves,
                );
            }
        }

        // Draw directory name label if enabled and within depth limit
        // LOD: Also check screen radius threshold for readability
        if !hide_dirnames && dir.depth() <= dir_name_depth && radius >= LOD_MIN_DIR_LABEL_RADIUS {
            if let Some(fid) = font_id {
                let name = dir.name();
                let label_pos = Vec2::new(
                    screen_pos.x + radius + 4.0,
                    screen_pos.y - dir_font_size * 0.3,
                );
                // Label with subtle shadow
                let shadow_color = Color::new(0.0, 0.0, 0.0, 0.4);
                renderer.draw_text(
                    name,
                    label_pos + Vec2::new(1.0, 1.0),
                    fid,
                    dir_font_size,
                    shadow_color,
                );
                let label_color = Color::new(0.75, 0.78, 0.85, 0.7);
                renderer.draw_text(name, label_pos, fid, dir_font_size, label_color);
            }
        }
    }
}

/// Render file entities with enhanced visuals and LOD optimization.
///
/// Uses a reusable buffer for label candidates to avoid per-frame allocations.
/// The buffer stores (`FileId`, `screen_pos`, radius, alpha, priority) tuples.
fn render_files(
    renderer: &mut SoftwareRenderer,
    scene: &Scene,
    camera: &Camera,
    visible_ids: &[FileId],
    args: &Args,
    font_id: Option<FontId>,
    label_candidates: &mut Vec<(FileId, Vec2, f32, f32, f32)>,
) {
    let show_filenames = !args.hide_filenames;
    let hide_tree = args.hide_tree;
    let file_font_size = args.font_size * 0.8;
    let camera_zoom = camera.zoom();

    // Use curves when zoomed out (better visual, acceptable perf)
    let use_curves = camera_zoom < 0.8;

    // LOD: Pre-compute whether we should render file branches at this zoom level
    let render_branches = !hide_tree && camera_zoom >= LOD_MIN_ZOOM_FOR_FILE_BRANCHES;

    // Clear and reuse the label candidates buffer (zero-allocation)
    label_candidates.clear();

    for &file_id in visible_ids {
        let Some(file) = scene.get_file(file_id) else {
            continue;
        };

        if file.alpha() < 0.01 {
            continue;
        }

        let screen_pos = camera.world_to_screen(file.position());
        let radius = file.radius() * camera_zoom;

        // LOD: Skip files that are too small to be visible on screen
        if radius < LOD_MIN_FILE_RADIUS {
            continue;
        }

        let color = file.current_color().with_alpha(file.alpha());
        let effective_radius = radius.max(2.0);

        // Draw connection to parent directory first (behind file)
        // LOD: Skip branches at very low zoom levels
        if render_branches {
            if let Some(dir) = scene.directories().get(file.directory()) {
                let dir_screen = camera.world_to_screen(dir.position());

                // Branch color matches file color for visual cohesion
                let branch_color = Color::new(
                    color.r * 0.7,
                    color.g * 0.7,
                    color.b * 0.7,
                    0.25 * file.alpha(),
                );

                draw_curved_branch(
                    renderer,
                    dir_screen,
                    screen_pos,
                    0.8,
                    branch_color,
                    use_curves,
                );
            }
        }

        // Draw soft glow behind file (especially for active/touched files)
        let is_touched = file.touch_time() > 0.0;
        let glow_intensity = if is_touched { 0.25 } else { 0.08 };
        let glow_color = color.with_alpha(glow_intensity * file.alpha());
        renderer.draw_disc(screen_pos, effective_radius * 2.0, glow_color);

        // Draw file as a filled disc with slight border effect
        // Outer ring (darker)
        let border_color = Color::new(color.r * 0.6, color.g * 0.6, color.b * 0.6, color.a);
        renderer.draw_disc(screen_pos, effective_radius + 0.5, border_color);

        // Main file disc
        renderer.draw_disc(screen_pos, effective_radius, color);

        // Bright highlight for active/touched files
        if is_touched {
            let highlight = Color::new(1.0, 1.0, 1.0, 0.3 * file.alpha());
            renderer.draw_disc(screen_pos, effective_radius * 0.5, highlight);
        }

        // Collect label candidate if conditions are met
        // LOD: Only add label candidates for files large enough to be readable
        if show_filenames
            && file.alpha() > 0.3
            && camera_zoom > 0.15
            && radius >= LOD_MIN_FILE_LABEL_RADIUS
        {
            // Priority based on visibility and activity (higher = more important)
            let activity_bonus = if is_touched { 100.0 } else { 0.0 };
            let priority = file.radius() * file.alpha() * 10.0 + activity_bonus;
            // Store FileId instead of &str to enable buffer reuse across frames
            label_candidates.push((
                file_id,
                screen_pos,
                effective_radius,
                file.alpha(),
                priority,
            ));
        }
    }

    // Draw labels with collision avoidance
    if let Some(fid) = font_id {
        render_file_labels(
            renderer,
            scene,
            label_candidates,
            camera_zoom,
            file_font_size,
            fid,
        );
    }
}

/// Renders file labels with collision avoidance and adaptive visibility.
///
/// Uses `FileId` in candidates buffer to enable zero-allocation across frames.
/// Looks up file names from the scene when rendering.
fn render_file_labels(
    renderer: &mut SoftwareRenderer,
    scene: &Scene,
    candidates: &mut [(FileId, Vec2, f32, f32, f32)],
    camera_zoom: f32,
    font_size: f32,
    font_id: FontId,
) {
    // Sort by priority (highest first) - priority is the 5th element (index 4)
    candidates.sort_by(|a, b| b.4.partial_cmp(&a.4).unwrap_or(std::cmp::Ordering::Equal));

    // Create label placer with zoom-based limit
    let mut placer = LabelPlacer::new(camera_zoom);

    for &(file_id, screen_pos, radius, alpha, _priority) in candidates.iter() {
        if !placer.can_place_more() {
            break;
        }

        // Look up the file name from the scene
        let Some(file) = scene.get_file(file_id) else {
            continue;
        };
        let name = file.name();

        // Calculate label dimensions
        let text_width = estimate_text_width(name, font_size);
        let text_height = font_size;

        // Primary position: right of the file
        let primary_pos = Vec2::new(screen_pos.x + radius + 3.0, screen_pos.y - font_size * 0.3);

        // Try to place with fallback positions
        if let Some(label_pos) =
            placer.try_place_with_fallback(primary_pos, text_width, text_height, screen_pos, radius)
        {
            // Draw shadow for readability
            let shadow_color = Color::new(0.0, 0.0, 0.0, 0.5 * alpha);
            renderer.draw_text(
                name,
                label_pos + Vec2::new(1.0, 1.0),
                font_id,
                font_size,
                shadow_color,
            );

            // Draw label
            let label_color = Color::new(0.95, 0.95, 0.95, 0.8 * alpha);
            renderer.draw_text(name, label_pos, font_id, font_size, label_color);
        }
    }
}

/// Render action beams (user to file connections) with enhanced glow effects.
fn render_actions(renderer: &mut SoftwareRenderer, scene: &Scene, camera: &Camera) {
    let zoom = camera.zoom();

    for action in scene.actions() {
        let user_opt = scene.get_user(action.user());
        let file_opt = scene.get_file(action.file());

        if let (Some(user), Some(file)) = (user_opt, file_opt) {
            let user_screen = camera.world_to_screen(user.position());
            let file_screen = camera.world_to_screen(file.position());

            let beam_color = action.beam_color();

            // Use enhanced beam drawing with glow
            draw_action_beam(
                renderer,
                user_screen,
                file_screen,
                action.progress(),
                beam_color,
                zoom,
            );
        }
    }
}

/// Render user entities with stylized avatar shapes and LOD optimization.
#[allow(clippy::too_many_arguments)]
fn render_users(
    renderer: &mut SoftwareRenderer,
    scene: &Scene,
    camera: &Camera,
    visible_ids: &[UserId],
    args: &Args,
    font_id: Option<FontId>,
    avatar_registry: &AvatarRegistry,
) {
    let show_usernames = !args.hide_usernames;
    let name_font_size = args.font_size;
    let camera_zoom = camera.zoom();

    for &user_id in visible_ids {
        let Some(user) = scene.get_user(user_id) else {
            continue;
        };

        if user.alpha() < 0.01 {
            continue;
        }

        let screen_pos = camera.world_to_screen(user.position());
        let radius = user.radius() * camera_zoom;

        // LOD: Skip users that are too small on screen
        if radius < LOD_MIN_USER_RADIUS {
            continue;
        }

        let color = user.display_color();
        let effective_radius = radius.max(5.0);

        // Check for avatar texture - use textured quad if available
        if let Some(avatar_id) = avatar_registry.get_avatar_id(user.name()) {
            // Draw glow behind avatar for active users
            if user.is_active() {
                for i in 0..3 {
                    let glow_radius = effective_radius * (1.3 + i as f32 * 0.15);
                    let glow_alpha = user.alpha() * 0.15 * (1.0 - i as f32 * 0.25);
                    let glow_color = color.with_alpha(glow_alpha);
                    renderer.draw_disc(screen_pos, glow_radius, glow_color);
                }
            }

            // Draw circular background/border
            let border_color =
                Color::new(color.r * 0.5, color.g * 0.5, color.b * 0.5, user.alpha());
            renderer.draw_disc(screen_pos, effective_radius + 2.0, border_color);

            // Draw avatar texture
            let half_size = effective_radius * 0.9;
            let bounds = Bounds::from_center_half_extents(screen_pos, Vec2::splat(half_size));
            let tint = Color::new(1.0, 1.0, 1.0, user.alpha());
            renderer.draw_quad(bounds, Some(avatar_id), tint);

            // Active ring
            if user.is_active() {
                let ring_color = Color::new(1.0, 1.0, 1.0, 0.4 * user.alpha());
                renderer.draw_circle(screen_pos, effective_radius * 1.15, 1.5, ring_color);
            }
        } else {
            // Draw stylized avatar shape (modern person silhouette)
            draw_avatar_shape(
                renderer,
                screen_pos,
                effective_radius,
                color,
                user.is_active(),
                user.alpha(),
            );

            // Draw initials on larger avatars
            if effective_radius > 14.0 {
                if let Some(fid) = font_id {
                    let initials = get_initials(user.name());
                    let initial_font_size = (effective_radius * 0.55).clamp(8.0, 18.0);
                    let text_width = initials.len() as f32 * initial_font_size * 0.5;
                    // Position initials in the body area
                    let initial_pos = Vec2::new(
                        screen_pos.x - text_width * 0.5,
                        screen_pos.y + effective_radius * 0.15,
                    );
                    let initial_color = Color::new(1.0, 1.0, 1.0, 0.85 * user.alpha());
                    renderer.draw_text(
                        &initials,
                        initial_pos,
                        fid,
                        initial_font_size,
                        initial_color,
                    );
                }
            }
        }

        // Draw username label
        // LOD: Skip labels for users that are too small on screen
        if show_usernames && radius >= LOD_MIN_USER_LABEL_RADIUS {
            if let Some(fid) = font_id {
                let name = user.name();
                let label_pos = Vec2::new(
                    screen_pos.x + effective_radius + 5.0,
                    screen_pos.y - name_font_size * 0.3,
                );
                // Add subtle shadow for better readability
                let shadow_color = Color::new(0.0, 0.0, 0.0, 0.5 * user.alpha());
                renderer.draw_text(
                    name,
                    label_pos + Vec2::new(1.0, 1.0),
                    fid,
                    name_font_size,
                    shadow_color,
                );
                let label_color = Color::new(1.0, 1.0, 1.0, 0.9 * user.alpha());
                renderer.draw_text(name, label_pos, fid, name_font_size, label_color);
            }
        }
    }
}

/// Render UI overlays (progress bar, stats, legend, watermark, etc.).
#[allow(clippy::too_many_arguments)]
fn render_overlays(
    renderer: &mut SoftwareRenderer,
    playback: &PlaybackState,
    args: &Args,
    font_id: Option<FontId>,
    commits: &[Commit],
    current_commit: usize,
    scene: &mut Scene,
    logo_texture: Option<TextureId>,
    logo_dimensions: Option<(u32, u32)>,
    logo_offset: (i32, i32),
    watermark: &WatermarkSettings,
) {
    let width = renderer.width() as f32;
    let height = renderer.height() as f32;

    // Draw pause indicator
    if playback.paused {
        let pause_color = Color::new(1.0, 1.0, 1.0, 0.7);
        renderer.draw_quad(
            Bounds::new(Vec2::new(20.0, 20.0), Vec2::new(28.0, 40.0)),
            None,
            pause_color,
        );
        renderer.draw_quad(
            Bounds::new(Vec2::new(34.0, 20.0), Vec2::new(42.0, 40.0)),
            None,
            pause_color,
        );
    }

    // Draw progress bar
    if !args.hide_progress && !commits.is_empty() {
        render_progress_bar(renderer, current_commit, commits.len(), width, height);
    }

    // Draw stats indicators
    render_stats_indicators(renderer, scene, current_commit, commits.len());

    // Draw text overlays
    if let Some(fid) = font_id {
        render_text_overlays(
            renderer,
            playback,
            args,
            fid,
            commits,
            current_commit,
            scene,
        );
    }

    // Draw file extension legend
    if !args.hide_legend {
        if let Some(fid) = font_id {
            render_legend(renderer, scene, fid, args.font_size, width, height);
        }
    }

    // Draw logo
    if let (Some(logo_tex), Some((logo_w, logo_h))) = (logo_texture, logo_dimensions) {
        render_logo(renderer, logo_tex, logo_w, logo_h, logo_offset, width);
    }

    // Draw watermark (rendered last to appear on top)
    render_watermark(renderer, watermark, font_id, width, height);
}

/// Render progress bar at bottom of screen.
fn render_progress_bar(
    renderer: &mut SoftwareRenderer,
    current_commit: usize,
    total_commits: usize,
    width: f32,
    height: f32,
) {
    let bar_height = 4.0;
    let progress = current_commit as f32 / total_commits.max(1) as f32;

    // Background bar
    renderer.draw_quad(
        Bounds::new(
            Vec2::new(0.0, height - bar_height),
            Vec2::new(width, height),
        ),
        None,
        Color::new(0.2, 0.2, 0.2, 0.5),
    );

    // Progress bar
    renderer.draw_quad(
        Bounds::new(
            Vec2::new(0.0, height - bar_height),
            Vec2::new(width * progress, height),
        ),
        None,
        Color::new(0.3, 0.6, 1.0, 0.8),
    );
}

/// Render stats indicators in corner.
fn render_stats_indicators(
    renderer: &mut SoftwareRenderer,
    scene: &Scene,
    current_commit: usize,
    total_commits: usize,
) {
    let stats_color = Color::new(1.0, 1.0, 1.0, 0.6);
    let file_count = scene.file_count();
    let user_count = scene.user_count();

    let indicator_height = 8.0;
    let max_width = 100.0;

    // Commit progress indicator
    if total_commits > 0 {
        let progress = current_commit as f32 / total_commits as f32;
        renderer.draw_quad(
            Bounds::new(
                Vec2::new(10.0, 50.0),
                Vec2::new(10.0 + max_width * progress, 50.0 + indicator_height),
            ),
            None,
            stats_color,
        );
    }

    // File count indicator (logarithmic scale)
    if file_count > 0 {
        let file_bar = ((file_count as f32).ln() / 10.0).min(1.0);
        renderer.draw_quad(
            Bounds::new(
                Vec2::new(10.0, 62.0),
                Vec2::new(10.0 + max_width * file_bar, 62.0 + indicator_height),
            ),
            None,
            Color::new(0.3, 1.0, 0.3, 0.6),
        );
    }

    // User count indicator
    if user_count > 0 {
        let user_bar = ((user_count as f32).ln() / 5.0).min(1.0);
        renderer.draw_quad(
            Bounds::new(
                Vec2::new(10.0, 74.0),
                Vec2::new(10.0 + max_width * user_bar, 74.0 + indicator_height),
            ),
            None,
            Color::new(1.0, 0.6, 0.3, 0.6),
        );
    }
}

/// Render text overlays (title, date, stats).
#[allow(clippy::too_many_arguments)]
fn render_text_overlays(
    renderer: &mut SoftwareRenderer,
    playback: &PlaybackState,
    args: &Args,
    font_id: FontId,
    commits: &[Commit],
    current_commit: usize,
    scene: &Scene,
) {
    let font_size = args.font_size;
    let text_color = Color::new(1.0, 1.0, 1.0, 0.9);
    let height = renderer.height() as f32;
    let width = renderer.width() as f32;

    // Title (top-center)
    if let Some(ref title) = args.title {
        let title_size = font_size * 1.5;
        let title_x = (width / 2.0) - (title.len() as f32 * title_size * 0.3);
        renderer.draw_text(
            title,
            Vec2::new(title_x.max(10.0), 20.0),
            font_id,
            title_size,
            text_color,
        );
    }

    // Date display (bottom-left, above progress bar)
    if !args.hide_date && !commits.is_empty() {
        if let Some(commit) = commits.get(current_commit.saturating_sub(1).max(0)) {
            let date_str = crate::helpers::format_timestamp(commit.timestamp);
            renderer.draw_text(
                &date_str,
                Vec2::new(10.0, height - 30.0),
                font_id,
                font_size,
                text_color.with_alpha(0.7),
            );
        }
    }

    // Current commit info (bottom-left, above date)
    if current_commit > 0 {
        if let Some(commit) = commits.get(current_commit - 1) {
            // Author name
            renderer.draw_text(
                &commit.author,
                Vec2::new(10.0, height - 50.0),
                font_id,
                font_size,
                text_color.with_alpha(0.8),
            );

            // File count in commit
            let files_text = format!("{} files", commit.files.len());
            renderer.draw_text(
                &files_text,
                Vec2::new(10.0, height - 70.0),
                font_id,
                font_size * 0.9,
                text_color.with_alpha(0.6),
            );
        }
    }

    // Speed indicator (top-right, only if not 1.0x)
    if (playback.speed - 1.0).abs() > 0.01 {
        let speed_text = format!("{:.1}x", playback.speed);
        renderer.draw_text(
            &speed_text,
            Vec2::new(width - 60.0, 20.0),
            font_id,
            font_size,
            text_color.with_alpha(0.7),
        );
    }

    // Pause indicator text
    if playback.paused {
        renderer.draw_text(
            "PAUSED",
            Vec2::new(50.0, 24.0),
            font_id,
            font_size,
            text_color.with_alpha(0.7),
        );
    }

    // Stats text
    let file_count = scene.file_count();
    let user_count = scene.user_count();
    let total_commits = commits.len();
    let stats_text = format!(
        "{current_commit}/{total_commits} commits | {file_count} files | {user_count} users"
    );
    renderer.draw_text(
        &stats_text,
        Vec2::new(120.0, 54.0),
        font_id,
        font_size * 0.8,
        text_color.with_alpha(0.5),
    );
}

/// Render file extension legend.
fn render_legend(
    renderer: &mut SoftwareRenderer,
    scene: &mut Scene,
    font_id: FontId,
    font_size: f32,
    width: f32,
    height: f32,
) {
    let text_color = Color::new(1.0, 1.0, 1.0, 0.9);
    let legend_font_size = font_size * 0.8;
    let legend_padding = 10.0;
    let legend_entry_height = legend_font_size + 4.0;
    let legend_color_size = legend_font_size * 0.7;

    // Get file extension stats (limited to top 10)
    let stats = scene.file_extension_stats();
    let max_legend_entries = 10;
    let legend_entries: Vec<_> = stats.iter().take(max_legend_entries).collect();

    if legend_entries.is_empty() {
        return;
    }

    let legend_height = legend_entries.len() as f32 * legend_entry_height + legend_padding * 2.0;
    let legend_width = 120.0;
    let legend_x = width - legend_width - legend_padding;
    let legend_y = height - legend_height - 20.0;

    // Background
    renderer.draw_quad(
        Bounds::new(
            Vec2::new(legend_x, legend_y),
            Vec2::new(legend_x + legend_width, legend_y + legend_height),
        ),
        None,
        Color::new(0.0, 0.0, 0.0, 0.5),
    );

    // Title
    renderer.draw_text(
        "File Types",
        Vec2::new(legend_x + legend_padding, legend_y + legend_padding),
        font_id,
        legend_font_size,
        text_color.with_alpha(0.8),
    );

    // Entries
    for (i, (ext, count)) in legend_entries.iter().enumerate() {
        let entry_y = legend_y + legend_padding + legend_entry_height * (i as f32 + 1.0);

        // Color swatch
        let ext_color = FileNode::color_from_extension(ext);
        renderer.draw_quad(
            Bounds::new(
                Vec2::new(legend_x + legend_padding, entry_y + 2.0),
                Vec2::new(
                    legend_x + legend_padding + legend_color_size,
                    entry_y + 2.0 + legend_color_size,
                ),
            ),
            None,
            ext_color,
        );

        // Extension name and count
        let ext_display = if ext.len() > 8 {
            format!("{}..", &ext[..6])
        } else {
            ext.clone()
        };
        let entry_text = format!("{ext_display} ({count})");
        renderer.draw_text(
            &entry_text,
            Vec2::new(legend_x + legend_padding + legend_color_size + 4.0, entry_y),
            font_id,
            legend_font_size * 0.9,
            text_color.with_alpha(0.7),
        );
    }
}

/// Render logo in top-right corner.
fn render_logo(
    renderer: &mut SoftwareRenderer,
    texture: TextureId,
    logo_width: u32,
    logo_height: u32,
    offset: (i32, i32),
    viewport_width: f32,
) {
    let (offset_x, offset_y) = offset;
    let logo_x = viewport_width - logo_width as f32 - offset_x as f32;
    let logo_y = offset_y as f32;

    let logo_bounds = Bounds::new(
        Vec2::new(logo_x, logo_y),
        Vec2::new(logo_x + logo_width as f32, logo_y + logo_height as f32),
    );
    renderer.draw_quad(logo_bounds, Some(texture), Color::WHITE);
}

/// Render watermark overlay.
///
/// The watermark is positioned in one of the four corners with configurable
/// margin, and renders primary text with optional secondary text below.
fn render_watermark(
    renderer: &mut SoftwareRenderer,
    watermark: &WatermarkSettings,
    font_id: Option<FontId>,
    width: f32,
    height: f32,
) {
    // Skip if disabled or no font
    if !watermark.enabled || !watermark.has_text() {
        return;
    }
    let Some(fid) = font_id else {
        return;
    };

    let text_color = watermark.effective_color();
    let subtext_color = text_color.with_alpha(text_color.a * 0.8);
    let font_size = watermark.font_size;
    let margin = watermark.margin;

    // Estimate text widths
    let text_width = estimate_text_width(&watermark.text, font_size);
    let subtext_width = watermark
        .subtext
        .as_ref()
        .map_or(0.0, |s| estimate_text_width(s, font_size * 0.85));
    let max_width = text_width.max(subtext_width);

    // Line height and total block height
    let line_height = font_size * 1.2;
    let total_height = if watermark.subtext.is_some() {
        line_height * 2.0
    } else {
        line_height
    };

    // Calculate position based on corner
    let (x, y) = match watermark.position {
        WatermarkPosition::TopLeft => (margin, margin),
        WatermarkPosition::TopRight => (width - max_width - margin, margin),
        WatermarkPosition::BottomLeft => (margin, height - total_height - margin),
        WatermarkPosition::BottomRight => {
            (width - max_width - margin, height - total_height - margin)
        }
    };

    // Draw primary text
    renderer.draw_text(&watermark.text, Vec2::new(x, y), fid, font_size, text_color);

    // Draw secondary text (subtext) if present
    if let Some(ref subtext) = watermark.subtext {
        let subtext_x = match watermark.position {
            WatermarkPosition::TopLeft | WatermarkPosition::BottomLeft => x,
            WatermarkPosition::TopRight | WatermarkPosition::BottomRight => {
                // Right-align the subtext
                x + (max_width - subtext_width)
            }
        };
        renderer.draw_text(
            subtext,
            Vec2::new(subtext_x, y + line_height),
            fid,
            font_size * 0.85,
            subtext_color,
        );
    }
}

/// Apply post-processing effects.
/// Both effects use pre-allocated buffers for zero per-frame allocation.
fn apply_effects(
    renderer: &mut SoftwareRenderer,
    shadow: Option<&mut ShadowEffect>,
    bloom: Option<&mut BloomEffect>,
    hide_bloom: bool,
) {
    let w = renderer.width() as usize;
    let h = renderer.height() as usize;

    // Apply shadow effect if enabled (uses pre-allocated buffers for zero allocation)
    if let Some(shadow_effect) = shadow {
        shadow_effect.apply(renderer.pixels_mut(), w, h);
    }

    // Apply bloom effect if enabled (uses pre-allocated buffers for zero allocation)
    if !hide_bloom {
        if let Some(bloom_effect) = bloom {
            bloom_effect.apply(renderer.pixels_mut(), w, h);
        }
    }
}

/// Present the rendered frame to the window.
pub fn present_frame(app: &mut App) {
    let Some(renderer) = &app.renderer else {
        return;
    };
    let Some(surface) = &mut app.surface else {
        return;
    };

    let width = renderer.width();
    let height = renderer.height();

    // Get the softbuffer buffer
    let mut buffer = match surface.buffer_mut() {
        Ok(b) => b,
        Err(e) => {
            eprintln!("Failed to get surface buffer: {e}");
            return;
        }
    };

    // Copy renderer pixels to softbuffer
    let pixels = renderer.pixels();
    let buffer_len = (width * height) as usize;

    if buffer.len() >= buffer_len && pixels.len() >= buffer_len {
        buffer[..buffer_len].copy_from_slice(&pixels[..buffer_len]);
    }

    // Present the buffer
    if let Err(e) = buffer.present() {
        eprintln!("Failed to present buffer: {e}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rource_render::visual::{catmull_rom_interpolate, catmull_rom_spline, create_branch_curve};

    // ========================================================================
    // Existing tests
    // ========================================================================

    #[test]
    fn test_get_initials() {
        assert_eq!(get_initials("John Doe"), "JD");
        assert_eq!(get_initials("Alice"), "A");
    }

    #[test]
    fn test_catmull_rom_spline_empty() {
        let result = catmull_rom_spline(&[], 10);
        assert!(result.is_empty());
    }

    #[test]
    fn test_catmull_rom_spline_single_point() {
        let points = vec![Vec2::new(5.0, 5.0)];
        let result = catmull_rom_spline(&points, 10);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], Vec2::new(5.0, 5.0));
    }

    #[test]
    fn test_catmull_rom_spline_two_points() {
        let points = vec![Vec2::new(0.0, 0.0), Vec2::new(10.0, 10.0)];
        let result = catmull_rom_spline(&points, 10);
        assert_eq!(result.len(), 2);
        assert_eq!(result[0], Vec2::new(0.0, 0.0));
        assert_eq!(result[1], Vec2::new(10.0, 10.0));
    }

    #[test]
    fn test_catmull_rom_spline_multiple_points() {
        let points = vec![
            Vec2::new(0.0, 0.0),
            Vec2::new(10.0, 5.0),
            Vec2::new(20.0, 0.0),
        ];
        let result = catmull_rom_spline(&points, 5);
        assert!(result.len() > 3);
        assert_eq!(result[0], points[0]);
        assert_eq!(*result.last().unwrap(), *points.last().unwrap());
    }

    #[test]
    fn test_catmull_rom_interpolate_endpoints() {
        let p0 = Vec2::new(0.0, 0.0);
        let p1 = Vec2::new(1.0, 1.0);
        let p2 = Vec2::new(2.0, 0.0);
        let p3 = Vec2::new(3.0, 1.0);

        let result = catmull_rom_interpolate(p0, p1, p2, p3, 0.0);
        assert!((result.x - p1.x).abs() < 0.001);
        assert!((result.y - p1.y).abs() < 0.001);

        let result = catmull_rom_interpolate(p0, p1, p2, p3, 1.0);
        assert!((result.x - p2.x).abs() < 0.001);
        assert!((result.y - p2.y).abs() < 0.001);
    }

    #[test]
    fn test_create_branch_curve_short_distance() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(0.5, 0.5);
        let result = create_branch_curve(start, end, 0.4);
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_create_branch_curve_normal_distance() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let result = create_branch_curve(start, end, 0.4);
        assert!(result.len() > 2);
        assert_eq!(result[0], start);
        assert_eq!(*result.last().unwrap(), end);
    }

    // ========================================================================
    // Directory Rendering Helper Tests
    // ========================================================================

    #[test]
    fn test_compute_dir_depth_factor_zero() {
        assert!((compute_dir_depth_factor(0) - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_dir_depth_factor_mid() {
        assert!((compute_dir_depth_factor(3) - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_compute_dir_depth_factor_capped() {
        // Depth 6 should give 1.0, depth 10 should also give 1.0 (capped)
        assert!((compute_dir_depth_factor(6) - 1.0).abs() < 0.001);
        assert!((compute_dir_depth_factor(10) - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_dir_base_brightness() {
        // At depth_factor=0 (root), brightness is highest
        let brightness_root = compute_dir_base_brightness(0.0);
        // At depth_factor=1 (deep), brightness is lowest
        let brightness_deep = compute_dir_base_brightness(1.0);
        assert!(brightness_root > brightness_deep);
        assert!((brightness_root - 0.35).abs() < 0.001);
        assert!((brightness_deep - 0.25).abs() < 0.001);
    }

    #[test]
    fn test_compute_dir_color_structure() {
        let color = compute_dir_color(0);
        assert!(color.r > 0.0 && color.r < 1.0);
        assert!(color.g > 0.0 && color.g < 1.0);
        assert!(color.b > 0.0 && color.b < 1.0);
        assert!((color.a - 0.55).abs() < 0.001);
    }

    #[test]
    fn test_compute_dir_color_blue_tint() {
        // Directory color should have a slight blue tint (b > g > r)
        let color = compute_dir_color(3);
        assert!(color.b >= color.g);
    }

    #[test]
    fn test_compute_dir_glow_color() {
        let dir_color = Color::new(0.5, 0.6, 0.7, 0.55);
        let glow = compute_dir_glow_color(dir_color);
        assert!((glow.r - dir_color.r).abs() < 0.001);
        assert!((glow.a - 0.1).abs() < 0.001);
    }

    #[test]
    fn test_compute_dir_center_color() {
        let dir_color = Color::new(0.5, 0.6, 0.7, 0.55);
        let center = compute_dir_center_color(dir_color);
        assert!((center.a - 0.4).abs() < 0.001);
    }

    #[test]
    fn test_compute_branch_width() {
        // At root (depth_factor=0), branch is thickest
        assert!((compute_branch_width(0.0) - 1.5).abs() < 0.001);
        // At deep (depth_factor=1), branch is thinnest
        assert!((compute_branch_width(1.0) - 1.0).abs() < 0.001);
        // Never goes below 0.8
        assert!(compute_branch_width(2.0) >= 0.8);
    }

    #[test]
    fn test_compute_dir_branch_color() {
        let dir_color = Color::new(0.3, 0.3, 0.3, 0.55);
        let branch = compute_dir_branch_color(dir_color);
        // Branch is brighter (multiplied by 1.1-1.2)
        assert!(branch.r > dir_color.r);
        assert!(branch.g > dir_color.g);
        assert!(branch.b > dir_color.b);
        assert!((branch.a - 0.35).abs() < 0.001);
    }

    #[test]
    fn test_should_render_dir_root_always() {
        // Root (depth=0) always renders regardless of radius
        assert!(should_render_dir(0.001, 0));
        assert!(should_render_dir(0.0, 0));
    }

    #[test]
    fn test_should_render_dir_by_radius() {
        // Non-root needs minimum radius
        assert!(!should_render_dir(0.01, 1));
        assert!(should_render_dir(0.1, 1));
    }

    #[test]
    fn test_should_render_dir_branches() {
        // Hidden tree should not render
        assert!(!should_render_dir_branches(1.0, true));
        // Low zoom should not render
        assert!(!should_render_dir_branches(0.005, false));
        // Normal zoom should render
        assert!(should_render_dir_branches(0.1, false));
    }

    #[test]
    fn test_should_render_dir_label() {
        // Hidden dirnames
        assert!(!should_render_dir_label(true, 0, 3, 10.0));
        // Depth exceeds limit
        assert!(!should_render_dir_label(false, 5, 3, 10.0));
        // Radius too small
        assert!(!should_render_dir_label(false, 1, 3, 2.0));
        // Should render
        assert!(should_render_dir_label(false, 1, 3, 10.0));
    }

    #[test]
    fn test_compute_dir_label_position() {
        let pos = compute_dir_label_position(Vec2::new(100.0, 100.0), 10.0, 12.0);
        assert!((pos.x - 114.0).abs() < 0.001); // 100 + 10 + 4
        assert!((pos.y - 96.4).abs() < 0.1); // 100 - 12*0.3
    }

    // ========================================================================
    // File Rendering Helper Tests
    // ========================================================================

    #[test]
    fn test_compute_effective_file_radius() {
        assert!((compute_effective_file_radius(5.0) - 5.0).abs() < 0.001);
        assert!((compute_effective_file_radius(0.5) - 2.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_file_glow_intensity() {
        assert!((compute_file_glow_intensity(true) - 0.25).abs() < 0.001);
        assert!((compute_file_glow_intensity(false) - 0.08).abs() < 0.001);
    }

    #[test]
    fn test_compute_file_glow_color() {
        let color = Color::new(1.0, 0.5, 0.0, 1.0);
        let glow = compute_file_glow_color(color, 0.25, 0.8);
        assert!((glow.r - 1.0).abs() < 0.001);
        assert!((glow.a - 0.2).abs() < 0.001); // 0.25 * 0.8
    }

    #[test]
    fn test_compute_file_border_color() {
        let color = Color::new(1.0, 0.5, 0.25, 0.9);
        let border = compute_file_border_color(color);
        assert!((border.r - 0.6).abs() < 0.001);
        assert!((border.g - 0.3).abs() < 0.001);
        assert!((border.a - 0.9).abs() < 0.001);
    }

    #[test]
    fn test_compute_file_label_priority() {
        // Active file gets bonus
        let active = compute_file_label_priority(5.0, 1.0, true);
        let inactive = compute_file_label_priority(5.0, 1.0, false);
        assert!(active > inactive);
        assert!((active - inactive - 100.0).abs() < 0.001);
    }

    #[test]
    fn test_should_render_file() {
        assert!(!should_render_file(0.05));
        assert!(should_render_file(0.2));
    }

    #[test]
    fn test_should_render_file_branches() {
        assert!(!should_render_file_branches(1.0, true));
        assert!(!should_render_file_branches(0.01, false));
        assert!(should_render_file_branches(0.1, false));
    }

    #[test]
    fn test_should_add_file_label() {
        // All conditions must be met
        assert!(!should_add_file_label(false, 0.5, 0.5, 5.0));
        assert!(!should_add_file_label(true, 0.2, 0.5, 5.0));
        assert!(!should_add_file_label(true, 0.5, 0.1, 5.0));
        assert!(!should_add_file_label(true, 0.5, 0.5, 1.0));
        assert!(should_add_file_label(true, 0.5, 0.5, 5.0));
    }

    #[test]
    fn test_compute_file_branch_color() {
        let color = Color::new(1.0, 0.5, 0.0, 1.0);
        let branch = compute_file_branch_color(color, 0.8);
        assert!((branch.r - 0.7).abs() < 0.001);
        assert!((branch.a - 0.2).abs() < 0.001); // 0.25 * 0.8
    }

    // ========================================================================
    // User Rendering Helper Tests
    // ========================================================================

    #[test]
    fn test_compute_effective_user_radius() {
        assert!((compute_effective_user_radius(10.0) - 10.0).abs() < 0.001);
        assert!((compute_effective_user_radius(3.0) - 5.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_user_border_color() {
        let color = Color::new(1.0, 0.5, 0.0, 1.0);
        let border = compute_user_border_color(color, 0.9);
        assert!((border.r - 0.5).abs() < 0.001);
        assert!((border.g - 0.25).abs() < 0.001);
        assert!((border.a - 0.9).abs() < 0.001);
    }

    #[test]
    fn test_compute_user_glow_radius() {
        let r = compute_user_glow_radius(10.0, 0);
        assert!((r - 13.0).abs() < 0.001); // 10 * (1.3 + 0*0.15)
        let r2 = compute_user_glow_radius(10.0, 2);
        assert!((r2 - 16.0).abs() < 0.001); // 10 * (1.3 + 2*0.15)
    }

    #[test]
    fn test_compute_user_glow_alpha() {
        let a = compute_user_glow_alpha(1.0, 0);
        assert!((a - 0.15).abs() < 0.001);
        let a2 = compute_user_glow_alpha(1.0, 2);
        assert!((a2 - 0.075).abs() < 0.001); // 0.15 * (1 - 0.5)
    }

    #[test]
    fn test_compute_initials_font_size() {
        // Clamped between 8 and 18
        assert!((compute_initials_font_size(10.0) - 8.0).abs() < 0.001);
        assert!((compute_initials_font_size(40.0) - 18.0).abs() < 0.001);
        assert!((compute_initials_font_size(25.0) - 13.75).abs() < 0.001);
    }

    #[test]
    fn test_compute_initials_text_width() {
        assert!((compute_initials_text_width(2, 12.0) - 12.0).abs() < 0.001);
        assert!((compute_initials_text_width(3, 10.0) - 15.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_initials_position() {
        let pos = compute_initials_position(Vec2::new(100.0, 100.0), 20.0, 10.0);
        assert!((pos.x - 95.0).abs() < 0.001); // 100 - 10*0.5
        assert!((pos.y - 103.0).abs() < 0.001); // 100 + 20*0.15
    }

    #[test]
    fn test_should_render_user() {
        assert!(!should_render_user(0.2));
        assert!(should_render_user(0.5));
    }

    #[test]
    fn test_should_render_user_label() {
        assert!(!should_render_user_label(false, 10.0));
        assert!(!should_render_user_label(true, 3.0));
        assert!(should_render_user_label(true, 10.0));
    }

    #[test]
    fn test_should_render_initials() {
        assert!(!should_render_initials(10.0));
        assert!(should_render_initials(20.0));
    }

    #[test]
    fn test_compute_user_label_position() {
        let pos = compute_user_label_position(Vec2::new(100.0, 100.0), 15.0, 12.0);
        assert!((pos.x - 120.0).abs() < 0.001); // 100 + 15 + 5
        assert!((pos.y - 96.4).abs() < 0.1); // 100 - 12*0.3
    }

    // ========================================================================
    // Progress Bar Helper Tests
    // ========================================================================

    #[test]
    fn test_compute_progress() {
        assert!((compute_progress(0, 100) - 0.0).abs() < 0.001);
        assert!((compute_progress(50, 100) - 0.5).abs() < 0.001);
        assert!((compute_progress(100, 100) - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_progress_zero_total() {
        // Should not panic, returns 0
        assert!((compute_progress(0, 0) - 0.0).abs() < 0.001);
    }

    // ========================================================================
    // Stats Indicator Helper Tests
    // ========================================================================

    #[test]
    fn test_compute_file_indicator_bar() {
        assert!((compute_file_indicator_bar(0) - 0.0).abs() < 0.001);
        assert!(compute_file_indicator_bar(100) > 0.0);
        // Capped at 1.0
        assert!(compute_file_indicator_bar(100_000) <= 1.0);
    }

    #[test]
    fn test_compute_user_indicator_bar() {
        assert!((compute_user_indicator_bar(0) - 0.0).abs() < 0.001);
        assert!(compute_user_indicator_bar(10) > 0.0);
        // Capped at 1.0
        assert!(compute_user_indicator_bar(10000) <= 1.0);
    }

    // ========================================================================
    // Title/Text Helper Tests
    // ========================================================================

    #[test]
    fn test_compute_title_x_position() {
        let x = compute_title_x_position(800.0, 10, 20.0);
        // (800/2) - (10 * 20 * 0.3) = 400 - 60 = 340
        assert!((x - 340.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_title_x_position_min() {
        // Long title should still be at least 10px from edge
        let x = compute_title_x_position(100.0, 50, 20.0);
        assert!((x - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_should_show_speed_indicator() {
        assert!(!should_show_speed_indicator(1.0));
        assert!(!should_show_speed_indicator(1.005));
        assert!(should_show_speed_indicator(1.5));
        assert!(should_show_speed_indicator(0.5));
    }

    #[test]
    fn test_format_stats_text() {
        let text = format_stats_text(50, 100, 200, 10);
        assert_eq!(text, "50/100 commits | 200 files | 10 users");
    }

    // ========================================================================
    // Legend Helper Tests
    // ========================================================================

    #[test]
    fn test_compute_legend_height() {
        let h = compute_legend_height(5, 20.0, 10.0);
        assert!((h - 120.0).abs() < 0.001); // 5*20 + 2*10
    }

    #[test]
    fn test_compute_legend_position() {
        let (x, y) = compute_legend_position(800.0, 600.0, 120.0, 200.0, 10.0);
        assert!((x - 670.0).abs() < 0.001); // 800 - 120 - 10
        assert!((y - 380.0).abs() < 0.001); // 600 - 200 - 20
    }

    #[test]
    fn test_truncate_extension() {
        assert_eq!(truncate_extension("rs"), "rs");
        assert_eq!(truncate_extension("typescript"), "typesc..");
    }

    // ========================================================================
    // Watermark Helper Tests
    // ========================================================================

    #[test]
    fn test_compute_watermark_total_height() {
        let h1 = compute_watermark_total_height(false, 20.0);
        assert!((h1 - 20.0).abs() < 0.001);
        let h2 = compute_watermark_total_height(true, 20.0);
        assert!((h2 - 40.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_watermark_position_cli_top_left() {
        let (x, y) = compute_watermark_position_cli(
            WatermarkPosition::TopLeft,
            10.0,
            100.0,
            40.0,
            800.0,
            600.0,
        );
        assert!((x - 10.0).abs() < 0.001);
        assert!((y - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_watermark_position_cli_top_right() {
        let (x, y) = compute_watermark_position_cli(
            WatermarkPosition::TopRight,
            10.0,
            100.0,
            40.0,
            800.0,
            600.0,
        );
        assert!((x - 690.0).abs() < 0.001); // 800 - 100 - 10
        assert!((y - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_watermark_position_cli_bottom_left() {
        let (x, y) = compute_watermark_position_cli(
            WatermarkPosition::BottomLeft,
            10.0,
            100.0,
            40.0,
            800.0,
            600.0,
        );
        assert!((x - 10.0).abs() < 0.001);
        assert!((y - 550.0).abs() < 0.001); // 600 - 40 - 10
    }

    #[test]
    fn test_compute_watermark_position_cli_bottom_right() {
        let (x, y) = compute_watermark_position_cli(
            WatermarkPosition::BottomRight,
            10.0,
            100.0,
            40.0,
            800.0,
            600.0,
        );
        assert!((x - 690.0).abs() < 0.001);
        assert!((y - 550.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_subtext_x_left() {
        let x = compute_subtext_x(WatermarkPosition::TopLeft, 10.0, 100.0, 50.0);
        assert!((x - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_compute_subtext_x_right() {
        let x = compute_subtext_x(WatermarkPosition::TopRight, 10.0, 100.0, 50.0);
        assert!((x - 60.0).abs() < 0.001); // 10 + (100 - 50)
    }

    // ========================================================================
    // Label Color Helper Tests
    // ========================================================================

    #[test]
    fn test_compute_label_shadow_color() {
        let shadow = compute_label_shadow_color(0.8);
        assert!((shadow.a - 0.4).abs() < 0.001); // 0.5 * 0.8
    }

    #[test]
    fn test_compute_file_label_color() {
        let color = compute_file_label_color(0.9);
        assert!((color.r - 0.95).abs() < 0.001);
        assert!((color.a - 0.72).abs() < 0.001); // 0.8 * 0.9
    }

    #[test]
    fn test_compute_user_label_color() {
        let color = compute_user_label_color(0.8);
        assert!((color.r - 1.0).abs() < 0.001);
        assert!((color.a - 0.72).abs() < 0.001); // 0.9 * 0.8
    }

    #[test]
    fn test_compute_dir_label_shadow_color() {
        let shadow = compute_dir_label_shadow_color();
        assert!((shadow.a - 0.4).abs() < 0.001);
    }

    #[test]
    fn test_compute_dir_label_color() {
        let color = compute_dir_label_color();
        assert!((color.r - 0.75).abs() < 0.001);
        assert!((color.a - 0.7).abs() < 0.001);
    }

    #[test]
    fn test_label_shadow_constants() {
        assert!((LABEL_SHADOW_COLOR.a - 0.5).abs() < 0.001);
        assert!((LABEL_SHADOW_OFFSET.x - 1.0).abs() < 0.001);
        assert!((LABEL_SHADOW_OFFSET.y - 1.0).abs() < 0.001);
    }
}
