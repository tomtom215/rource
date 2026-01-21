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

use rource_core::entity::DirId;
use rource_core::{FileId, UserId};
use rource_math::{Bounds, Color, Rect, Vec2};
use rource_render::{FontId, Renderer};

use crate::rendering::{draw_action_beam, draw_avatar_shape, draw_curved_branch};

// =============================================================================
// Level-of-Detail (LOD) Constants
// =============================================================================
// These thresholds control when entities are skipped for performance.
// Values are in screen pixels.

/// Minimum screen radius for a file to be rendered at all.
/// Files smaller than this are completely invisible and skipped.
/// Set to 0.5 pixels - below this, the entity cannot contribute a visible pixel.
pub const LOD_MIN_FILE_RADIUS: f32 = 0.5;

/// Minimum screen radius for a directory node to be rendered.
/// Directories are more important landmarks, so we use a lower threshold.
pub const LOD_MIN_DIR_RADIUS: f32 = 0.3;

/// Minimum screen radius for file labels to be rendered.
/// Labels are expensive (text rendering + shadow) so we skip them earlier.
/// At 3.0 pixels radius, the entity is visible but labels would be unreadable.
pub const LOD_MIN_FILE_LABEL_RADIUS: f32 = 3.0;

/// Minimum screen radius for directory labels to be rendered.
pub const LOD_MIN_DIR_LABEL_RADIUS: f32 = 4.0;

/// Minimum screen radius for user avatars to be rendered.
/// Users are key visual elements, so we keep the threshold low.
pub const LOD_MIN_USER_RADIUS: f32 = 1.0;

/// Minimum screen radius for user labels to be rendered.
pub const LOD_MIN_USER_LABEL_RADIUS: f32 = 5.0;

/// Minimum zoom level for rendering file-to-directory connections.
/// Below this zoom, branch lines create visual noise without benefit.
pub const LOD_MIN_ZOOM_FOR_FILE_BRANCHES: f32 = 0.05;

/// Minimum zoom level for rendering directory-to-parent connections.
pub const LOD_MIN_ZOOM_FOR_DIR_BRANCHES: f32 = 0.02;

/// Context shared between rendering phases.
///
/// This struct is passed to all rendering phase functions to provide
/// shared state and configuration without needing to pass many parameters.
#[allow(dead_code)] // Fields may be used by future phases
pub struct RenderContext {
    /// Visible bounds in world space (for culling extensions).
    pub visible_bounds: Bounds,
    /// Camera zoom level.
    pub camera_zoom: f32,
    /// Whether to use curved branches.
    pub use_curves: bool,
    /// Visible directory IDs.
    pub visible_dirs: Vec<DirId>,
    /// Visible file IDs.
    pub visible_files: Vec<FileId>,
    /// Visible user IDs.
    pub visible_users: Vec<UserId>,
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
    let render_branches = ctx.camera_zoom >= LOD_MIN_ZOOM_FOR_DIR_BRANCHES;

    for dir_id in &ctx.visible_dirs {
        if let Some(dir) = scene.directories().get(*dir_id) {
            if !dir.is_visible() {
                continue;
            }

            let screen_pos = camera.world_to_screen(dir.position());
            let radius = dir.radius() * ctx.camera_zoom;

            // LOD: Skip directories that are too small to be visible
            // Root directory (depth 0) is always rendered as it's the anchor point
            if radius < LOD_MIN_DIR_RADIUS && dir.depth() > 0 {
                continue;
            }

            // Enhanced directory styling based on depth
            let depth = dir.depth() as f32;
            let depth_factor = (depth / 6.0).min(1.0);

            // Gradient color with depth
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

            // Draw directory as a hollow circle
            renderer.draw_circle(screen_pos, radius, 1.5, dir_color);

            // Small filled center dot
            let center_color = dir_color.with_alpha(0.4);
            renderer.draw_disc(screen_pos, radius * 0.25, center_color);

            // Draw connection to parent with curved branches
            // LOD: Skip branches at very low zoom levels
            if render_branches {
                if let Some(parent_pos) = dir.parent_position() {
                    let parent_screen = camera.world_to_screen(parent_pos);

                    // Branch width based on depth (thinner for deeper nodes)
                    let branch_width = (1.5 - depth_factor * 0.5).max(0.8);

                    // Depth-based opacity: fades deeper branches to reduce visual noise
                    // opacity = max_opacity * (1.0 - depth_factor * fade_rate)
                    let depth_opacity = ctx.branch_opacity_max
                        * (1.0 - depth_factor * ctx.branch_depth_fade).max(0.05);

                    // Branch color with depth-based opacity
                    let branch_color = Color::new(
                        dir_color.r * 1.1,
                        dir_color.g * 1.1,
                        dir_color.b * 1.2,
                        depth_opacity,
                    );

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

    for dir_id in &ctx.visible_dirs {
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
    let render_branches = ctx.camera_zoom >= LOD_MIN_ZOOM_FOR_FILE_BRANCHES;

    for file_id in &ctx.visible_files {
        if let Some(file) = scene.get_file(*file_id) {
            if file.alpha() < 0.01 {
                continue;
            }

            let screen_pos = camera.world_to_screen(file.position());
            let radius = file.radius() * ctx.camera_zoom;

            // LOD: Skip files that are too small to be visible on screen
            // This provides significant performance gains for large repos at low zoom
            if radius < LOD_MIN_FILE_RADIUS {
                continue;
            }

            let color = file.current_color().with_alpha(file.alpha());
            let effective_radius = radius.max(2.0);

            // Draw connection to parent directory first (behind file)
            // LOD: Skip branches at very low zoom levels where they create visual noise
            if render_branches {
                if let Some(dir) = scene.directories().get(file.directory()) {
                    let dir_screen = camera.world_to_screen(dir.position());

                    // Depth-based opacity for file branches
                    let dir_depth = dir.depth();
                    let depth_factor = (dir_depth as f32 / 6.0).min(1.0);
                    let depth_opacity = (1.0 - depth_factor * ctx.branch_depth_fade).max(0.05);

                    // Branch color matches file color for visual cohesion
                    // Combine file alpha, base opacity, and depth fade
                    let branch_color = Color::new(
                        color.r * 0.7,
                        color.g * 0.7,
                        color.b * 0.7,
                        0.25 * file.alpha() * depth_opacity,
                    );

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

            // Draw soft glow behind file
            let is_touched = file.touch_time() > 0.0;
            let glow_intensity = if is_touched { 0.25 } else { 0.08 };
            let glow_color = color.with_alpha(glow_intensity * file.alpha());
            renderer.draw_disc(screen_pos, effective_radius * 2.0, glow_color);

            // Outer ring (darker border)
            let border_color = Color::new(color.r * 0.6, color.g * 0.6, color.b * 0.6, color.a);
            renderer.draw_disc(screen_pos, effective_radius + 0.5, border_color);

            // Main file disc
            renderer.draw_disc(screen_pos, effective_radius, color);

            // Bright highlight for active/touched files
            if is_touched {
                let highlight = Color::new(1.0, 1.0, 1.0, 0.3 * file.alpha());
                renderer.draw_disc(screen_pos, effective_radius * 0.5, highlight);
            }
        }
    }
}

/// Renders action beams from users to files.
#[inline(never)]
pub fn render_actions<R: Renderer + ?Sized>(
    renderer: &mut R,
    ctx: &RenderContext,
    scene: &rource_core::Scene,
    camera: &rource_core::Camera,
) {
    for action in scene.actions() {
        if action.is_complete() {
            continue;
        }

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
    for user_id in &ctx.visible_users {
        if let Some(user) = scene.get_user(*user_id) {
            if user.alpha() < 0.01 {
                continue;
            }

            let screen_pos = camera.world_to_screen(user.position());
            let raw_radius = user.radius() * ctx.camera_zoom;

            // LOD: Skip users that are too small on screen
            // Users are important visual elements, so we use a low threshold
            if raw_radius < LOD_MIN_USER_RADIUS {
                continue;
            }

            let radius = raw_radius.max(5.0);
            let color = user.display_color();

            draw_avatar_shape(
                renderer,
                screen_pos,
                radius,
                color,
                user.is_active(),
                user.alpha(),
            );
        }
    }
}

/// Renders user name labels.
///
/// Applies LOD (Level-of-Detail) optimization:
/// - Labels are skipped when screen radius < `LOD_MIN_USER_LABEL_RADIUS`
#[inline(never)]
pub fn render_user_labels<R: Renderer + ?Sized>(
    renderer: &mut R,
    ctx: &RenderContext,
    scene: &rource_core::Scene,
    camera: &rource_core::Camera,
) {
    if !ctx.show_labels {
        return;
    }

    let Some(font_id) = ctx.font_id else { return };

    for user_id in &ctx.visible_users {
        if let Some(user) = scene.get_user(*user_id) {
            if user.alpha() < 0.01 {
                continue;
            }

            let screen_pos = camera.world_to_screen(user.position());
            let raw_radius = user.radius() * ctx.camera_zoom;

            // LOD: Skip labels for users that are too small on screen
            if raw_radius < LOD_MIN_USER_LABEL_RADIUS {
                continue;
            }

            let radius = raw_radius.max(5.0);
            let label_pos = Vec2::new(
                screen_pos.x + radius + 5.0,
                screen_pos.y - ctx.font_size * 0.3,
            );
            let alpha = user.alpha();

            // Shadow for better readability
            let shadow_color = Color::new(0.0, 0.0, 0.0, 0.5 * alpha);
            renderer.draw_text(
                user.name(),
                label_pos + Vec2::new(1.0, 1.0),
                font_id,
                ctx.font_size,
                shadow_color,
            );

            let label_color = Color::new(1.0, 1.0, 1.0, 0.9 * alpha);
            renderer.draw_text(user.name(), label_pos, font_id, ctx.font_size, label_color);
        }
    }
}

/// Estimates text width for label placement.
#[inline]
fn estimate_text_width(text: &str, font_size: f32) -> f32 {
    text.len() as f32 * font_size * 0.6
}

/// Label placement helper for collision avoidance.
pub struct LabelPlacer {
    placed_labels: Vec<Rect>,
    max_labels: usize,
}

impl LabelPlacer {
    /// Creates a new label placer.
    pub fn new(camera_zoom: f32) -> Self {
        // Adaptive max labels based on zoom
        let max_labels = if camera_zoom > 1.0 {
            200
        } else if camera_zoom > 0.5 {
            100
        } else {
            50
        };
        Self {
            placed_labels: Vec::with_capacity(max_labels),
            max_labels,
        }
    }

    /// Checks if more labels can be placed.
    pub fn can_place_more(&self) -> bool {
        self.placed_labels.len() < self.max_labels
    }

    /// Tries to place a label, checking for collisions.
    pub fn try_place(&mut self, pos: Vec2, width: f32, height: f32) -> bool {
        let rect = Rect::new(pos.x, pos.y, width, height);

        // Check for collisions
        for placed in &self.placed_labels {
            if rects_intersect(&rect, placed) {
                return false;
            }
        }

        self.placed_labels.push(rect);
        true
    }

    /// Tries to place with fallback positions.
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
/// Applies LOD (Level-of-Detail) optimization:
/// - Labels are skipped when camera zoom is too low (< 0.15)
/// - Labels are skipped for files with screen radius < `LOD_MIN_FILE_LABEL_RADIUS`
/// - Label collision avoidance limits total labels rendered
#[inline(never)]
pub fn render_file_labels<R: Renderer + ?Sized>(
    renderer: &mut R,
    ctx: &RenderContext,
    scene: &rource_core::Scene,
    camera: &rource_core::Camera,
) {
    if !ctx.show_labels || ctx.camera_zoom <= 0.15 {
        return;
    }

    let Some(font_id) = ctx.font_id else { return };

    let file_font_size = ctx.font_size * 0.8;

    // Collect label candidates with priority
    // LOD: Only consider files large enough on screen for readable labels
    let mut label_candidates: Vec<(Vec2, f32, f32, &str, f32)> = Vec::new();
    for file_id in &ctx.visible_files {
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

            label_candidates.push((screen_pos, radius, file.alpha(), file.name(), priority));
        }
    }

    // Sort by priority (highest first)
    label_candidates.sort_by(|a, b| b.4.partial_cmp(&a.4).unwrap_or(std::cmp::Ordering::Equal));

    // Use label placer for collision avoidance
    let mut placer = LabelPlacer::new(ctx.camera_zoom);

    for (screen_pos, radius, alpha, name, _priority) in &label_candidates {
        if !placer.can_place_more() {
            break;
        }

        // Calculate label dimensions
        let text_width = estimate_text_width(name, file_font_size);
        let text_height = file_font_size;

        // Primary position: right of the file
        let primary_pos = Vec2::new(
            screen_pos.x + radius + 3.0,
            screen_pos.y - file_font_size * 0.3,
        );

        // Try to place with fallback positions
        if let Some(label_pos) = placer.try_place_with_fallback(
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

#[cfg(test)]
mod tests {
    use super::*;

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

        // Place at primary position
        placer.try_place(Vec2::new(10.0, 0.0), 50.0, 20.0);

        // Try to place overlapping - should use fallback
        let result = placer.try_place_with_fallback(
            Vec2::new(10.0, 0.0),
            50.0,
            20.0,
            Vec2::new(0.0, 10.0),
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
}
