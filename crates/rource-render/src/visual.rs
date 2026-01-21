//! Shared visual rendering utilities.
//!
//! This module contains common rendering functions used by both CLI and WASM
//! builds to ensure visual parity. All functions are generic over the
//! [`Renderer`] trait.
//!
//! ## Contents
//!
//! - **Spline interpolation**: Catmull-Rom splines for smooth curves
//! - **Branch rendering**: Curved tree branches with glow effects
//! - **Avatar rendering**: Stylized person silhouettes
//! - **Beam rendering**: Action beams from users to files
//!
//! ## Usage
//!
//! ```ignore
//! use rource_render::{visual, Renderer, SoftwareRenderer};
//! use rource_math::{Color, Vec2};
//!
//! let mut renderer = SoftwareRenderer::new(800, 600);
//! renderer.begin_frame();
//!
//! // Draw a curved branch
//! visual::draw_curved_branch(
//!     &mut renderer,
//!     Vec2::new(100.0, 100.0),
//!     Vec2::new(300.0, 200.0),
//!     2.0,
//!     Color::WHITE,
//!     true,
//! );
//!
//! renderer.end_frame();
//! ```

use rource_math::{Color, Vec2};

use crate::Renderer;

// ============================================================================
// Constants
// ============================================================================

/// Number of segments for Catmull-Rom spline interpolation.
pub const SPLINE_SEGMENTS: usize = 12;

/// Curve tension for branch splines (0.0 = straight, 0.5 = natural curves).
pub const BRANCH_CURVE_TENSION: f32 = 0.4;

/// Glow intensity multiplier for action beams.
pub const BEAM_GLOW_INTENSITY: f32 = 0.4;

/// Number of glow layers for beams.
pub const BEAM_GLOW_LAYERS: usize = 3;

// ============================================================================
// Spline Interpolation
// ============================================================================

/// Generates Catmull-Rom spline points between control points.
///
/// Creates smooth curves through the given points using Catmull-Rom
/// interpolation, which passes through all control points.
///
/// # Arguments
///
/// * `points` - Control points to interpolate through (minimum 2 required for output)
/// * `segments_per_span` - Number of interpolated points per span between control points
///
/// # Returns
///
/// Returns the interpolated points. For 0-2 input points, returns a copy of the input.
/// For 3+ points, returns smoothly interpolated spline points.
///
/// # Example
///
/// ```
/// use rource_render::visual::catmull_rom_spline;
/// use rource_math::Vec2;
///
/// let points = vec![
///     Vec2::new(0.0, 0.0),
///     Vec2::new(50.0, 100.0),
///     Vec2::new(100.0, 0.0),
/// ];
/// let curve = catmull_rom_spline(&points, 8);
/// assert!(curve.len() > points.len()); // More points due to interpolation
/// ```
#[must_use]
pub fn catmull_rom_spline(points: &[Vec2], segments_per_span: usize) -> Vec<Vec2> {
    // Handle edge cases
    if points.len() < 2 {
        return points.to_vec();
    }

    if points.len() == 2 {
        return points.to_vec();
    }

    let mut result = Vec::with_capacity(points.len() * segments_per_span);

    // For Catmull-Rom, we need 4 control points for each span
    // Duplicate first and last points to handle edges
    for i in 0..points.len() - 1 {
        let p0 = if i == 0 { points[0] } else { points[i - 1] };
        let p1 = points[i];
        let p2 = points[i + 1];
        let p3 = if i + 2 >= points.len() {
            points[points.len() - 1]
        } else {
            points[i + 2]
        };

        // Generate points along this span
        for j in 0..segments_per_span {
            let t = j as f32 / segments_per_span as f32;
            result.push(catmull_rom_interpolate(p0, p1, p2, p3, t));
        }
    }

    // Add the final point
    if let Some(&last) = points.last() {
        result.push(last);
    }

    result
}

/// Performs Catmull-Rom interpolation between p1 and p2.
///
/// # Arguments
///
/// * `p0` - Control point before the interpolated segment
/// * `p1` - Start of interpolated segment (result at t=0)
/// * `p2` - End of interpolated segment (result at t=1)
/// * `p3` - Control point after the interpolated segment
/// * `t` - Interpolation parameter (0.0 to 1.0)
///
/// # Returns
///
/// The interpolated point on the spline curve.
#[inline]
#[must_use]
pub fn catmull_rom_interpolate(p0: Vec2, p1: Vec2, p2: Vec2, p3: Vec2, t: f32) -> Vec2 {
    let t2 = t * t;
    let t3 = t2 * t;

    // Catmull-Rom basis matrix coefficients
    let c0 = -0.5 * t3 + t2 - 0.5 * t;
    let c1 = 1.5 * t3 - 2.5 * t2 + 1.0;
    let c2 = -1.5 * t3 + 2.0 * t2 + 0.5 * t;
    let c3 = 0.5 * t3 - 0.5 * t2;

    Vec2::new(
        c0 * p0.x + c1 * p1.x + c2 * p2.x + c3 * p3.x,
        c0 * p0.y + c1 * p1.y + c2 * p2.y + c3 * p3.y,
    )
}

/// Creates a curved path between two points with natural-looking curvature.
///
/// The curve bends perpendicular to the line between points, creating
/// an organic tree-branch appearance.
///
/// # Arguments
///
/// * `start` - Starting point of the curve
/// * `end` - Ending point of the curve
/// * `tension` - Curve tension (0.0 = straight, higher = more curved)
///
/// # Returns
///
/// A vector of points along the curved path.
#[must_use]
pub fn create_branch_curve(start: Vec2, end: Vec2, tension: f32) -> Vec<Vec2> {
    let mid = start.lerp(end, 0.5);
    let dir = end - start;
    let length = dir.length();

    if length < 1.0 {
        return vec![start, end];
    }

    // Perpendicular offset for natural curve
    let perp = Vec2::new(-dir.y, dir.x).normalized();
    let offset = perp * length * tension * 0.15;

    // Create control points with slight S-curve
    let ctrl1 = start.lerp(mid, 0.33) + offset * 0.5;
    let ctrl2 = start.lerp(mid, 0.66) + offset;
    let ctrl3 = mid.lerp(end, 0.33) + offset * 0.5;
    let ctrl4 = mid.lerp(end, 0.66);

    catmull_rom_spline(
        &[start, ctrl1, ctrl2, ctrl3, ctrl4, end],
        SPLINE_SEGMENTS / 2,
    )
}

// ============================================================================
// Avatar Drawing
// ============================================================================

/// Draws a stylized avatar shape (modern person silhouette).
///
/// Creates a distinctive, portfolio-quality avatar with:
/// - Circular head with subtle highlight
/// - Rounded body/torso below
/// - Soft glow effect for active users
///
/// # Arguments
///
/// * `renderer` - The renderer to draw with
/// * `center` - Center position of the avatar
/// * `radius` - Radius of the avatar
/// * `color` - Base color of the avatar
/// * `is_active` - Whether the user is currently active (adds glow effect)
/// * `alpha` - Alpha transparency (0.0 - 1.0)
pub fn draw_avatar_shape<R: Renderer + ?Sized>(
    renderer: &mut R,
    center: Vec2,
    radius: f32,
    color: Color,
    is_active: bool,
    alpha: f32,
) {
    let effective_alpha = color.a * alpha;
    if effective_alpha < 0.01 {
        return;
    }

    // Dimensions relative to radius
    let head_radius = radius * 0.42;
    let body_width = radius * 0.7;
    let body_height = radius * 0.65;

    // Positions
    let head_center = Vec2::new(center.x, center.y - radius * 0.28);
    let body_center = Vec2::new(center.x, center.y + radius * 0.32);

    // Draw outer glow for active users
    if is_active {
        for i in 0..4 {
            let glow_radius = radius * (1.4 + i as f32 * 0.15);
            let glow_alpha = effective_alpha * 0.12 * (1.0 - i as f32 * 0.2);
            let glow_color = color.with_alpha(glow_alpha);
            renderer.draw_disc(center, glow_radius, glow_color);
        }
    }

    // Draw shadow/base layer (slightly larger, darker)
    let shadow_color = Color::new(
        color.r * 0.2,
        color.g * 0.2,
        color.b * 0.2,
        effective_alpha * 0.6,
    );
    renderer.draw_disc(center, radius * 1.05, shadow_color);

    // Draw body (rounded rectangle approximated with overlapping shapes)
    let body_color = Color::new(
        color.r * 0.85,
        color.g * 0.85,
        color.b * 0.85,
        effective_alpha,
    );

    // Body: stack of discs forming a pill shape
    let body_top = body_center.y - body_height * 0.4;
    let body_bottom = body_center.y + body_height * 0.4;
    let steps = 6;
    for i in 0..=steps {
        let t = i as f32 / steps as f32;
        let y = body_top + t * (body_bottom - body_top);
        // Taper the body slightly at top and bottom
        let taper = 1.0 - (t - 0.5).abs() * 0.3;
        let w = body_width * taper * 0.5;
        renderer.draw_disc(Vec2::new(center.x, y), w, body_color);
    }

    // Draw head
    let head_color = color.with_alpha(effective_alpha);
    renderer.draw_disc(head_center, head_radius, head_color);

    // Head highlight (subtle 3D effect)
    let highlight_offset = Vec2::new(-head_radius * 0.25, -head_radius * 0.25);
    let highlight_color = Color::new(1.0, 1.0, 1.0, effective_alpha * 0.25);
    renderer.draw_disc(
        head_center + highlight_offset,
        head_radius * 0.35,
        highlight_color,
    );

    // Active indicator: pulsing ring
    if is_active {
        let ring_color = Color::new(1.0, 1.0, 1.0, effective_alpha * 0.4);
        renderer.draw_circle(center, radius * 1.15, 1.5, ring_color);
    }
}

// ============================================================================
// Enhanced Beam Drawing
// ============================================================================

/// Draws an action beam with glow effect.
///
/// Creates a visually striking beam from user to file with:
/// - Multiple glow layers for soft edges
/// - Animated head with trail effect
///
/// # Arguments
///
/// * `renderer` - The renderer to draw with
/// * `start` - Starting position (user)
/// * `end` - Ending position (file)
/// * `progress` - Animation progress (0.0 - 1.0)
/// * `color` - Beam color
/// * `zoom` - Camera zoom level (affects line widths)
pub fn draw_action_beam<R: Renderer + ?Sized>(
    renderer: &mut R,
    start: Vec2,
    end: Vec2,
    progress: f32,
    color: Color,
    zoom: f32,
) {
    let beam_end = start.lerp(end, progress);

    // Draw glow layers (wider, more transparent)
    for i in 0..BEAM_GLOW_LAYERS {
        let layer = i as f32;
        let width = (2.0 + layer * 2.0) * zoom.max(0.5);
        let alpha = color.a * BEAM_GLOW_INTENSITY * (1.0 - layer * 0.25);
        let glow_color = color.with_alpha(alpha);
        renderer.draw_line(start, beam_end, width, glow_color);
    }

    // Draw core beam (brightest)
    let core_color = Color::new(
        (color.r + 0.3).min(1.0),
        (color.g + 0.3).min(1.0),
        (color.b + 0.3).min(1.0),
        color.a,
    );
    renderer.draw_line(start, beam_end, 1.5 * zoom.max(0.5), core_color);

    // Draw beam head with glow
    let head_radius = (4.0 * zoom).max(2.5);

    // Head glow
    for i in 0..2 {
        let glow_r = head_radius * (1.5 + i as f32 * 0.5);
        let glow_a = color.a * 0.3 * (1.0 - i as f32 * 0.3);
        renderer.draw_disc(beam_end, glow_r, color.with_alpha(glow_a));
    }

    // Head core (bright center)
    renderer.draw_disc(beam_end, head_radius, core_color);

    // Tiny bright center for extra pop
    let center_color = Color::new(1.0, 1.0, 1.0, color.a * 0.8);
    renderer.draw_disc(beam_end, head_radius * 0.4, center_color);
}

// ============================================================================
// Enhanced Branch Drawing
// ============================================================================

/// Draws a curved branch line with gradient effect.
///
/// # Arguments
///
/// * `renderer` - The renderer to draw with
/// * `start` - Starting position (parent node)
/// * `end` - Ending position (child node)
/// * `width` - Line width
/// * `color` - Branch color
/// * `use_curve` - Whether to use curved path or straight line
pub fn draw_curved_branch<R: Renderer + ?Sized>(
    renderer: &mut R,
    start: Vec2,
    end: Vec2,
    width: f32,
    color: Color,
    use_curve: bool,
) {
    if color.a < 0.01 {
        return;
    }

    if use_curve {
        // Generate smooth curve points
        let curve_points = create_branch_curve(start, end, BRANCH_CURVE_TENSION);

        // Draw the spline with gradient (brighter at end/file)
        renderer.draw_spline(&curve_points, width, color);

        // Add subtle glow along the curve
        let glow_color = color.with_alpha(color.a * 0.15);
        renderer.draw_spline(&curve_points, width * 2.5, glow_color);
    } else {
        // Fallback to straight line
        renderer.draw_line(start, end, width, color);
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

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
        // Should have more points than input
        assert!(result.len() > 3);
        // First point should match input
        assert_eq!(result[0], points[0]);
        // Last point should match input
        assert_eq!(*result.last().unwrap(), *points.last().unwrap());
    }

    #[test]
    fn test_catmull_rom_interpolate_endpoints() {
        let p0 = Vec2::new(0.0, 0.0);
        let p1 = Vec2::new(1.0, 1.0);
        let p2 = Vec2::new(2.0, 0.0);
        let p3 = Vec2::new(3.0, 1.0);

        // At t=0, should be at p1
        let result = catmull_rom_interpolate(p0, p1, p2, p3, 0.0);
        assert!((result.x - p1.x).abs() < 0.001);
        assert!((result.y - p1.y).abs() < 0.001);

        // At t=1, should be at p2
        let result = catmull_rom_interpolate(p0, p1, p2, p3, 1.0);
        assert!((result.x - p2.x).abs() < 0.001);
        assert!((result.y - p2.y).abs() < 0.001);
    }

    #[test]
    fn test_create_branch_curve_short_distance() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(0.5, 0.5);
        let result = create_branch_curve(start, end, 0.4);
        // Short distances should return simple 2-point line
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_create_branch_curve_normal_distance() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let result = create_branch_curve(start, end, 0.4);
        // Should create multiple interpolated points
        assert!(result.len() > 2);
        // First point should be start
        assert_eq!(result[0], start);
        // Last point should be end
        assert_eq!(*result.last().unwrap(), end);
    }

    #[test]
    fn test_branch_curve_tension_zero() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(50.0, 50.0);
        let result = create_branch_curve(start, end, 0.0);
        // With zero tension, curve points should still be generated
        assert!(result.len() >= 2);
        assert_eq!(result[0], start);
        assert_eq!(*result.last().unwrap(), end);
    }

    #[test]
    fn test_constants_valid() {
        // Use const assertions for compile-time validation
        const _: () = assert!(SPLINE_SEGMENTS > 0);
        const _: () = assert!(BEAM_GLOW_LAYERS > 0);
        // Runtime checks for float comparisons (const assert doesn't support floats well)
        let _ = BRANCH_CURVE_TENSION; // Ensure constant is used
        let _ = BEAM_GLOW_INTENSITY; // Ensure constant is used
    }

    // ========================================================================
    // MockRenderer for testing draw functions
    // ========================================================================

    use rource_math::Bounds;
    use std::cell::RefCell;

    /// Tracks all draw calls for verification in tests.
    #[derive(Debug, Clone, Default)]
    struct DrawCalls {
        discs: Vec<(Vec2, f32, Color)>,
        circles: Vec<(Vec2, f32, f32, Color)>,
        lines: Vec<(Vec2, Vec2, f32, Color)>,
        splines: Vec<(Vec<Vec2>, f32, Color)>,
    }

    /// A mock renderer that tracks draw calls without actual rendering.
    struct MockRenderer {
        calls: RefCell<DrawCalls>,
    }

    impl MockRenderer {
        fn new() -> Self {
            Self {
                calls: RefCell::new(DrawCalls::default()),
            }
        }

        fn calls(&self) -> DrawCalls {
            self.calls.borrow().clone()
        }
    }

    impl crate::Renderer for MockRenderer {
        fn begin_frame(&mut self) {}
        fn end_frame(&mut self) {}
        fn clear(&mut self, _color: Color) {}

        fn draw_circle(&mut self, center: Vec2, radius: f32, width: f32, color: Color) {
            self.calls
                .borrow_mut()
                .circles
                .push((center, radius, width, color));
        }

        fn draw_disc(&mut self, center: Vec2, radius: f32, color: Color) {
            self.calls.borrow_mut().discs.push((center, radius, color));
        }

        fn draw_line(&mut self, start: Vec2, end: Vec2, width: f32, color: Color) {
            self.calls
                .borrow_mut()
                .lines
                .push((start, end, width, color));
        }

        fn draw_spline(&mut self, points: &[Vec2], width: f32, color: Color) {
            self.calls
                .borrow_mut()
                .splines
                .push((points.to_vec(), width, color));
        }

        fn draw_quad(
            &mut self,
            _bounds: Bounds,
            _texture: Option<crate::TextureId>,
            _color: Color,
        ) {
        }
        fn draw_text(
            &mut self,
            _text: &str,
            _position: Vec2,
            _font: crate::FontId,
            _size: f32,
            _color: Color,
        ) {
        }
        fn load_font(&mut self, _data: &[u8]) -> Option<crate::FontId> {
            None
        }
        fn set_transform(&mut self, _transform: rource_math::Mat4) {}
        fn transform(&self) -> rource_math::Mat4 {
            rource_math::Mat4::IDENTITY
        }
        fn push_clip(&mut self, _bounds: Bounds) {}
        fn pop_clip(&mut self) {}
        fn resize(&mut self, _width: u32, _height: u32) {}
        fn width(&self) -> u32 {
            800
        }
        fn height(&self) -> u32 {
            600
        }
        fn load_texture(&mut self, _width: u32, _height: u32, _data: &[u8]) -> crate::TextureId {
            crate::TextureId::new(0)
        }
        fn unload_texture(&mut self, _texture: crate::TextureId) {}
    }

    // ========================================================================
    // Drawing function tests
    // ========================================================================

    #[test]
    fn test_draw_avatar_shape_active() {
        let mut renderer = MockRenderer::new();
        let center = Vec2::new(100.0, 100.0);
        let radius = 20.0;
        let color = Color::new(0.5, 0.5, 1.0, 1.0);

        draw_avatar_shape(&mut renderer, center, radius, color, true, 1.0);

        let calls = renderer.calls();
        // Active avatar should draw glow layers, shadow, body discs, head, highlight, and ring
        assert!(!calls.discs.is_empty(), "Should draw discs for avatar");
        assert!(!calls.circles.is_empty(), "Active avatar should draw ring");
    }

    #[test]
    fn test_draw_avatar_shape_inactive() {
        let mut renderer = MockRenderer::new();
        let center = Vec2::new(100.0, 100.0);
        let radius = 20.0;
        let color = Color::new(0.5, 0.5, 1.0, 1.0);

        draw_avatar_shape(&mut renderer, center, radius, color, false, 1.0);

        let calls = renderer.calls();
        // Inactive avatar should draw body and head but no active ring/glow
        assert!(!calls.discs.is_empty(), "Should draw discs for avatar");
        assert!(
            calls.circles.is_empty(),
            "Inactive avatar should not draw ring"
        );
    }

    #[test]
    fn test_draw_avatar_shape_invisible() {
        let mut renderer = MockRenderer::new();
        let center = Vec2::new(100.0, 100.0);
        let radius = 20.0;
        let color = Color::new(0.5, 0.5, 1.0, 1.0);

        // Alpha below threshold should skip drawing
        draw_avatar_shape(&mut renderer, center, radius, color, true, 0.005);

        let calls = renderer.calls();
        assert!(calls.discs.is_empty(), "Very low alpha should skip drawing");
    }

    #[test]
    fn test_draw_action_beam() {
        let mut renderer = MockRenderer::new();
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let color = Color::new(1.0, 0.5, 0.0, 1.0);

        draw_action_beam(&mut renderer, start, end, 0.5, color, 1.0);

        let calls = renderer.calls();
        // Should draw glow layers + core line
        assert!(
            calls.lines.len() > BEAM_GLOW_LAYERS,
            "Should draw glow layers and core"
        );
        // Should draw beam head (discs for glow and core)
        assert!(
            calls.discs.len() >= 3,
            "Should draw beam head with glow and core"
        );
    }

    #[test]
    fn test_draw_action_beam_progress_zero() {
        let mut renderer = MockRenderer::new();
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let color = Color::new(1.0, 0.5, 0.0, 1.0);

        draw_action_beam(&mut renderer, start, end, 0.0, color, 1.0);

        let calls = renderer.calls();
        // At progress=0, lines should be from start to start (zero length)
        for (line_start, line_end, _, _) in &calls.lines {
            assert_eq!(*line_start, start);
            assert_eq!(*line_end, start);
        }
    }

    #[test]
    fn test_draw_curved_branch_with_curve() {
        let mut renderer = MockRenderer::new();
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let color = Color::new(0.5, 0.5, 0.5, 1.0);

        draw_curved_branch(&mut renderer, start, end, 2.0, color, true);

        let calls = renderer.calls();
        // Should draw spline (main curve and glow)
        assert_eq!(calls.splines.len(), 2, "Should draw main spline and glow");
        // Check that the wider glow is drawn
        let widths: Vec<f32> = calls.splines.iter().map(|(_, w, _)| *w).collect();
        assert!(
            widths.iter().any(|&w| w > 2.0),
            "Should have wider glow spline"
        );
    }

    #[test]
    fn test_draw_curved_branch_straight() {
        let mut renderer = MockRenderer::new();
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let color = Color::new(0.5, 0.5, 0.5, 1.0);

        draw_curved_branch(&mut renderer, start, end, 2.0, color, false);

        let calls = renderer.calls();
        // Should draw a single line, not splines
        assert!(
            calls.splines.is_empty(),
            "Straight branch should not use splines"
        );
        assert_eq!(calls.lines.len(), 1, "Should draw one straight line");
    }

    #[test]
    fn test_draw_curved_branch_invisible() {
        let mut renderer = MockRenderer::new();
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let color = Color::new(0.5, 0.5, 0.5, 0.005);

        draw_curved_branch(&mut renderer, start, end, 2.0, color, true);

        let calls = renderer.calls();
        // Very low alpha should skip drawing
        assert!(calls.splines.is_empty(), "Invisible branch should not draw");
        assert!(calls.lines.is_empty(), "Invisible branch should not draw");
    }
}
