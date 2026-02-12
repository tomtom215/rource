// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

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

// Precomputed multipliers for avatar glow (avoids i as f32 in loop)
// glow_radius = radius * (1.4 + i * 0.15), glow_alpha = 0.12 * (1.0 - i * 0.2)
const AVATAR_GLOW_RADIUS_MULTS: [f32; 4] = [1.4, 1.55, 1.70, 1.85];
const AVATAR_GLOW_ALPHA_MULTS: [f32; 4] = [0.12, 0.096, 0.072, 0.048];

// Precomputed t values and taper for avatar body (avoids division in loop)
// t = i / 6, taper = 1.0 - |t - 0.5| * 0.3
const AVATAR_BODY_T: [f32; 7] = [0.0, 0.16667, 0.33333, 0.5, 0.66667, 0.83333, 1.0];
const AVATAR_BODY_TAPER: [f32; 7] = [0.85, 0.90, 0.95, 1.0, 0.95, 0.90, 0.85];

// Precomputed beam glow values (avoids i as f32 in loop)
// width_base = 2 + i * 2, alpha_mult = BEAM_GLOW_INTENSITY * (1.0 - i * 0.25)
const BEAM_GLOW_WIDTH_BASE: [f32; 3] = [2.0, 4.0, 6.0];
const BEAM_GLOW_ALPHA_MULT: [f32; 3] = [0.4, 0.3, 0.2];

// Precomputed beam head glow values
// radius_mult = 1.5 + i * 0.5, alpha_mult = 0.3 * (1.0 - i * 0.3)
const BEAM_HEAD_GLOW_RADIUS: [f32; 2] = [1.5, 2.0];
const BEAM_HEAD_GLOW_ALPHA: [f32; 2] = [0.3, 0.21];

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
    // Precompute reciprocal to avoid division in inner loop (perf: ~1000 divisions/frame saved)
    let inv_segments = 1.0 / segments_per_span as f32;
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
            let t = j as f32 * inv_segments;
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
    // Optimization: The perpendicular vector (-dir.y, dir.x) has the same magnitude as dir.
    // Since we multiply by length afterward, normalization and multiplication cancel out:
    // (perp / length) * length = perp. This saves one sqrt() call.
    let perp = Vec2::new(-dir.y, dir.x);
    let offset = perp * tension * 0.15;

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

    // Draw outer glow for active users (uses precomputed multipliers)
    if is_active {
        for i in 0..4 {
            let glow_radius = radius * AVATAR_GLOW_RADIUS_MULTS[i];
            let glow_alpha = effective_alpha * AVATAR_GLOW_ALPHA_MULTS[i];
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

    // Body: stack of discs forming a pill shape (uses precomputed t and taper)
    let body_top = body_center.y - body_height * 0.4;
    let body_bottom = body_center.y + body_height * 0.4;
    let body_range = body_bottom - body_top;
    for i in 0..7 {
        let y = body_top + AVATAR_BODY_T[i] * body_range;
        let w = body_width * AVATAR_BODY_TAPER[i] * 0.5;
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

    // Draw glow layers (uses precomputed width and alpha multipliers)
    let zoom_factor = zoom.max(0.5);
    for i in 0..BEAM_GLOW_LAYERS {
        let width = BEAM_GLOW_WIDTH_BASE[i] * zoom_factor;
        let alpha = color.a * BEAM_GLOW_ALPHA_MULT[i];
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

    // Head glow (uses precomputed radius and alpha multipliers)
    for i in 0..2 {
        let glow_r = head_radius * BEAM_HEAD_GLOW_RADIUS[i];
        let glow_a = color.a * BEAM_HEAD_GLOW_ALPHA[i];
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
// Phase 87: Zero-Allocation Branch Drawing
// ============================================================================

/// Screen-space distance threshold (pixels²) below which straight lines are used.
///
/// When the squared distance between branch endpoints is less than this,
/// a straight line is visually indistinguishable from a curve. Avoids
/// Catmull-Rom computation for short branches.
///
/// 50² = 2500 pixels² ≈ branches shorter than ~50px on screen.
const BRANCH_CURVE_DIST_SQ_THRESHOLD: f32 = 2500.0;

/// Generates Catmull-Rom spline points into a reusable buffer.
///
/// Zero-allocation version of [`catmull_rom_spline`]. The buffer is cleared
/// and repopulated each call, eliminating per-call heap allocation.
///
/// # Phase 87
///
/// This function is called 200+ times per frame (once per visible file branch).
/// The allocating version created ~200 `Vec<Vec2>` allocations per frame.
/// This version reuses a single buffer across all calls.
pub fn catmull_rom_spline_into(points: &[Vec2], segments_per_span: usize, output: &mut Vec<Vec2>) {
    output.clear();

    if points.len() < 2 {
        output.extend_from_slice(points);
        return;
    }

    if points.len() == 2 {
        output.extend_from_slice(points);
        return;
    }

    output.reserve(points.len() * segments_per_span + 1);

    let inv_segments = 1.0 / segments_per_span as f32;
    for i in 0..points.len() - 1 {
        let p0 = if i == 0 { points[0] } else { points[i - 1] };
        let p1 = points[i];
        let p2 = points[i + 1];
        let p3 = if i + 2 >= points.len() {
            points[points.len() - 1]
        } else {
            points[i + 2]
        };

        for j in 0..segments_per_span {
            let t = j as f32 * inv_segments;
            output.push(catmull_rom_interpolate(p0, p1, p2, p3, t));
        }
    }

    if let Some(&last) = points.last() {
        output.push(last);
    }
}

/// Creates a curved branch path into a reusable buffer.
///
/// Zero-allocation version of [`create_branch_curve`].
///
/// # Phase 87
///
/// Eliminates ~200 `Vec<Vec2>` heap allocations per frame by reusing
/// a caller-owned buffer.
pub fn create_branch_curve_into(start: Vec2, end: Vec2, tension: f32, output: &mut Vec<Vec2>) {
    let dir = end - start;
    let length_sq = dir.x * dir.x + dir.y * dir.y;

    if length_sq < 1.0 {
        output.clear();
        output.push(start);
        output.push(end);
        return;
    }

    let mid = start.lerp(end, 0.5);
    let perp = Vec2::new(-dir.y, dir.x);
    let offset = perp * tension * 0.15;

    let ctrl1 = start.lerp(mid, 0.33) + offset * 0.5;
    let ctrl2 = start.lerp(mid, 0.66) + offset;
    let ctrl3 = mid.lerp(end, 0.33) + offset * 0.5;
    let ctrl4 = mid.lerp(end, 0.66);

    let control_points = [start, ctrl1, ctrl2, ctrl3, ctrl4, end];
    catmull_rom_spline_into(&control_points, SPLINE_SEGMENTS / 2, output);
}

/// Draws a curved branch using a reusable buffer (zero allocation per call).
///
/// # Phase 87: Zero-Allocation Branch Drawing
///
/// This replaces `draw_curved_branch` in hot loops where branches are drawn
/// for hundreds of files per frame. Key differences from `draw_curved_branch`:
///
/// - Uses caller-owned `curve_buf` to avoid heap allocation per call
/// - LOD simplification: uses straight lines when endpoints are close on screen
///   (< ~50 pixels apart), avoiding Catmull-Rom computation entirely
/// - No branch glow pass (the 0.15 alpha glow is imperceptible for thin file
///   branches and doubled the number of `draw_spline` calls)
///
/// # Arguments
///
/// * `curve_buf` - Reusable buffer for curve points (cleared and repopulated)
/// * Other arguments same as `draw_curved_branch`
#[inline]
pub fn draw_curved_branch_buffered<R: Renderer + ?Sized>(
    renderer: &mut R,
    start: Vec2,
    end: Vec2,
    width: f32,
    color: Color,
    use_curve: bool,
    curve_buf: &mut Vec<Vec2>,
) {
    if color.a < 0.01 {
        return;
    }

    if !use_curve {
        renderer.draw_line(start, end, width, color);
        return;
    }

    // LOD: Use straight line when branch is short on screen.
    // Squared distance avoids sqrt() — at < ~50px, curves are indistinguishable.
    let dx = end.x - start.x;
    let dy = end.y - start.y;
    let dist_sq = dx * dx + dy * dy;

    if dist_sq < BRANCH_CURVE_DIST_SQ_THRESHOLD {
        renderer.draw_line(start, end, width, color);
        return;
    }

    create_branch_curve_into(start, end, BRANCH_CURVE_TENSION, curve_buf);
    renderer.draw_spline(curve_buf, width, color);
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

    // ========================================================================
    // Phase 87: catmull_rom_spline_into tests (zero-allocation parity)
    // ========================================================================

    #[test]
    fn test_catmull_rom_spline_into_empty() {
        let mut buf = Vec::new();
        catmull_rom_spline_into(&[], 10, &mut buf);
        assert!(buf.is_empty());
    }

    #[test]
    fn test_catmull_rom_spline_into_single_point() {
        let mut buf = Vec::new();
        let points = [Vec2::new(5.0, 5.0)];
        catmull_rom_spline_into(&points, 10, &mut buf);
        assert_eq!(buf.len(), 1);
        assert_eq!(buf[0], Vec2::new(5.0, 5.0));
    }

    #[test]
    fn test_catmull_rom_spline_into_two_points() {
        let mut buf = Vec::new();
        let points = [Vec2::new(0.0, 0.0), Vec2::new(10.0, 10.0)];
        catmull_rom_spline_into(&points, 10, &mut buf);
        assert_eq!(buf.len(), 2);
        assert_eq!(buf[0], Vec2::new(0.0, 0.0));
        assert_eq!(buf[1], Vec2::new(10.0, 10.0));
    }

    #[test]
    fn test_catmull_rom_spline_into_multiple_points() {
        let mut buf = Vec::new();
        let points = [
            Vec2::new(0.0, 0.0),
            Vec2::new(10.0, 5.0),
            Vec2::new(20.0, 0.0),
        ];
        catmull_rom_spline_into(&points, 5, &mut buf);
        // Should have more points than input (5 segments × 2 spans + 1 endpoint)
        assert!(buf.len() > 3, "Expected > 3 points, got {}", buf.len());
        // First point should match input
        assert_eq!(buf[0], points[0]);
        // Last point should match input
        assert_eq!(*buf.last().unwrap(), *points.last().unwrap());
    }

    #[test]
    fn test_catmull_rom_spline_into_parity_with_allocating() {
        // Verify zero-alloc version produces identical output to allocating version
        let points = vec![
            Vec2::new(0.0, 0.0),
            Vec2::new(10.0, 5.0),
            Vec2::new(20.0, 0.0),
            Vec2::new(30.0, 10.0),
        ];
        let allocating = catmull_rom_spline(&points, 4);
        let mut buf = Vec::new();
        catmull_rom_spline_into(&points, 4, &mut buf);
        assert_eq!(buf.len(), allocating.len(), "Length mismatch");
        for (i, (a, b)) in allocating.iter().zip(buf.iter()).enumerate() {
            assert!(
                (a.x - b.x).abs() < 1e-6 && (a.y - b.y).abs() < 1e-6,
                "Point {i} differs: allocating={a:?}, into={b:?}"
            );
        }
    }

    #[test]
    fn test_catmull_rom_spline_into_buffer_reuse() {
        // Verify buffer is properly cleared and reused across calls
        let mut buf = Vec::new();
        let points_a = [Vec2::new(0.0, 0.0), Vec2::new(10.0, 10.0)];
        catmull_rom_spline_into(&points_a, 4, &mut buf);
        assert_eq!(buf.len(), 2);

        let points_b = [
            Vec2::new(0.0, 0.0),
            Vec2::new(5.0, 10.0),
            Vec2::new(10.0, 0.0),
        ];
        catmull_rom_spline_into(&points_b, 4, &mut buf);
        assert!(buf.len() > 2, "Buffer should be repopulated, not appended");
        assert_eq!(buf[0], points_b[0]);
        assert_eq!(*buf.last().unwrap(), *points_b.last().unwrap());
    }

    #[test]
    fn test_catmull_rom_spline_into_interpolation_correctness() {
        // Verify intermediate points are actually interpolated (not just endpoints)
        let mut buf = Vec::new();
        let points = [
            Vec2::new(0.0, 0.0),
            Vec2::new(10.0, 10.0),
            Vec2::new(20.0, 0.0),
        ];
        catmull_rom_spline_into(&points, 4, &mut buf);
        // Check that intermediate points exist between endpoints
        let has_intermediate = buf.iter().any(|p| p.x > 0.5 && p.x < 19.5);
        assert!(
            has_intermediate,
            "Should have interpolated intermediate points"
        );
        // Verify monotonic x progression (for this simple case)
        for w in buf.windows(2) {
            assert!(
                w[1].x >= w[0].x - 0.01,
                "X should be roughly monotonic: {} -> {}",
                w[0].x,
                w[1].x
            );
        }
    }

    // ========================================================================
    // Phase 87: create_branch_curve_into tests
    // ========================================================================

    #[test]
    fn test_create_branch_curve_into_short_distance() {
        let mut buf = Vec::new();
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(0.5, 0.5);
        create_branch_curve_into(start, end, 0.4, &mut buf);
        // Short distances should return simple 2-point line
        assert_eq!(buf.len(), 2);
        assert_eq!(buf[0], start);
        assert_eq!(buf[1], end);
    }

    #[test]
    fn test_create_branch_curve_into_normal_distance() {
        let mut buf = Vec::new();
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        create_branch_curve_into(start, end, 0.4, &mut buf);
        // Should create multiple interpolated points
        assert!(buf.len() > 2, "Expected > 2 points, got {}", buf.len());
        // First point should be start
        assert_eq!(buf[0], start);
        // Last point should be end
        assert_eq!(*buf.last().unwrap(), end);
    }

    #[test]
    fn test_create_branch_curve_into_parity_with_allocating() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let allocating = create_branch_curve(start, end, 0.4);
        let mut buf = Vec::new();
        create_branch_curve_into(start, end, 0.4, &mut buf);
        assert_eq!(buf.len(), allocating.len(), "Length mismatch");
        for (i, (a, b)) in allocating.iter().zip(buf.iter()).enumerate() {
            assert!(
                (a.x - b.x).abs() < 1e-6 && (a.y - b.y).abs() < 1e-6,
                "Point {i} differs: allocating={a:?}, into={b:?}"
            );
        }
    }

    #[test]
    fn test_create_branch_curve_into_tension_affects_shape() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let mut buf_low = Vec::new();
        let mut buf_high = Vec::new();
        create_branch_curve_into(start, end, 0.1, &mut buf_low);
        create_branch_curve_into(start, end, 1.0, &mut buf_high);
        // Same number of points but different intermediate positions
        assert_eq!(buf_low.len(), buf_high.len());
        // At least one intermediate point should differ due to tension
        let differs = buf_low
            .iter()
            .zip(buf_high.iter())
            .any(|(a, b)| (a.x - b.x).abs() > 0.01 || (a.y - b.y).abs() > 0.01);
        assert!(
            differs,
            "Different tensions should produce different curves"
        );
    }

    #[test]
    fn test_create_branch_curve_into_perpendicular_offset() {
        // Verify the curve has a perpendicular offset (not just a straight line)
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 0.0); // Horizontal line
        let mut buf = Vec::new();
        create_branch_curve_into(start, end, 0.4, &mut buf);
        // With horizontal start→end and non-zero tension, some points should
        // have non-zero y (perpendicular offset)
        let has_y_offset = buf.iter().any(|p| p.y.abs() > 0.01);
        assert!(
            has_y_offset,
            "Curve with tension should have perpendicular offset"
        );
    }

    #[test]
    fn test_create_branch_curve_into_buffer_reuse() {
        let mut buf = vec![Vec2::new(999.0, 999.0); 50]; // Pre-fill with garbage
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(0.5, 0.5); // Short distance → 2 points
        create_branch_curve_into(start, end, 0.4, &mut buf);
        assert_eq!(buf.len(), 2, "Buffer should be cleared and repopulated");
        assert_eq!(buf[0], start);
        assert_eq!(buf[1], end);
    }

    // ========================================================================
    // Phase 87: draw_curved_branch_buffered tests
    // ========================================================================

    #[test]
    fn test_draw_curved_branch_buffered_with_curve() {
        let mut renderer = MockRenderer::new();
        let mut buf = Vec::new();
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0); // Far enough for curve (dist_sq = 20000 > 2500)
        let color = Color::new(0.5, 0.5, 0.5, 1.0);

        draw_curved_branch_buffered(&mut renderer, start, end, 2.0, color, true, &mut buf);

        let calls = renderer.calls();
        // Should draw a single spline (no glow unlike draw_curved_branch)
        assert_eq!(calls.splines.len(), 1, "Should draw exactly one spline");
        assert!(
            calls.lines.is_empty(),
            "Should not draw lines when using curve"
        );
    }

    #[test]
    fn test_draw_curved_branch_buffered_straight_line() {
        let mut renderer = MockRenderer::new();
        let mut buf = Vec::new();
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let color = Color::new(0.5, 0.5, 0.5, 1.0);

        draw_curved_branch_buffered(&mut renderer, start, end, 2.0, color, false, &mut buf);

        let calls = renderer.calls();
        assert!(
            calls.splines.is_empty(),
            "Straight mode should not draw splines"
        );
        assert_eq!(calls.lines.len(), 1, "Should draw one straight line");
        // Verify the line coordinates
        assert_eq!(calls.lines[0].0, start);
        assert_eq!(calls.lines[0].1, end);
    }

    #[test]
    fn test_draw_curved_branch_buffered_invisible() {
        let mut renderer = MockRenderer::new();
        let mut buf = Vec::new();
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let color = Color::new(0.5, 0.5, 0.5, 0.005); // Below 0.01 threshold

        draw_curved_branch_buffered(&mut renderer, start, end, 2.0, color, true, &mut buf);

        let calls = renderer.calls();
        assert!(
            calls.splines.is_empty(),
            "Invisible branch should not draw splines"
        );
        assert!(
            calls.lines.is_empty(),
            "Invisible branch should not draw lines"
        );
    }

    #[test]
    fn test_draw_curved_branch_buffered_lod_short_distance() {
        // When endpoints are close (< 50px), should use straight line even with use_curve=true
        let mut renderer = MockRenderer::new();
        let mut buf = Vec::new();
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(10.0, 10.0); // dist_sq = 200 < 2500 threshold
        let color = Color::new(0.5, 0.5, 0.5, 1.0);

        draw_curved_branch_buffered(&mut renderer, start, end, 2.0, color, true, &mut buf);

        let calls = renderer.calls();
        // LOD simplification: short branch → straight line
        assert!(
            calls.splines.is_empty(),
            "Short branch should use line, not spline"
        );
        assert_eq!(calls.lines.len(), 1, "Short branch should draw one line");
    }

    #[test]
    fn test_draw_curved_branch_buffered_lod_threshold_boundary() {
        // Test exactly at the threshold boundary (50px = dist_sq 2500)
        let mut renderer_below = MockRenderer::new();
        let mut renderer_above = MockRenderer::new();
        let mut buf = Vec::new();
        let color = Color::new(0.5, 0.5, 0.5, 1.0);

        // Just below threshold: 49px diagonal ≈ dist_sq = 49² + 0² = 2401 < 2500
        let start = Vec2::new(0.0, 0.0);
        let end_below = Vec2::new(49.0, 0.0);
        draw_curved_branch_buffered(
            &mut renderer_below,
            start,
            end_below,
            2.0,
            color,
            true,
            &mut buf,
        );

        // Just above threshold: 51px ≈ dist_sq = 51² = 2601 > 2500
        let end_above = Vec2::new(51.0, 0.0);
        draw_curved_branch_buffered(
            &mut renderer_above,
            start,
            end_above,
            2.0,
            color,
            true,
            &mut buf,
        );

        let calls_below = renderer_below.calls();
        let calls_above = renderer_above.calls();

        // Below threshold → line
        assert_eq!(
            calls_below.lines.len(),
            1,
            "Below threshold should draw line"
        );
        assert!(
            calls_below.splines.is_empty(),
            "Below threshold should not draw spline"
        );
        // Above threshold → spline
        assert_eq!(
            calls_above.splines.len(),
            1,
            "Above threshold should draw spline"
        );
        assert!(
            calls_above.lines.is_empty(),
            "Above threshold should not draw line"
        );
    }

    #[test]
    fn test_draw_curved_branch_buffered_no_glow() {
        // Verify the buffered version does NOT draw glow (unlike draw_curved_branch)
        let mut renderer_buffered = MockRenderer::new();
        let mut renderer_original = MockRenderer::new();
        let mut buf = Vec::new();
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let color = Color::new(0.5, 0.5, 0.5, 1.0);

        draw_curved_branch_buffered(
            &mut renderer_buffered,
            start,
            end,
            2.0,
            color,
            true,
            &mut buf,
        );
        draw_curved_branch(&mut renderer_original, start, end, 2.0, color, true);

        let buffered_calls = renderer_buffered.calls();
        let original_calls = renderer_original.calls();

        // Original draws 2 splines (main + glow), buffered draws 1 (main only)
        assert_eq!(
            buffered_calls.splines.len(),
            1,
            "Buffered should draw 1 spline (no glow)"
        );
        assert_eq!(
            original_calls.splines.len(),
            2,
            "Original should draw 2 splines (main + glow)"
        );
    }

    #[test]
    fn test_draw_curved_branch_buffered_buffer_reuse() {
        // Verify the buffer is properly reused across multiple calls
        let mut renderer = MockRenderer::new();
        let mut buf = Vec::new();
        let color = Color::new(0.5, 0.5, 0.5, 1.0);

        // First call with long branch (uses spline)
        draw_curved_branch_buffered(
            &mut renderer,
            Vec2::new(0.0, 0.0),
            Vec2::new(100.0, 100.0),
            2.0,
            color,
            true,
            &mut buf,
        );
        let first_len = buf.len();
        assert!(
            first_len > 2,
            "Long branch should populate buffer with curve points"
        );

        // Second call with different endpoints
        draw_curved_branch_buffered(
            &mut renderer,
            Vec2::new(50.0, 50.0),
            Vec2::new(200.0, 200.0),
            2.0,
            color,
            true,
            &mut buf,
        );
        // Buffer should have been cleared and repopulated, not appended
        assert_eq!(
            buf.len(),
            first_len,
            "Buffer should be repopulated (same number of curve points)"
        );
    }

    #[test]
    fn test_draw_curved_branch_buffered_dist_sq_computation() {
        // Verify the distance computation is correct (dx² + dy²)
        let mut renderer = MockRenderer::new();
        let mut buf = Vec::new();
        let color = Color::new(0.5, 0.5, 0.5, 1.0);

        // Distance: sqrt(30² + 40²) = 50px, dist_sq = 2500 = threshold
        // At threshold, should use line (< not <=)
        let start = Vec2::new(0.0, 0.0);
        // Use slightly less than threshold: 30² + 39² = 900 + 1521 = 2421 < 2500
        let end = Vec2::new(30.0, 39.0);
        draw_curved_branch_buffered(&mut renderer, start, end, 2.0, color, true, &mut buf);

        let calls = renderer.calls();
        assert_eq!(calls.lines.len(), 1, "dist_sq=2421 < 2500 should use line");
        assert!(calls.splines.is_empty());
    }
}
