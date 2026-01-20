//! Enhanced visual rendering helpers for Rource WASM.
//!
//! This module contains spline interpolation, avatar drawing, beam effects,
//! and curved branch rendering. These functions are used by the main render
//! loop to create visually appealing visualizations.
//!
//! Note: This code is separate from the CLI rendering code in `rource-cli/src/rendering.rs`.
//! When making visual changes, both files should be updated to maintain visual parity.

use rource_math::{Color, Vec2};
use rource_render::Renderer;

/// Number of segments for Catmull-Rom spline interpolation.
pub const SPLINE_SEGMENTS: usize = 12;

/// Curve tension for branch splines (0.0 = straight, 0.5 = natural curves).
pub const BRANCH_CURVE_TENSION: f32 = 0.4;

/// Glow intensity multiplier for action beams.
pub const BEAM_GLOW_INTENSITY: f32 = 0.4;

/// Number of glow layers for beams.
pub const BEAM_GLOW_LAYERS: usize = 3;

/// Generates Catmull-Rom spline points between control points.
///
/// # Arguments
///
/// * `points` - The control points for the spline
/// * `segments_per_span` - Number of interpolated segments between each pair of control points
///
/// # Returns
///
/// A vector of interpolated points along the spline curve.
pub fn catmull_rom_spline(points: &[Vec2], segments_per_span: usize) -> Vec<Vec2> {
    if points.len() < 2 {
        return points.to_vec();
    }

    if points.len() == 2 {
        return points.to_vec();
    }

    let mut result = Vec::with_capacity(points.len() * segments_per_span);

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
            let t = j as f32 / segments_per_span as f32;
            let point = catmull_rom_interpolate(p0, p1, p2, p3, t);
            result.push(point);
        }
    }

    result.push(*points.last().unwrap());
    result
}

/// Performs Catmull-Rom interpolation between p1 and p2.
///
/// # Arguments
///
/// * `p0` - Control point before p1
/// * `p1` - Start of interpolated segment
/// * `p2` - End of interpolated segment
/// * `p3` - Control point after p2
/// * `t` - Interpolation parameter (0.0 = p1, 1.0 = p2)
#[inline]
pub fn catmull_rom_interpolate(p0: Vec2, p1: Vec2, p2: Vec2, p3: Vec2, t: f32) -> Vec2 {
    let t2 = t * t;
    let t3 = t2 * t;

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
/// # Arguments
///
/// * `start` - Starting point of the curve
/// * `end` - Ending point of the curve
/// * `tension` - Curve tension (0.0 = straight, higher = more curved)
///
/// # Returns
///
/// A vector of points along the curved path.
pub fn create_branch_curve(start: Vec2, end: Vec2, tension: f32) -> Vec<Vec2> {
    let mid = start.lerp(end, 0.5);
    let dir = end - start;
    let length = dir.length();

    if length < 1.0 {
        return vec![start, end];
    }

    let perp = Vec2::new(-dir.y, dir.x).normalized();
    let offset = perp * length * tension * 0.15;

    let ctrl1 = start.lerp(mid, 0.33) + offset * 0.5;
    let ctrl2 = start.lerp(mid, 0.66) + offset;
    let ctrl3 = mid.lerp(end, 0.33) + offset * 0.5;
    let ctrl4 = mid.lerp(end, 0.66);

    catmull_rom_spline(
        &[start, ctrl1, ctrl2, ctrl3, ctrl4, end],
        SPLINE_SEGMENTS / 2,
    )
}

/// Draws a stylized avatar shape (modern person silhouette).
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

    let head_radius = radius * 0.42;
    let body_width = radius * 0.7;
    let body_height = radius * 0.65;

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

    // Draw shadow/base layer
    let shadow_color = Color::new(
        color.r * 0.2,
        color.g * 0.2,
        color.b * 0.2,
        effective_alpha * 0.6,
    );
    renderer.draw_disc(center, radius * 1.05, shadow_color);

    // Draw body (pill shape approximated with overlapping discs)
    let body_color = Color::new(
        color.r * 0.85,
        color.g * 0.85,
        color.b * 0.85,
        effective_alpha,
    );

    let body_top = body_center.y - body_height * 0.4;
    let body_bottom = body_center.y + body_height * 0.4;
    let steps = 6;
    for i in 0..=steps {
        let t = i as f32 / steps as f32;
        let y = body_top + t * (body_bottom - body_top);
        let taper = 1.0 - (t - 0.5).abs() * 0.3;
        let w = body_width * taper * 0.5;
        renderer.draw_disc(Vec2::new(center.x, y), w, body_color);
    }

    // Draw head
    let head_color = color.with_alpha(effective_alpha);
    renderer.draw_disc(head_center, head_radius, head_color);

    // Head highlight
    let highlight_offset = Vec2::new(-head_radius * 0.25, -head_radius * 0.25);
    let highlight_color = Color::new(1.0, 1.0, 1.0, effective_alpha * 0.25);
    renderer.draw_disc(
        head_center + highlight_offset,
        head_radius * 0.35,
        highlight_color,
    );

    // Active indicator ring
    if is_active {
        let ring_color = Color::new(1.0, 1.0, 1.0, effective_alpha * 0.4);
        renderer.draw_circle(center, radius * 1.15, 1.5, ring_color);
    }
}

/// Draws an action beam with glow effect.
///
/// # Arguments
///
/// * `renderer` - The renderer to draw with
/// * `start` - Starting position (user)
/// * `end` - Ending position (file)
/// * `progress` - Animation progress (0.0 - 1.0)
/// * `color` - Beam color
/// * `zoom` - Camera zoom level
pub fn draw_action_beam<R: Renderer + ?Sized>(
    renderer: &mut R,
    start: Vec2,
    end: Vec2,
    progress: f32,
    color: Color,
    zoom: f32,
) {
    let beam_end = start.lerp(end, progress);

    // Draw glow layers
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

    for i in 0..2 {
        let glow_r = head_radius * (1.5 + i as f32 * 0.5);
        let glow_a = color.a * 0.3 * (1.0 - i as f32 * 0.3);
        renderer.draw_disc(beam_end, glow_r, color.with_alpha(glow_a));
    }

    renderer.draw_disc(beam_end, head_radius, core_color);

    // Tiny bright center
    let center_color = Color::new(1.0, 1.0, 1.0, color.a * 0.8);
    renderer.draw_disc(beam_end, head_radius * 0.4, center_color);
}

/// Draws a curved branch line with gradient effect.
///
/// # Arguments
///
/// * `renderer` - The renderer to draw with
/// * `start` - Starting position
/// * `end` - Ending position
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
        let curve_points = create_branch_curve(start, end, BRANCH_CURVE_TENSION);
        renderer.draw_spline(&curve_points, width, color);

        // Subtle glow along the curve
        let glow_color = color.with_alpha(color.a * 0.15);
        renderer.draw_spline(&curve_points, width * 2.5, glow_color);
    } else {
        renderer.draw_line(start, end, width, color);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_catmull_rom_spline_empty() {
        let points: Vec<Vec2> = vec![];
        let result = catmull_rom_spline(&points, 10);
        assert!(result.is_empty());
    }

    #[test]
    fn test_catmull_rom_spline_single_point() {
        let points = vec![Vec2::new(1.0, 2.0)];
        let result = catmull_rom_spline(&points, 10);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], Vec2::new(1.0, 2.0));
    }

    #[test]
    fn test_catmull_rom_spline_two_points() {
        let points = vec![Vec2::new(0.0, 0.0), Vec2::new(10.0, 10.0)];
        let result = catmull_rom_spline(&points, 10);
        // With only 2 points, returns the original points
        assert_eq!(result.len(), 2);
        assert_eq!(result[0], Vec2::new(0.0, 0.0));
        assert_eq!(result[1], Vec2::new(10.0, 10.0));
    }

    #[test]
    fn test_catmull_rom_spline_three_points() {
        let points = vec![
            Vec2::new(0.0, 0.0),
            Vec2::new(5.0, 5.0),
            Vec2::new(10.0, 0.0),
        ];
        let result = catmull_rom_spline(&points, 4);
        // Should have segments + 1 points per span, plus final point
        assert!(result.len() > 3);
        // First and last should match original
        assert_eq!(result[0], Vec2::new(0.0, 0.0));
        assert_eq!(*result.last().unwrap(), Vec2::new(10.0, 0.0));
    }

    #[test]
    fn test_catmull_rom_spline_many_points() {
        let points = vec![
            Vec2::new(0.0, 0.0),
            Vec2::new(2.0, 4.0),
            Vec2::new(4.0, 0.0),
            Vec2::new(6.0, 4.0),
            Vec2::new(8.0, 0.0),
        ];
        let result = catmull_rom_spline(&points, 8);
        // Should produce smooth interpolation
        assert!(result.len() > points.len());
        // Endpoints preserved
        assert_eq!(result[0], points[0]);
        assert_eq!(*result.last().unwrap(), *points.last().unwrap());
    }

    #[test]
    fn test_catmull_rom_interpolate_at_zero() {
        let p0 = Vec2::new(-1.0, 0.0);
        let p1 = Vec2::new(0.0, 0.0);
        let p2 = Vec2::new(1.0, 0.0);
        let p3 = Vec2::new(2.0, 0.0);
        let result = catmull_rom_interpolate(p0, p1, p2, p3, 0.0);
        // At t=0, should be at p1
        assert!((result.x - p1.x).abs() < 0.001);
        assert!((result.y - p1.y).abs() < 0.001);
    }

    #[test]
    fn test_catmull_rom_interpolate_at_one() {
        let p0 = Vec2::new(-1.0, 0.0);
        let p1 = Vec2::new(0.0, 0.0);
        let p2 = Vec2::new(1.0, 0.0);
        let p3 = Vec2::new(2.0, 0.0);
        let result = catmull_rom_interpolate(p0, p1, p2, p3, 1.0);
        // At t=1, should be at p2
        assert!((result.x - p2.x).abs() < 0.001);
        assert!((result.y - p2.y).abs() < 0.001);
    }

    #[test]
    fn test_catmull_rom_interpolate_midpoint() {
        let p0 = Vec2::new(0.0, 0.0);
        let p1 = Vec2::new(0.0, 0.0);
        let p2 = Vec2::new(4.0, 0.0);
        let p3 = Vec2::new(4.0, 0.0);
        let result = catmull_rom_interpolate(p0, p1, p2, p3, 0.5);
        // At t=0.5, should be roughly in the middle
        assert!(result.x > 1.0 && result.x < 3.0);
    }

    #[test]
    fn test_create_branch_curve_very_short() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(0.1, 0.1);
        let result = create_branch_curve(start, end, 0.5);
        // Very short distance returns just start and end
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_create_branch_curve_horizontal() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 0.0);
        let result = create_branch_curve(start, end, 0.5);
        // Should have multiple points for a proper curve
        assert!(result.len() >= 2);
        // Start and end preserved
        assert_eq!(result[0], start);
        assert_eq!(*result.last().unwrap(), end);
    }

    #[test]
    fn test_create_branch_curve_vertical() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(0.0, 100.0);
        let result = create_branch_curve(start, end, 0.5);
        assert!(result.len() >= 2);
        assert_eq!(result[0], start);
        assert_eq!(*result.last().unwrap(), end);
    }

    #[test]
    fn test_create_branch_curve_diagonal() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let result = create_branch_curve(start, end, 0.4);
        assert!(result.len() >= 2);
        // The curve should have control points that add natural curvature
    }

    #[test]
    fn test_create_branch_curve_zero_tension() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(50.0, 50.0);
        let result = create_branch_curve(start, end, 0.0);
        // With zero tension, should still produce a valid curve
        assert!(result.len() >= 2);
    }
}
