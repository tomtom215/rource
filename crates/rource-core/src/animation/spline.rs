// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Spline interpolation for smooth curves.
//!
//! This module provides Catmull-Rom spline interpolation for creating
//! smooth curves through a series of points. Catmull-Rom splines are
//! ideal for camera paths, edge rendering, and smooth motion.
//!
//! # Catmull-Rom Splines
//!
//! Catmull-Rom splines are a type of cubic interpolating spline that
//! pass through all control points. They provide:
//!
//! - C1 continuity (smooth first derivative)
//! - Local control (changing one point only affects nearby segments)
//! - Simple computation
//!
//! # Example
//!
//! ```
//! use rource_core::animation::{CatmullRomSpline, SplinePoint};
//! use rource_math::Vec2;
//!
//! let mut spline = CatmullRomSpline::new();
//! spline.add_point(Vec2::new(0.0, 0.0));
//! spline.add_point(Vec2::new(100.0, 50.0));
//! spline.add_point(Vec2::new(200.0, 0.0));
//!
//! // Interpolate at t=0.5 (middle of the curve)
//! let point = spline.interpolate(0.5);
//! ```

use rource_math::Vec2;

/// Default tension for Catmull-Rom splines.
///
/// Tension of 0.5 gives the "standard" Catmull-Rom curve.
/// Lower values produce tighter curves, higher values produce looser curves.
pub const DEFAULT_TENSION: f32 = 0.5;

/// Number of segments to use when tessellating the spline.
pub const DEFAULT_SEGMENTS_PER_SPAN: usize = 16;

/// A point on a spline with optional tangent override.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SplinePoint {
    /// Position of the point.
    pub position: Vec2,

    /// Optional tangent override at this point.
    /// If None, the tangent is calculated automatically.
    pub tangent: Option<Vec2>,
}

impl SplinePoint {
    /// Creates a new spline point at the given position.
    #[must_use]
    pub const fn new(position: Vec2) -> Self {
        Self {
            position,
            tangent: None,
        }
    }

    /// Creates a new spline point with a custom tangent.
    #[must_use]
    pub const fn with_tangent(position: Vec2, tangent: Vec2) -> Self {
        Self {
            position,
            tangent: Some(tangent),
        }
    }
}

impl From<Vec2> for SplinePoint {
    fn from(position: Vec2) -> Self {
        Self::new(position)
    }
}

/// A Catmull-Rom spline for smooth curve interpolation.
///
/// Catmull-Rom splines pass through all control points and provide
/// smooth C1 continuous curves. They require at least 2 points to
/// define a curve (with phantom endpoints automatically generated).
#[derive(Debug, Clone)]
pub struct CatmullRomSpline {
    /// Control points of the spline.
    points: Vec<SplinePoint>,

    /// Tension parameter (0.0 to 1.0).
    tension: f32,

    /// Cached tessellated points for rendering.
    cached_points: Vec<Vec2>,

    /// Whether the cache is valid.
    cache_valid: bool,

    /// Number of segments per span for tessellation.
    segments_per_span: usize,
}

impl Default for CatmullRomSpline {
    fn default() -> Self {
        Self::new()
    }
}

impl CatmullRomSpline {
    /// Creates a new empty spline.
    #[must_use]
    pub fn new() -> Self {
        Self {
            points: Vec::new(),
            tension: DEFAULT_TENSION,
            cached_points: Vec::new(),
            cache_valid: false,
            segments_per_span: DEFAULT_SEGMENTS_PER_SPAN,
        }
    }

    /// Creates a spline with the given points.
    #[must_use]
    pub fn from_points(points: impl IntoIterator<Item = Vec2>) -> Self {
        let mut spline = Self::new();
        for point in points {
            spline.add_point(point);
        }
        spline
    }

    /// Creates a spline with custom tension.
    #[must_use]
    pub fn with_tension(tension: f32) -> Self {
        Self {
            tension: tension.clamp(0.0, 1.0),
            ..Self::new()
        }
    }

    /// Returns the number of control points.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.points.len()
    }

    /// Returns true if the spline has no points.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }

    /// Returns the control points.
    #[inline]
    #[must_use]
    pub fn points(&self) -> &[SplinePoint] {
        &self.points
    }

    /// Returns the tension parameter.
    #[inline]
    #[must_use]
    pub const fn tension(&self) -> f32 {
        self.tension
    }

    /// Sets the tension parameter.
    pub fn set_tension(&mut self, tension: f32) {
        self.tension = tension.clamp(0.0, 1.0);
        self.cache_valid = false;
    }

    /// Returns the segments per span for tessellation.
    #[inline]
    #[must_use]
    pub const fn segments_per_span(&self) -> usize {
        self.segments_per_span
    }

    /// Sets the segments per span for tessellation.
    pub fn set_segments_per_span(&mut self, segments: usize) {
        self.segments_per_span = segments.max(1);
        self.cache_valid = false;
    }

    /// Adds a point to the end of the spline.
    pub fn add_point(&mut self, position: Vec2) {
        self.points.push(SplinePoint::new(position));
        self.cache_valid = false;
    }

    /// Adds a point with custom tangent to the spline.
    pub fn add_point_with_tangent(&mut self, position: Vec2, tangent: Vec2) {
        self.points
            .push(SplinePoint::with_tangent(position, tangent));
        self.cache_valid = false;
    }

    /// Inserts a point at the given index.
    pub fn insert_point(&mut self, index: usize, position: Vec2) {
        let index = index.min(self.points.len());
        self.points.insert(index, SplinePoint::new(position));
        self.cache_valid = false;
    }

    /// Removes the point at the given index.
    pub fn remove_point(&mut self, index: usize) -> Option<SplinePoint> {
        if index < self.points.len() {
            self.cache_valid = false;
            Some(self.points.remove(index))
        } else {
            None
        }
    }

    /// Updates the position of a point.
    pub fn set_point(&mut self, index: usize, position: Vec2) {
        if let Some(point) = self.points.get_mut(index) {
            point.position = position;
            self.cache_valid = false;
        }
    }

    /// Clears all points from the spline.
    pub fn clear(&mut self) {
        self.points.clear();
        self.cached_points.clear();
        self.cache_valid = false;
    }

    /// Returns the number of spans in the spline.
    ///
    /// A span connects two adjacent control points.
    #[must_use]
    pub fn span_count(&self) -> usize {
        if self.points.len() < 2 {
            0
        } else {
            self.points.len() - 1
        }
    }

    /// Gets the four control points needed to interpolate a span.
    ///
    /// For endpoints, phantom points are generated by reflecting
    /// the adjacent point.
    fn get_span_points(&self, span_index: usize) -> Option<[Vec2; 4]> {
        if span_index >= self.span_count() {
            return None;
        }

        let n = self.points.len();

        // P0: previous point (or phantom)
        let p0 = if span_index == 0 {
            // Phantom point: reflect P1 around P0
            let p0 = self.points[0].position;
            let p1 = self.points[1].position;
            p0 + (p0 - p1)
        } else {
            self.points[span_index - 1].position
        };

        // P1: start of span
        let p1 = self.points[span_index].position;

        // P2: end of span
        let p2 = self.points[span_index + 1].position;

        // P3: next point (or phantom)
        let p3 = if span_index + 2 >= n {
            // Phantom point: reflect P2 around P1
            p2 + (p2 - p1)
        } else {
            self.points[span_index + 2].position
        };

        Some([p0, p1, p2, p3])
    }

    /// Interpolates a position on the spline.
    ///
    /// # Arguments
    ///
    /// * `t` - Parameter from 0.0 (start) to 1.0 (end)
    ///
    /// # Returns
    ///
    /// The interpolated position, or the first/last point if
    /// t is outside the range.
    #[must_use]
    pub fn interpolate(&self, t: f32) -> Vec2 {
        if self.points.is_empty() {
            return Vec2::ZERO;
        }

        if self.points.len() == 1 {
            return self.points[0].position;
        }

        // Clamp t to valid range
        let t = t.clamp(0.0, 1.0);

        // Find which span we're in
        let span_count = self.span_count() as f32;
        let global_t = t * span_count;
        let span_index = (global_t.floor() as usize).min(self.span_count() - 1);
        let local_t = global_t - span_index as f32;

        self.interpolate_span(span_index, local_t)
    }

    /// Interpolates a position within a specific span.
    ///
    /// # Arguments
    ///
    /// * `span_index` - Index of the span (0 to `span_count` - 1)
    /// * `t` - Parameter from 0.0 (start of span) to 1.0 (end of span)
    #[must_use]
    pub fn interpolate_span(&self, span_index: usize, t: f32) -> Vec2 {
        if let Some([p0, p1, p2, p3]) = self.get_span_points(span_index) {
            catmull_rom(p0, p1, p2, p3, t, self.tension)
        } else if !self.points.is_empty() {
            self.points[0].position
        } else {
            Vec2::ZERO
        }
    }

    /// Interpolates the tangent (derivative) at a point on the spline.
    ///
    /// # Arguments
    ///
    /// * `t` - Parameter from 0.0 (start) to 1.0 (end)
    #[must_use]
    pub fn tangent(&self, t: f32) -> Vec2 {
        if self.points.len() < 2 {
            return Vec2::ZERO;
        }

        let t = t.clamp(0.0, 1.0);
        let span_count = self.span_count() as f32;
        let global_t = t * span_count;
        let span_index = (global_t.floor() as usize).min(self.span_count() - 1);
        let local_t = global_t - span_index as f32;

        self.tangent_span(span_index, local_t)
    }

    /// Interpolates the tangent within a specific span.
    #[must_use]
    pub fn tangent_span(&self, span_index: usize, t: f32) -> Vec2 {
        if let Some([p0, p1, p2, p3]) = self.get_span_points(span_index) {
            catmull_rom_tangent(p0, p1, p2, p3, t, self.tension)
        } else {
            Vec2::ZERO
        }
    }

    /// Returns the total approximate length of the spline.
    ///
    /// This uses linear approximation based on the tessellated points.
    #[must_use]
    pub fn approximate_length(&mut self) -> f32 {
        self.ensure_cache();

        let mut length = 0.0;
        for window in self.cached_points.windows(2) {
            length += (window[1] - window[0]).length();
        }
        length
    }

    /// Tessellates the spline into a series of line segments.
    ///
    /// This is useful for rendering the spline as a polyline.
    #[must_use]
    pub fn tessellate(&mut self) -> &[Vec2] {
        self.ensure_cache();
        &self.cached_points
    }

    /// Ensures the cache is up to date.
    fn ensure_cache(&mut self) {
        if self.cache_valid {
            return;
        }

        self.cached_points.clear();

        if self.points.len() < 2 {
            if !self.points.is_empty() {
                self.cached_points.push(self.points[0].position);
            }
            self.cache_valid = true;
            return;
        }

        let total_segments = self.span_count() * self.segments_per_span;
        self.cached_points.reserve(total_segments + 1);

        for i in 0..=total_segments {
            let t = i as f32 / total_segments as f32;
            self.cached_points.push(self.interpolate(t));
        }

        self.cache_valid = true;
    }

    /// Finds the closest point on the spline to the given position.
    ///
    /// Returns (t, distance) where t is the parameter and distance
    /// is the distance to the closest point.
    #[must_use]
    pub fn closest_point(&mut self, position: Vec2) -> (f32, f32) {
        self.ensure_cache();

        if self.cached_points.is_empty() {
            return (0.0, f32::INFINITY);
        }

        let mut best_t = 0.0;
        let mut best_dist = f32::INFINITY;

        for (i, point) in self.cached_points.iter().enumerate() {
            let dist = (*point - position).length();
            if dist < best_dist {
                best_dist = dist;
                best_t = i as f32 / (self.cached_points.len() - 1).max(1) as f32;
            }
        }

        (best_t, best_dist)
    }
}

/// Catmull-Rom interpolation between four points.
///
/// The curve passes through P1 and P2, using P0 and P3 to
/// determine the tangents at those points.
///
/// # Arguments
///
/// * `p0` - Previous point (for tangent calculation)
/// * `p1` - Start of segment
/// * `p2` - End of segment
/// * `p3` - Next point (for tangent calculation)
/// * `t` - Parameter (0.0 to 1.0)
/// * `tension` - Tension parameter (0.5 is standard)
#[must_use]
pub fn catmull_rom(p0: Vec2, p1: Vec2, p2: Vec2, p3: Vec2, t: f32, tension: f32) -> Vec2 {
    let t2 = t * t;
    let t3 = t2 * t;

    // Catmull-Rom basis matrix with tension
    // Standard is tension = 0.5
    let s = tension;

    // Coefficients for the cubic polynomial
    let a0 = -s * t3 + 2.0 * s * t2 - s * t;
    let a1 = (2.0 - s) * t3 + (s - 3.0) * t2 + 1.0;
    let a2 = (s - 2.0) * t3 + (3.0 - 2.0 * s) * t2 + s * t;
    let a3 = s * t3 - s * t2;

    p0 * a0 + p1 * a1 + p2 * a2 + p3 * a3
}

/// Catmull-Rom tangent (derivative) at a point.
#[must_use]
pub fn catmull_rom_tangent(p0: Vec2, p1: Vec2, p2: Vec2, p3: Vec2, t: f32, tension: f32) -> Vec2 {
    let t2 = t * t;
    let s = tension;

    // Derivative of the Catmull-Rom polynomial
    let d0 = -3.0 * s * t2 + 4.0 * s * t - s;
    let d1 = 3.0 * (2.0 - s) * t2 + 2.0 * (s - 3.0) * t;
    let d2 = 3.0 * (s - 2.0) * t2 + 2.0 * (3.0 - 2.0 * s) * t + s;
    let d3 = 3.0 * s * t2 - 2.0 * s * t;

    p0 * d0 + p1 * d1 + p2 * d2 + p3 * d3
}

/// A simple linear spline (polyline) for comparison.
#[derive(Debug, Clone)]
pub struct LinearSpline {
    points: Vec<Vec2>,
}

impl Default for LinearSpline {
    fn default() -> Self {
        Self::new()
    }
}

impl LinearSpline {
    /// Creates a new empty linear spline.
    #[must_use]
    pub fn new() -> Self {
        Self { points: Vec::new() }
    }

    /// Creates a linear spline from points.
    #[must_use]
    pub fn from_points(points: impl IntoIterator<Item = Vec2>) -> Self {
        Self {
            points: points.into_iter().collect(),
        }
    }

    /// Returns the number of points.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.points.len()
    }

    /// Returns true if empty.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }

    /// Returns the points.
    #[inline]
    #[must_use]
    pub fn points(&self) -> &[Vec2] {
        &self.points
    }

    /// Adds a point.
    pub fn add_point(&mut self, point: Vec2) {
        self.points.push(point);
    }

    /// Clears all points.
    pub fn clear(&mut self) {
        self.points.clear();
    }

    /// Interpolates along the spline.
    #[must_use]
    pub fn interpolate(&self, t: f32) -> Vec2 {
        if self.points.is_empty() {
            return Vec2::ZERO;
        }

        if self.points.len() == 1 {
            return self.points[0];
        }

        let t = t.clamp(0.0, 1.0);
        let segment_count = (self.points.len() - 1) as f32;
        let global_t = t * segment_count;
        let segment_index = (global_t.floor() as usize).min(self.points.len() - 2);
        let local_t = global_t - segment_index as f32;

        self.points[segment_index].lerp(self.points[segment_index + 1], local_t)
    }

    /// Returns the total length of the spline.
    #[must_use]
    pub fn length(&self) -> f32 {
        let mut len = 0.0;
        for window in self.points.windows(2) {
            len += (window[1] - window[0]).length();
        }
        len
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPSILON: f32 = 0.001;

    fn approx_eq(a: f32, b: f32) -> bool {
        (a - b).abs() < EPSILON
    }

    fn vec2_approx_eq(a: Vec2, b: Vec2) -> bool {
        approx_eq(a.x, b.x) && approx_eq(a.y, b.y)
    }

    #[test]
    fn test_spline_point_new() {
        let point = SplinePoint::new(Vec2::new(10.0, 20.0));
        assert_eq!(point.position, Vec2::new(10.0, 20.0));
        assert!(point.tangent.is_none());
    }

    #[test]
    fn test_spline_point_with_tangent() {
        let point = SplinePoint::with_tangent(Vec2::new(10.0, 20.0), Vec2::new(1.0, 0.0));
        assert_eq!(point.position, Vec2::new(10.0, 20.0));
        assert_eq!(point.tangent, Some(Vec2::new(1.0, 0.0)));
    }

    #[test]
    fn test_spline_empty() {
        let spline = CatmullRomSpline::new();

        assert!(spline.is_empty());
        assert_eq!(spline.len(), 0);
        assert_eq!(spline.span_count(), 0);
    }

    #[test]
    fn test_spline_single_point() {
        let mut spline = CatmullRomSpline::new();
        spline.add_point(Vec2::new(10.0, 20.0));

        assert_eq!(spline.len(), 1);
        assert_eq!(spline.span_count(), 0);

        // Interpolation should return the single point
        let p = spline.interpolate(0.5);
        assert!(vec2_approx_eq(p, Vec2::new(10.0, 20.0)));
    }

    #[test]
    fn test_spline_two_points() {
        let mut spline = CatmullRomSpline::new();
        spline.add_point(Vec2::new(0.0, 0.0));
        spline.add_point(Vec2::new(100.0, 0.0));

        assert_eq!(spline.len(), 2);
        assert_eq!(spline.span_count(), 1);

        // Start
        let p0 = spline.interpolate(0.0);
        assert!(vec2_approx_eq(p0, Vec2::new(0.0, 0.0)));

        // End
        let p1 = spline.interpolate(1.0);
        assert!(vec2_approx_eq(p1, Vec2::new(100.0, 0.0)));

        // Middle should be approximately in the middle
        let mid = spline.interpolate(0.5);
        assert!(approx_eq(mid.x, 50.0));
    }

    #[test]
    fn test_spline_three_points() {
        let mut spline = CatmullRomSpline::new();
        spline.add_point(Vec2::new(0.0, 0.0));
        spline.add_point(Vec2::new(50.0, 50.0));
        spline.add_point(Vec2::new(100.0, 0.0));

        assert_eq!(spline.span_count(), 2);

        // Endpoints
        assert!(vec2_approx_eq(spline.interpolate(0.0), Vec2::new(0.0, 0.0)));
        assert!(vec2_approx_eq(
            spline.interpolate(1.0),
            Vec2::new(100.0, 0.0)
        ));

        // Middle point (t=0.5 should be at the middle control point)
        let mid = spline.interpolate(0.5);
        assert!(approx_eq(mid.x, 50.0));
    }

    #[test]
    fn test_spline_from_points() {
        let points = vec![Vec2::new(0.0, 0.0), Vec2::new(100.0, 100.0)];
        let spline = CatmullRomSpline::from_points(points);

        assert_eq!(spline.len(), 2);
    }

    #[test]
    fn test_spline_tension() {
        let mut spline = CatmullRomSpline::with_tension(0.3);
        assert!(approx_eq(spline.tension(), 0.3));

        spline.set_tension(0.7);
        assert!(approx_eq(spline.tension(), 0.7));

        // Tension should be clamped
        spline.set_tension(2.0);
        assert!(approx_eq(spline.tension(), 1.0));

        spline.set_tension(-1.0);
        assert!(approx_eq(spline.tension(), 0.0));
    }

    #[test]
    fn test_spline_modify_points() {
        let mut spline = CatmullRomSpline::new();
        spline.add_point(Vec2::new(0.0, 0.0));
        spline.add_point(Vec2::new(100.0, 0.0));

        spline.set_point(1, Vec2::new(100.0, 100.0));
        assert!(vec2_approx_eq(
            spline.interpolate(1.0),
            Vec2::new(100.0, 100.0)
        ));

        spline.insert_point(1, Vec2::new(50.0, 50.0));
        assert_eq!(spline.len(), 3);

        let removed = spline.remove_point(1);
        assert!(removed.is_some());
        assert_eq!(spline.len(), 2);
    }

    #[test]
    fn test_spline_clear() {
        let mut spline = CatmullRomSpline::new();
        spline.add_point(Vec2::new(0.0, 0.0));
        spline.add_point(Vec2::new(100.0, 0.0));

        spline.clear();
        assert!(spline.is_empty());
    }

    #[test]
    fn test_spline_tessellate() {
        let mut spline = CatmullRomSpline::new();
        spline.add_point(Vec2::new(0.0, 0.0));
        spline.add_point(Vec2::new(100.0, 0.0));
        spline.set_segments_per_span(8);

        let points = spline.tessellate();
        assert_eq!(points.len(), 9); // 8 segments + 1

        // First and last should match endpoints
        assert!(vec2_approx_eq(points[0], Vec2::new(0.0, 0.0)));
        assert!(vec2_approx_eq(points[8], Vec2::new(100.0, 0.0)));
    }

    #[test]
    fn test_spline_tangent() {
        let mut spline = CatmullRomSpline::new();
        spline.add_point(Vec2::new(0.0, 0.0));
        spline.add_point(Vec2::new(100.0, 0.0));

        let tangent = spline.tangent(0.5);
        // For a straight line, tangent should point in direction of line
        assert!(tangent.x > 0.0);
    }

    #[test]
    fn test_spline_length() {
        let mut spline = CatmullRomSpline::new();
        spline.add_point(Vec2::new(0.0, 0.0));
        spline.add_point(Vec2::new(100.0, 0.0));

        let length = spline.approximate_length();
        // Should be approximately 100 for a straight line
        assert!(approx_eq(length, 100.0));
    }

    #[test]
    fn test_spline_closest_point() {
        let mut spline = CatmullRomSpline::new();
        spline.add_point(Vec2::new(0.0, 0.0));
        spline.add_point(Vec2::new(100.0, 0.0));

        let (t, dist) = spline.closest_point(Vec2::new(50.0, 10.0));
        assert!(approx_eq(t, 0.5));
        assert!(approx_eq(dist, 10.0));
    }

    #[test]
    fn test_catmull_rom_function() {
        let p0 = Vec2::new(-50.0, 0.0);
        let p1 = Vec2::new(0.0, 0.0);
        let p2 = Vec2::new(100.0, 0.0);
        let p3 = Vec2::new(150.0, 0.0);

        // At t=0, should be at p1
        let at_0 = catmull_rom(p0, p1, p2, p3, 0.0, 0.5);
        assert!(vec2_approx_eq(at_0, p1));

        // At t=1, should be at p2
        let at_1 = catmull_rom(p0, p1, p2, p3, 1.0, 0.5);
        assert!(vec2_approx_eq(at_1, p2));
    }

    #[test]
    fn test_linear_spline() {
        let mut spline = LinearSpline::new();
        spline.add_point(Vec2::new(0.0, 0.0));
        spline.add_point(Vec2::new(100.0, 0.0));

        assert_eq!(spline.len(), 2);

        let mid = spline.interpolate(0.5);
        assert!(vec2_approx_eq(mid, Vec2::new(50.0, 0.0)));

        let length = spline.length();
        assert!(approx_eq(length, 100.0));
    }

    #[test]
    fn test_linear_spline_from_points() {
        let spline = LinearSpline::from_points(vec![Vec2::new(0.0, 0.0), Vec2::new(100.0, 100.0)]);

        assert_eq!(spline.len(), 2);
        let mid = spline.interpolate(0.5);
        assert!(vec2_approx_eq(mid, Vec2::new(50.0, 50.0)));
    }

    #[test]
    fn test_spline_clamp_t() {
        let mut spline = CatmullRomSpline::new();
        spline.add_point(Vec2::new(0.0, 0.0));
        spline.add_point(Vec2::new(100.0, 0.0));

        // t outside valid range should be clamped
        let before = spline.interpolate(-0.5);
        let after = spline.interpolate(1.5);

        assert!(vec2_approx_eq(before, Vec2::new(0.0, 0.0)));
        assert!(vec2_approx_eq(after, Vec2::new(100.0, 0.0)));
    }
}
