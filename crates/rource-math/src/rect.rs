// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Rectangle and bounds types for 2D regions.

use std::fmt;

use crate::Vec2;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A rectangle defined by position and size.
///
/// The position is the top-left corner in screen coordinates (Y-down).
///
/// # Examples
///
/// ```
/// use rource_math::{Rect, Vec2};
///
/// let rect = Rect::new(10.0, 20.0, 100.0, 50.0);
/// assert_eq!(rect.x, 10.0);
/// assert_eq!(rect.width, 100.0);
/// assert!(rect.contains(Vec2::new(50.0, 40.0)));
/// ```
#[derive(Clone, Copy, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Rect {
    /// X coordinate of the top-left corner.
    pub x: f32,
    /// Y coordinate of the top-left corner.
    pub y: f32,
    /// Width of the rectangle.
    pub width: f32,
    /// Height of the rectangle.
    pub height: f32,
}

impl Rect {
    /// A zero-sized rectangle at the origin.
    pub const ZERO: Self = Self {
        x: 0.0,
        y: 0.0,
        width: 0.0,
        height: 0.0,
    };

    /// Creates a new rectangle.
    #[inline]
    #[must_use]
    pub const fn new(x: f32, y: f32, width: f32, height: f32) -> Self {
        Self {
            x,
            y,
            width,
            height,
        }
    }

    /// Creates a rectangle from position and size vectors.
    #[inline]
    #[must_use]
    pub const fn from_pos_size(pos: Vec2, size: Vec2) -> Self {
        Self {
            x: pos.x,
            y: pos.y,
            width: size.x,
            height: size.y,
        }
    }

    /// Creates a rectangle from two corner points.
    ///
    /// The corners can be in any order; the rectangle will be normalized.
    #[inline]
    #[must_use]
    pub fn from_corners(a: Vec2, b: Vec2) -> Self {
        let min_x = a.x.min(b.x);
        let min_y = a.y.min(b.y);
        let max_x = a.x.max(b.x);
        let max_y = a.y.max(b.y);
        Self {
            x: min_x,
            y: min_y,
            width: max_x - min_x,
            height: max_y - min_y,
        }
    }

    /// Creates a rectangle centered at a point with the given size.
    #[inline]
    #[must_use]
    pub fn from_center_size(center: Vec2, size: Vec2) -> Self {
        Self {
            x: center.x - size.x / 2.0,
            y: center.y - size.y / 2.0,
            width: size.x,
            height: size.y,
        }
    }

    /// Returns the position (top-left corner) as a Vec2.
    #[inline]
    #[must_use]
    pub const fn position(self) -> Vec2 {
        Vec2 {
            x: self.x,
            y: self.y,
        }
    }

    /// Returns the size as a Vec2.
    #[inline]
    #[must_use]
    pub const fn size(self) -> Vec2 {
        Vec2 {
            x: self.width,
            y: self.height,
        }
    }

    /// Returns the center point of the rectangle.
    #[inline]
    #[must_use]
    pub fn center(self) -> Vec2 {
        Vec2 {
            x: self.x + self.width / 2.0,
            y: self.y + self.height / 2.0,
        }
    }

    /// Returns the minimum (top-left) corner.
    #[inline]
    #[must_use]
    pub const fn min(self) -> Vec2 {
        Vec2 {
            x: self.x,
            y: self.y,
        }
    }

    /// Returns the maximum (bottom-right) corner.
    #[inline]
    #[must_use]
    pub fn max(self) -> Vec2 {
        Vec2 {
            x: self.x + self.width,
            y: self.y + self.height,
        }
    }

    /// Returns the left edge X coordinate.
    #[inline]
    #[must_use]
    pub const fn left(self) -> f32 {
        self.x
    }

    /// Returns the right edge X coordinate.
    #[inline]
    #[must_use]
    pub fn right(self) -> f32 {
        self.x + self.width
    }

    /// Returns the top edge Y coordinate.
    #[inline]
    #[must_use]
    pub const fn top(self) -> f32 {
        self.y
    }

    /// Returns the bottom edge Y coordinate.
    #[inline]
    #[must_use]
    pub fn bottom(self) -> f32 {
        self.y + self.height
    }

    /// Returns the area of the rectangle.
    #[inline]
    #[must_use]
    pub fn area(self) -> f32 {
        self.width * self.height
    }

    /// Returns the perimeter of the rectangle.
    #[inline]
    #[must_use]
    pub fn perimeter(self) -> f32 {
        2.0 * (self.width + self.height)
    }

    /// Checks if the rectangle contains a point.
    #[inline]
    #[must_use]
    pub fn contains(self, point: Vec2) -> bool {
        point.x >= self.x
            && point.x <= self.x + self.width
            && point.y >= self.y
            && point.y <= self.y + self.height
    }

    /// Checks if this rectangle contains another rectangle entirely.
    #[inline]
    #[must_use]
    pub fn contains_rect(self, other: Self) -> bool {
        other.x >= self.x
            && other.y >= self.y
            && other.x + other.width <= self.x + self.width
            && other.y + other.height <= self.y + self.height
    }

    /// Checks if this rectangle intersects another.
    #[inline]
    #[must_use]
    pub fn intersects(self, other: Self) -> bool {
        self.x < other.x + other.width
            && self.x + self.width > other.x
            && self.y < other.y + other.height
            && self.y + self.height > other.y
    }

    /// Returns the intersection of two rectangles, or `None` if they don't intersect.
    #[must_use]
    pub fn intersection(self, other: Self) -> Option<Self> {
        let x = self.x.max(other.x);
        let y = self.y.max(other.y);
        let right = (self.x + self.width).min(other.x + other.width);
        let bottom = (self.y + self.height).min(other.y + other.height);

        if right > x && bottom > y {
            Some(Self {
                x,
                y,
                width: right - x,
                height: bottom - y,
            })
        } else {
            None
        }
    }

    /// Returns the smallest rectangle containing both this and another rectangle.
    #[inline]
    #[must_use]
    pub fn union(self, other: Self) -> Self {
        let x = self.x.min(other.x);
        let y = self.y.min(other.y);
        let right = (self.x + self.width).max(other.x + other.width);
        let bottom = (self.y + self.height).max(other.y + other.height);
        Self {
            x,
            y,
            width: right - x,
            height: bottom - y,
        }
    }

    /// Expands the rectangle by the given amount on all sides.
    #[inline]
    #[must_use]
    pub fn expand(self, amount: f32) -> Self {
        Self {
            x: self.x - amount,
            y: self.y - amount,
            width: self.width + 2.0 * amount,
            height: self.height + 2.0 * amount,
        }
    }

    /// Expands the rectangle by different amounts on each axis.
    #[inline]
    #[must_use]
    pub fn expand_xy(self, x_amount: f32, y_amount: f32) -> Self {
        Self {
            x: self.x - x_amount,
            y: self.y - y_amount,
            width: self.width + 2.0 * x_amount,
            height: self.height + 2.0 * y_amount,
        }
    }

    /// Contracts the rectangle by the given amount on all sides.
    #[inline]
    #[must_use]
    pub fn shrink(self, amount: f32) -> Self {
        self.expand(-amount)
    }

    /// Translates the rectangle by the given offset.
    #[inline]
    #[must_use]
    pub fn translate(self, offset: Vec2) -> Self {
        Self {
            x: self.x + offset.x,
            y: self.y + offset.y,
            width: self.width,
            height: self.height,
        }
    }

    /// Scales the rectangle by a factor, keeping the center fixed.
    #[inline]
    #[must_use]
    pub fn scale_from_center(self, factor: f32) -> Self {
        let center = self.center();
        let new_width = self.width * factor;
        let new_height = self.height * factor;
        Self {
            x: center.x - new_width / 2.0,
            y: center.y - new_height / 2.0,
            width: new_width,
            height: new_height,
        }
    }

    /// Returns true if the rectangle has positive area.
    #[inline]
    #[must_use]
    pub fn is_valid(self) -> bool {
        self.width > 0.0 && self.height > 0.0
    }

    /// Returns true if the rectangle has zero or negative area.
    #[inline]
    #[must_use]
    pub fn is_empty(self) -> bool {
        self.width <= 0.0 || self.height <= 0.0
    }

    /// Converts to a Bounds type.
    #[inline]
    #[must_use]
    pub fn to_bounds(self) -> Bounds {
        Bounds {
            min: self.min(),
            max: self.max(),
        }
    }

    /// Checks if this rectangle is approximately equal to another.
    #[inline]
    #[must_use]
    pub fn approx_eq(self, other: Self) -> bool {
        crate::approx_eq(self.x, other.x)
            && crate::approx_eq(self.y, other.y)
            && crate::approx_eq(self.width, other.width)
            && crate::approx_eq(self.height, other.height)
    }
}

impl fmt::Debug for Rect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Rect")
            .field("x", &self.x)
            .field("y", &self.y)
            .field("width", &self.width)
            .field("height", &self.height)
            .finish()
    }
}

impl fmt::Display for Rect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Rect({}, {}, {}x{})",
            self.x, self.y, self.width, self.height
        )
    }
}

/// A 2D bounding box defined by minimum and maximum corners.
///
/// This is an alternative representation to [`Rect`] that's sometimes
/// more convenient for certain operations like union and intersection.
///
/// # Examples
///
/// ```
/// use rource_math::{Bounds, Vec2};
///
/// let bounds = Bounds::new(Vec2::new(0.0, 0.0), Vec2::new(100.0, 100.0));
/// assert!(bounds.contains(Vec2::new(50.0, 50.0)));
/// ```
#[derive(Clone, Copy, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Bounds {
    /// Minimum corner (top-left in screen coordinates).
    pub min: Vec2,
    /// Maximum corner (bottom-right in screen coordinates).
    pub max: Vec2,
}

impl Bounds {
    /// An "inverted" bounds useful for computing bounds from points.
    ///
    /// Use this as the starting value when accumulating bounds:
    /// ```
    /// use rource_math::{Bounds, Vec2};
    ///
    /// let mut bounds = Bounds::INVERTED;
    /// bounds = bounds.include_point(Vec2::new(10.0, 20.0));
    /// bounds = bounds.include_point(Vec2::new(30.0, 40.0));
    /// ```
    pub const INVERTED: Self = Self {
        min: Vec2 {
            x: f32::INFINITY,
            y: f32::INFINITY,
        },
        max: Vec2 {
            x: f32::NEG_INFINITY,
            y: f32::NEG_INFINITY,
        },
    };

    /// A zero-sized bounds at the origin.
    pub const ZERO: Self = Self {
        min: Vec2::ZERO,
        max: Vec2::ZERO,
    };

    /// Creates a new bounds from min and max corners.
    #[inline]
    #[must_use]
    pub const fn new(min: Vec2, max: Vec2) -> Self {
        Self { min, max }
    }

    /// Creates bounds from any two corner points.
    #[inline]
    #[must_use]
    pub fn from_points(a: Vec2, b: Vec2) -> Self {
        Self {
            min: a.min(b),
            max: a.max(b),
        }
    }

    /// Creates bounds from a center point and half-extents.
    #[inline]
    #[must_use]
    pub fn from_center_half_extents(center: Vec2, half_extents: Vec2) -> Self {
        Self {
            min: center - half_extents,
            max: center + half_extents,
        }
    }

    /// Creates bounds from a center point and size.
    #[inline]
    #[must_use]
    pub fn from_center_size(center: Vec2, size: Vec2) -> Self {
        Self::from_center_half_extents(center, size * 0.5)
    }

    /// Returns the width of the bounds.
    #[inline]
    #[must_use]
    pub fn width(self) -> f32 {
        self.max.x - self.min.x
    }

    /// Returns the height of the bounds.
    #[inline]
    #[must_use]
    pub fn height(self) -> f32 {
        self.max.y - self.min.y
    }

    /// Returns the size as a Vec2.
    #[inline]
    #[must_use]
    pub fn size(self) -> Vec2 {
        self.max - self.min
    }

    /// Returns the center of the bounds.
    #[inline]
    #[must_use]
    pub fn center(self) -> Vec2 {
        (self.min + self.max) * 0.5
    }

    /// Returns the half-extents (half of size).
    #[inline]
    #[must_use]
    pub fn half_extents(self) -> Vec2 {
        self.size() * 0.5
    }

    /// Returns the area of the bounds.
    #[inline]
    #[must_use]
    pub fn area(self) -> f32 {
        self.width() * self.height()
    }

    /// Checks if the bounds contains a point.
    #[inline]
    #[must_use]
    pub fn contains(self, point: Vec2) -> bool {
        point.x >= self.min.x
            && point.x <= self.max.x
            && point.y >= self.min.y
            && point.y <= self.max.y
    }

    /// Checks if this bounds contains another bounds entirely.
    #[inline]
    #[must_use]
    pub fn contains_bounds(self, other: Self) -> bool {
        other.min.x >= self.min.x
            && other.min.y >= self.min.y
            && other.max.x <= self.max.x
            && other.max.y <= self.max.y
    }

    /// Checks if this bounds intersects another.
    #[inline]
    #[must_use]
    pub fn intersects(self, other: Self) -> bool {
        self.min.x < other.max.x
            && self.max.x > other.min.x
            && self.min.y < other.max.y
            && self.max.y > other.min.y
    }

    /// Returns the intersection of two bounds, or `None` if they don't intersect.
    #[must_use]
    pub fn intersection(self, other: Self) -> Option<Self> {
        let min = self.min.max(other.min);
        let max = self.max.min(other.max);

        if min.x < max.x && min.y < max.y {
            Some(Self { min, max })
        } else {
            None
        }
    }

    /// Returns the smallest bounds containing both this and another bounds.
    #[inline]
    #[must_use]
    pub fn union(self, other: Self) -> Self {
        Self {
            min: self.min.min(other.min),
            max: self.max.max(other.max),
        }
    }

    /// Returns bounds expanded to include the given point.
    #[inline]
    #[must_use]
    pub fn include_point(self, point: Vec2) -> Self {
        Self {
            min: self.min.min(point),
            max: self.max.max(point),
        }
    }

    /// Expands the bounds by the given amount on all sides.
    #[inline]
    #[must_use]
    pub fn expand(self, amount: f32) -> Self {
        let expand_vec = Vec2::splat(amount);
        Self {
            min: self.min - expand_vec,
            max: self.max + expand_vec,
        }
    }

    /// Contracts the bounds by the given amount on all sides.
    #[inline]
    #[must_use]
    pub fn shrink(self, amount: f32) -> Self {
        self.expand(-amount)
    }

    /// Translates the bounds by the given offset.
    #[inline]
    #[must_use]
    pub fn translate(self, offset: Vec2) -> Self {
        Self {
            min: self.min + offset,
            max: self.max + offset,
        }
    }

    /// Returns true if the bounds has positive area.
    #[inline]
    #[must_use]
    pub fn is_valid(self) -> bool {
        self.max.x > self.min.x && self.max.y > self.min.y
    }

    /// Returns true if the bounds is inverted or has zero area.
    #[inline]
    #[must_use]
    pub fn is_empty(self) -> bool {
        self.max.x <= self.min.x || self.max.y <= self.min.y
    }

    /// Converts to a Rect type.
    #[inline]
    #[must_use]
    pub fn to_rect(self) -> Rect {
        Rect {
            x: self.min.x,
            y: self.min.y,
            width: self.max.x - self.min.x,
            height: self.max.y - self.min.y,
        }
    }

    /// Checks if this bounds is approximately equal to another.
    #[inline]
    #[must_use]
    pub fn approx_eq(self, other: Self) -> bool {
        self.min.approx_eq(other.min) && self.max.approx_eq(other.max)
    }
}

impl fmt::Debug for Bounds {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Bounds")
            .field("min", &self.min)
            .field("max", &self.max)
            .finish()
    }
}

impl fmt::Display for Bounds {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Bounds({} to {})", self.min, self.max)
    }
}

impl From<Rect> for Bounds {
    #[inline]
    fn from(rect: Rect) -> Self {
        rect.to_bounds()
    }
}

impl From<Bounds> for Rect {
    #[inline]
    fn from(bounds: Bounds) -> Self {
        bounds.to_rect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rect_new() {
        let r = Rect::new(10.0, 20.0, 100.0, 50.0);
        assert_eq!(r.x, 10.0);
        assert_eq!(r.y, 20.0);
        assert_eq!(r.width, 100.0);
        assert_eq!(r.height, 50.0);
    }

    #[test]
    fn test_rect_from_corners() {
        let r = Rect::from_corners(Vec2::new(10.0, 20.0), Vec2::new(110.0, 70.0));
        assert_eq!(r.x, 10.0);
        assert_eq!(r.y, 20.0);
        assert_eq!(r.width, 100.0);
        assert_eq!(r.height, 50.0);

        // Reversed corners should give same result
        let r2 = Rect::from_corners(Vec2::new(110.0, 70.0), Vec2::new(10.0, 20.0));
        assert!(r.approx_eq(r2));
    }

    #[test]
    fn test_rect_from_center_size() {
        let r = Rect::from_center_size(Vec2::new(50.0, 50.0), Vec2::new(100.0, 100.0));
        assert_eq!(r.x, 0.0);
        assert_eq!(r.y, 0.0);
        assert_eq!(r.width, 100.0);
        assert_eq!(r.height, 100.0);
    }

    #[test]
    fn test_rect_accessors() {
        let r = Rect::new(10.0, 20.0, 100.0, 50.0);

        assert_eq!(r.position(), Vec2::new(10.0, 20.0));
        assert_eq!(r.size(), Vec2::new(100.0, 50.0));
        assert_eq!(r.center(), Vec2::new(60.0, 45.0));
        assert_eq!(r.min(), Vec2::new(10.0, 20.0));
        assert_eq!(r.max(), Vec2::new(110.0, 70.0));
        assert_eq!(r.left(), 10.0);
        assert_eq!(r.right(), 110.0);
        assert_eq!(r.top(), 20.0);
        assert_eq!(r.bottom(), 70.0);
        assert_eq!(r.area(), 5000.0);
        assert_eq!(r.perimeter(), 300.0);
    }

    #[test]
    fn test_rect_contains() {
        let r = Rect::new(0.0, 0.0, 100.0, 100.0);

        assert!(r.contains(Vec2::new(50.0, 50.0)));
        assert!(r.contains(Vec2::new(0.0, 0.0)));
        assert!(r.contains(Vec2::new(100.0, 100.0)));
        assert!(!r.contains(Vec2::new(-1.0, 50.0)));
        assert!(!r.contains(Vec2::new(101.0, 50.0)));
    }

    #[test]
    fn test_rect_contains_rect() {
        let outer = Rect::new(0.0, 0.0, 100.0, 100.0);
        let inner = Rect::new(10.0, 10.0, 50.0, 50.0);
        let overlapping = Rect::new(50.0, 50.0, 100.0, 100.0);

        assert!(outer.contains_rect(inner));
        assert!(!outer.contains_rect(overlapping));
        assert!(!inner.contains_rect(outer));
    }

    #[test]
    fn test_rect_intersects() {
        let a = Rect::new(0.0, 0.0, 100.0, 100.0);
        let b = Rect::new(50.0, 50.0, 100.0, 100.0);
        let c = Rect::new(200.0, 200.0, 100.0, 100.0);

        assert!(a.intersects(b));
        assert!(b.intersects(a));
        assert!(!a.intersects(c));
    }

    #[test]
    fn test_rect_intersection() {
        let a = Rect::new(0.0, 0.0, 100.0, 100.0);
        let b = Rect::new(50.0, 50.0, 100.0, 100.0);

        let intersection = a.intersection(b).unwrap();
        assert_eq!(intersection.x, 50.0);
        assert_eq!(intersection.y, 50.0);
        assert_eq!(intersection.width, 50.0);
        assert_eq!(intersection.height, 50.0);

        let c = Rect::new(200.0, 200.0, 100.0, 100.0);
        assert!(a.intersection(c).is_none());
    }

    #[test]
    fn test_rect_union() {
        let a = Rect::new(0.0, 0.0, 100.0, 100.0);
        let b = Rect::new(50.0, 50.0, 100.0, 100.0);

        let union = a.union(b);
        assert_eq!(union.x, 0.0);
        assert_eq!(union.y, 0.0);
        assert_eq!(union.width, 150.0);
        assert_eq!(union.height, 150.0);
    }

    #[test]
    fn test_rect_expand_shrink() {
        let r = Rect::new(10.0, 10.0, 80.0, 80.0);

        let expanded = r.expand(10.0);
        assert_eq!(expanded.x, 0.0);
        assert_eq!(expanded.y, 0.0);
        assert_eq!(expanded.width, 100.0);
        assert_eq!(expanded.height, 100.0);

        let shrunk = r.shrink(10.0);
        assert_eq!(shrunk.x, 20.0);
        assert_eq!(shrunk.y, 20.0);
        assert_eq!(shrunk.width, 60.0);
        assert_eq!(shrunk.height, 60.0);
    }

    #[test]
    fn test_rect_translate() {
        let r = Rect::new(0.0, 0.0, 100.0, 100.0);
        let translated = r.translate(Vec2::new(50.0, 50.0));
        assert_eq!(translated.x, 50.0);
        assert_eq!(translated.y, 50.0);
        assert_eq!(translated.width, 100.0);
        assert_eq!(translated.height, 100.0);
    }

    #[test]
    fn test_rect_scale_from_center() {
        let r = Rect::new(0.0, 0.0, 100.0, 100.0);
        let scaled = r.scale_from_center(2.0);
        assert_eq!(scaled.center(), r.center());
        assert_eq!(scaled.width, 200.0);
        assert_eq!(scaled.height, 200.0);
    }

    #[test]
    fn test_rect_validity() {
        assert!(Rect::new(0.0, 0.0, 100.0, 100.0).is_valid());
        assert!(!Rect::new(0.0, 0.0, 0.0, 100.0).is_valid());
        assert!(!Rect::new(0.0, 0.0, -100.0, 100.0).is_valid());

        assert!(!Rect::new(0.0, 0.0, 100.0, 100.0).is_empty());
        assert!(Rect::new(0.0, 0.0, 0.0, 100.0).is_empty());
    }

    #[test]
    fn test_bounds_new() {
        let b = Bounds::new(Vec2::new(0.0, 0.0), Vec2::new(100.0, 100.0));
        assert_eq!(b.min, Vec2::new(0.0, 0.0));
        assert_eq!(b.max, Vec2::new(100.0, 100.0));
    }

    #[test]
    fn test_bounds_from_points() {
        let b = Bounds::from_points(Vec2::new(100.0, 100.0), Vec2::new(0.0, 0.0));
        assert_eq!(b.min, Vec2::new(0.0, 0.0));
        assert_eq!(b.max, Vec2::new(100.0, 100.0));
    }

    #[test]
    fn test_bounds_from_center() {
        let b = Bounds::from_center_size(Vec2::new(50.0, 50.0), Vec2::new(100.0, 100.0));
        assert!(b.min.approx_eq(Vec2::new(0.0, 0.0)));
        assert!(b.max.approx_eq(Vec2::new(100.0, 100.0)));
    }

    #[test]
    fn test_bounds_accessors() {
        let b = Bounds::new(Vec2::new(10.0, 20.0), Vec2::new(110.0, 70.0));

        assert_eq!(b.width(), 100.0);
        assert_eq!(b.height(), 50.0);
        assert_eq!(b.size(), Vec2::new(100.0, 50.0));
        assert_eq!(b.center(), Vec2::new(60.0, 45.0));
        assert_eq!(b.half_extents(), Vec2::new(50.0, 25.0));
        assert_eq!(b.area(), 5000.0);
    }

    #[test]
    fn test_bounds_include_point() {
        let b = Bounds::INVERTED
            .include_point(Vec2::new(10.0, 20.0))
            .include_point(Vec2::new(30.0, 40.0));

        assert_eq!(b.min, Vec2::new(10.0, 20.0));
        assert_eq!(b.max, Vec2::new(30.0, 40.0));
    }

    #[test]
    fn test_bounds_contains() {
        let b = Bounds::new(Vec2::ZERO, Vec2::new(100.0, 100.0));

        assert!(b.contains(Vec2::new(50.0, 50.0)));
        assert!(!b.contains(Vec2::new(150.0, 50.0)));
    }

    #[test]
    fn test_bounds_intersects() {
        let a = Bounds::new(Vec2::ZERO, Vec2::new(100.0, 100.0));
        let b = Bounds::new(Vec2::new(50.0, 50.0), Vec2::new(150.0, 150.0));
        let c = Bounds::new(Vec2::new(200.0, 200.0), Vec2::new(300.0, 300.0));

        assert!(a.intersects(b));
        assert!(!a.intersects(c));
    }

    #[test]
    fn test_bounds_union() {
        let a = Bounds::new(Vec2::ZERO, Vec2::new(100.0, 100.0));
        let b = Bounds::new(Vec2::new(50.0, 50.0), Vec2::new(150.0, 150.0));

        let u = a.union(b);
        assert_eq!(u.min, Vec2::ZERO);
        assert_eq!(u.max, Vec2::new(150.0, 150.0));
    }

    #[test]
    fn test_rect_bounds_conversion() {
        let r = Rect::new(10.0, 20.0, 100.0, 50.0);
        let b = r.to_bounds();
        let r2 = b.to_rect();

        assert!(r.approx_eq(r2));
    }

    #[test]
    fn test_display() {
        let r = Rect::new(10.0, 20.0, 100.0, 50.0);
        assert_eq!(format!("{r}"), "Rect(10, 20, 100x50)");

        let b = Bounds::new(Vec2::new(10.0, 20.0), Vec2::new(100.0, 50.0));
        assert!(format!("{b}").contains("Bounds"));
    }
}
