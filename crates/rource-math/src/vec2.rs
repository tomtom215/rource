// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Two-dimensional vector type.

use std::fmt;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A two-dimensional vector with `x` and `y` components.
///
/// This is the primary 2D type used throughout Rource for positions,
/// velocities, directions, and sizes.
///
/// # Examples
///
/// ```
/// use rource_math::Vec2;
///
/// let a = Vec2::new(3.0, 4.0);
/// let b = Vec2::new(1.0, 2.0);
///
/// // Vector operations
/// let sum = a + b;
/// let diff = a - b;
/// let scaled = a * 2.0;
///
/// // Geometric operations
/// let length = a.length();
/// let normalized = a.normalized();
/// let dot = a.dot(b);
/// ```
#[derive(Clone, Copy, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[repr(C)]
pub struct Vec2 {
    /// The x component.
    pub x: f32,
    /// The y component.
    pub y: f32,
}

impl Vec2 {
    /// A vector with all components set to zero.
    pub const ZERO: Self = Self { x: 0.0, y: 0.0 };

    /// A vector with all components set to one.
    pub const ONE: Self = Self { x: 1.0, y: 1.0 };

    /// A unit vector pointing in the positive X direction.
    pub const X: Self = Self { x: 1.0, y: 0.0 };

    /// A unit vector pointing in the positive Y direction.
    pub const Y: Self = Self { x: 0.0, y: 1.0 };

    /// A unit vector pointing in the negative X direction.
    pub const NEG_X: Self = Self { x: -1.0, y: 0.0 };

    /// A unit vector pointing in the negative Y direction.
    pub const NEG_Y: Self = Self { x: 0.0, y: -1.0 };

    /// Creates a new vector with the given components.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let v = Vec2::new(1.0, 2.0);
    /// assert_eq!(v.x, 1.0);
    /// assert_eq!(v.y, 2.0);
    /// ```
    #[inline]
    #[must_use]
    pub const fn new(x: f32, y: f32) -> Self {
        Self { x, y }
    }

    /// Creates a vector with both components set to the same value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let v = Vec2::splat(5.0);
    /// assert_eq!(v.x, 5.0);
    /// assert_eq!(v.y, 5.0);
    /// ```
    #[inline]
    #[must_use]
    pub const fn splat(value: f32) -> Self {
        Self { x: value, y: value }
    }

    /// Creates a unit vector from an angle in radians.
    ///
    /// The angle is measured counter-clockwise from the positive X axis.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::{Vec2, PI};
    ///
    /// let v = Vec2::from_angle(0.0);
    /// assert!((v.x - 1.0).abs() < 1e-6);
    /// assert!(v.y.abs() < 1e-6);
    ///
    /// let v = Vec2::from_angle(PI / 2.0);
    /// assert!(v.x.abs() < 1e-6);
    /// assert!((v.y - 1.0).abs() < 1e-6);
    /// ```
    #[inline]
    #[must_use]
    pub fn from_angle(radians: f32) -> Self {
        Self {
            x: radians.cos(),
            y: radians.sin(),
        }
    }

    /// Returns the angle of this vector in radians.
    ///
    /// The angle is measured counter-clockwise from the positive X axis,
    /// in the range `(-PI, PI]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::{Vec2, PI};
    ///
    /// let v = Vec2::new(1.0, 0.0);
    /// assert!(v.angle().abs() < 1e-6);
    ///
    /// let v = Vec2::new(0.0, 1.0);
    /// assert!((v.angle() - PI / 2.0).abs() < 1e-6);
    /// ```
    #[inline]
    #[must_use]
    pub fn angle(self) -> f32 {
        self.y.atan2(self.x)
    }

    /// Returns the dot product of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let a = Vec2::new(1.0, 2.0);
    /// let b = Vec2::new(3.0, 4.0);
    /// assert_eq!(a.dot(b), 11.0); // 1*3 + 2*4 = 11
    /// ```
    #[inline]
    #[must_use]
    pub fn dot(self, other: Self) -> f32 {
        self.x * other.x + self.y * other.y
    }

    /// Returns the "cross product" (perp dot product) of two 2D vectors.
    ///
    /// This returns the z-component of the 3D cross product if the vectors
    /// were extended to 3D with z=0. It's useful for determining the signed
    /// area of the parallelogram formed by the two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let a = Vec2::new(1.0, 0.0);
    /// let b = Vec2::new(0.0, 1.0);
    /// assert_eq!(a.cross(b), 1.0);  // Positive (counter-clockwise)
    /// assert_eq!(b.cross(a), -1.0); // Negative (clockwise)
    /// ```
    #[inline]
    #[must_use]
    pub fn cross(self, other: Self) -> f32 {
        self.x * other.y - self.y * other.x
    }

    /// Returns the squared length of the vector.
    ///
    /// This is more efficient than [`length`](Self::length) when you only need
    /// to compare lengths, as it avoids the square root.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let v = Vec2::new(3.0, 4.0);
    /// assert_eq!(v.length_squared(), 25.0);
    /// ```
    #[inline]
    #[must_use]
    pub fn length_squared(self) -> f32 {
        self.dot(self)
    }

    /// Returns the length (magnitude) of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let v = Vec2::new(3.0, 4.0);
    /// assert_eq!(v.length(), 5.0);
    /// ```
    #[inline]
    #[must_use]
    pub fn length(self) -> f32 {
        self.length_squared().sqrt()
    }

    /// Returns a normalized (unit length) version of this vector.
    ///
    /// Returns [`Vec2::ZERO`] if the vector has zero length.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let v = Vec2::new(3.0, 4.0);
    /// let n = v.normalized();
    /// assert!((n.length() - 1.0).abs() < 1e-6);
    /// ```
    #[inline]
    #[must_use]
    pub fn normalized(self) -> Self {
        let len = self.length();
        if len > 0.0 {
            self / len
        } else {
            Self::ZERO
        }
    }

    /// Normalizes the vector in place.
    ///
    /// If the vector has zero length, it remains unchanged.
    #[inline]
    pub fn normalize(&mut self) {
        *self = self.normalized();
    }

    /// Returns the distance between two points.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let a = Vec2::new(0.0, 0.0);
    /// let b = Vec2::new(3.0, 4.0);
    /// assert_eq!(a.distance(b), 5.0);
    /// ```
    #[inline]
    #[must_use]
    pub fn distance(self, other: Self) -> f32 {
        (self - other).length()
    }

    /// Returns the squared distance between two points.
    ///
    /// More efficient than [`distance`](Self::distance) when only comparing distances.
    #[inline]
    #[must_use]
    pub fn distance_squared(self, other: Self) -> f32 {
        (self - other).length_squared()
    }

    /// Linearly interpolates between two vectors.
    ///
    /// # Arguments
    ///
    /// * `other` - The target vector
    /// * `t` - Interpolation factor (0.0 = self, 1.0 = other)
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let a = Vec2::new(0.0, 0.0);
    /// let b = Vec2::new(10.0, 20.0);
    ///
    /// assert_eq!(a.lerp(b, 0.0), a);
    /// assert_eq!(a.lerp(b, 1.0), b);
    /// assert_eq!(a.lerp(b, 0.5), Vec2::new(5.0, 10.0));
    /// ```
    #[inline]
    #[must_use]
    pub fn lerp(self, other: Self, t: f32) -> Self {
        Self {
            x: crate::lerp(self.x, other.x, t),
            y: crate::lerp(self.y, other.y, t),
        }
    }

    /// Returns a vector with the absolute value of each component.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let v = Vec2::new(-3.0, 4.0);
    /// assert_eq!(v.abs(), Vec2::new(3.0, 4.0));
    /// ```
    #[inline]
    #[must_use]
    pub fn abs(self) -> Self {
        Self {
            x: self.x.abs(),
            y: self.y.abs(),
        }
    }

    /// Returns a vector with each component clamped to the given range.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let v = Vec2::new(-5.0, 15.0);
    /// let clamped = v.clamp(Vec2::ZERO, Vec2::new(10.0, 10.0));
    /// assert_eq!(clamped, Vec2::new(0.0, 10.0));
    /// ```
    #[inline]
    #[must_use]
    pub fn clamp(self, min: Self, max: Self) -> Self {
        Self {
            x: crate::clamp(self.x, min.x, max.x),
            y: crate::clamp(self.y, min.y, max.y),
        }
    }

    /// Returns the component-wise minimum of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let a = Vec2::new(1.0, 4.0);
    /// let b = Vec2::new(3.0, 2.0);
    /// assert_eq!(a.min(b), Vec2::new(1.0, 2.0));
    /// ```
    #[inline]
    #[must_use]
    pub fn min(self, other: Self) -> Self {
        Self {
            x: self.x.min(other.x),
            y: self.y.min(other.y),
        }
    }

    /// Returns the component-wise maximum of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let a = Vec2::new(1.0, 4.0);
    /// let b = Vec2::new(3.0, 2.0);
    /// assert_eq!(a.max(b), Vec2::new(3.0, 4.0));
    /// ```
    #[inline]
    #[must_use]
    pub fn max(self, other: Self) -> Self {
        Self {
            x: self.x.max(other.x),
            y: self.y.max(other.y),
        }
    }

    /// Returns a vector perpendicular to this one.
    ///
    /// The result is rotated 90 degrees counter-clockwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let v = Vec2::new(1.0, 0.0);
    /// assert_eq!(v.perp(), Vec2::new(0.0, 1.0));
    /// ```
    #[inline]
    #[must_use]
    pub fn perp(self) -> Self {
        Self {
            x: -self.y,
            y: self.x,
        }
    }

    /// Rotates the vector by the given angle in radians.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::{Vec2, PI};
    ///
    /// let v = Vec2::new(1.0, 0.0);
    /// let rotated = v.rotate(PI / 2.0);
    /// assert!(rotated.x.abs() < 1e-6);
    /// assert!((rotated.y - 1.0).abs() < 1e-6);
    /// ```
    #[inline]
    #[must_use]
    pub fn rotate(self, radians: f32) -> Self {
        let cos = radians.cos();
        let sin = radians.sin();
        Self {
            x: self.x * cos - self.y * sin,
            y: self.x * sin + self.y * cos,
        }
    }

    /// Returns the floor of each component.
    #[inline]
    #[must_use]
    pub fn floor(self) -> Self {
        Self {
            x: self.x.floor(),
            y: self.y.floor(),
        }
    }

    /// Returns the ceiling of each component.
    #[inline]
    #[must_use]
    pub fn ceil(self) -> Self {
        Self {
            x: self.x.ceil(),
            y: self.y.ceil(),
        }
    }

    /// Returns the rounded value of each component.
    #[inline]
    #[must_use]
    pub fn round(self) -> Self {
        Self {
            x: self.x.round(),
            y: self.y.round(),
        }
    }

    /// Checks if this vector is approximately equal to another.
    #[inline]
    #[must_use]
    pub fn approx_eq(self, other: Self) -> bool {
        crate::approx_eq(self.x, other.x) && crate::approx_eq(self.y, other.y)
    }

    /// Reflects this vector off a surface with the given normal.
    ///
    /// # Arguments
    ///
    /// * `normal` - The surface normal (should be normalized)
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let v = Vec2::new(1.0, -1.0);
    /// let normal = Vec2::new(0.0, 1.0);
    /// let reflected = v.reflect(normal);
    /// assert!((reflected.x - 1.0).abs() < 1e-6);
    /// assert!((reflected.y - 1.0).abs() < 1e-6);
    /// ```
    #[inline]
    #[must_use]
    pub fn reflect(self, normal: Self) -> Self {
        self - normal * 2.0 * self.dot(normal)
    }

    /// Projects this vector onto another vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let v = Vec2::new(3.0, 4.0);
    /// let onto = Vec2::new(1.0, 0.0);
    /// let projected = v.project(onto);
    /// assert_eq!(projected, Vec2::new(3.0, 0.0));
    /// ```
    #[inline]
    #[must_use]
    pub fn project(self, onto: Self) -> Self {
        let onto_len_sq = onto.length_squared();
        if onto_len_sq > 0.0 {
            onto * (self.dot(onto) / onto_len_sq)
        } else {
            Self::ZERO
        }
    }
}

// Operator implementations

impl Add for Vec2 {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        Self {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

impl AddAssign for Vec2 {
    #[inline]
    fn add_assign(&mut self, other: Self) {
        self.x += other.x;
        self.y += other.y;
    }
}

impl Sub for Vec2 {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        Self {
            x: self.x - other.x,
            y: self.y - other.y,
        }
    }
}

impl SubAssign for Vec2 {
    #[inline]
    fn sub_assign(&mut self, other: Self) {
        self.x -= other.x;
        self.y -= other.y;
    }
}

impl Mul<f32> for Vec2 {
    type Output = Self;

    #[inline]
    fn mul(self, scalar: f32) -> Self {
        Self {
            x: self.x * scalar,
            y: self.y * scalar,
        }
    }
}

impl Mul<Vec2> for f32 {
    type Output = Vec2;

    #[inline]
    fn mul(self, vec: Vec2) -> Vec2 {
        Vec2 {
            x: self * vec.x,
            y: self * vec.y,
        }
    }
}

impl MulAssign<f32> for Vec2 {
    #[inline]
    fn mul_assign(&mut self, scalar: f32) {
        self.x *= scalar;
        self.y *= scalar;
    }
}

impl Mul for Vec2 {
    type Output = Self;

    #[inline]
    fn mul(self, other: Self) -> Self {
        Self {
            x: self.x * other.x,
            y: self.y * other.y,
        }
    }
}

impl MulAssign for Vec2 {
    #[inline]
    fn mul_assign(&mut self, other: Self) {
        self.x *= other.x;
        self.y *= other.y;
    }
}

/// Divides a `Vec2` by a scalar.
///
/// # Division by Zero
///
/// Division by zero follows IEEE 754 floating-point semantics:
/// - Positive components divided by 0.0 produce positive infinity
/// - Negative components divided by 0.0 produce negative infinity
/// - 0.0 divided by 0.0 produces NaN
///
/// For safe division, check for zero or use a small epsilon threshold.
impl Div<f32> for Vec2 {
    type Output = Self;

    #[inline]
    fn div(self, scalar: f32) -> Self {
        Self {
            x: self.x / scalar,
            y: self.y / scalar,
        }
    }
}

impl DivAssign<f32> for Vec2 {
    #[inline]
    fn div_assign(&mut self, scalar: f32) {
        self.x /= scalar;
        self.y /= scalar;
    }
}

impl Div for Vec2 {
    type Output = Self;

    #[inline]
    fn div(self, other: Self) -> Self {
        Self {
            x: self.x / other.x,
            y: self.y / other.y,
        }
    }
}

impl Neg for Vec2 {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self {
            x: -self.x,
            y: -self.y,
        }
    }
}

impl fmt::Debug for Vec2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Vec2")
            .field("x", &self.x)
            .field("y", &self.y)
            .finish()
    }
}

impl fmt::Display for Vec2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.x, self.y)
    }
}

impl From<(f32, f32)> for Vec2 {
    #[inline]
    fn from((x, y): (f32, f32)) -> Self {
        Self { x, y }
    }
}

impl From<[f32; 2]> for Vec2 {
    #[inline]
    fn from([x, y]: [f32; 2]) -> Self {
        Self { x, y }
    }
}

impl From<Vec2> for (f32, f32) {
    #[inline]
    fn from(v: Vec2) -> Self {
        (v.x, v.y)
    }
}

impl From<Vec2> for [f32; 2] {
    #[inline]
    fn from(v: Vec2) -> Self {
        [v.x, v.y]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PI;

    #[test]
    fn test_constants() {
        assert_eq!(Vec2::ZERO, Vec2::new(0.0, 0.0));
        assert_eq!(Vec2::ONE, Vec2::new(1.0, 1.0));
        assert_eq!(Vec2::X, Vec2::new(1.0, 0.0));
        assert_eq!(Vec2::Y, Vec2::new(0.0, 1.0));
    }

    #[test]
    fn test_new_and_splat() {
        let v = Vec2::new(1.0, 2.0);
        assert_eq!(v.x, 1.0);
        assert_eq!(v.y, 2.0);

        let s = Vec2::splat(5.0);
        assert_eq!(s.x, 5.0);
        assert_eq!(s.y, 5.0);
    }

    #[test]
    fn test_from_angle() {
        let v = Vec2::from_angle(0.0);
        assert!(v.approx_eq(Vec2::X));

        let v = Vec2::from_angle(PI / 2.0);
        assert!(v.approx_eq(Vec2::Y));

        let v = Vec2::from_angle(PI);
        assert!(v.approx_eq(Vec2::NEG_X));

        let v = Vec2::from_angle(-PI / 2.0);
        assert!(v.approx_eq(Vec2::NEG_Y));
    }

    #[test]
    fn test_angle() {
        assert!(Vec2::X.angle().abs() < 1e-6);
        assert!((Vec2::Y.angle() - PI / 2.0).abs() < 1e-6);
        assert!((Vec2::NEG_X.angle().abs() - PI).abs() < 1e-6);
        assert!((Vec2::NEG_Y.angle() + PI / 2.0).abs() < 1e-6);
    }

    #[test]
    fn test_dot() {
        assert_eq!(Vec2::X.dot(Vec2::Y), 0.0);
        assert_eq!(Vec2::X.dot(Vec2::X), 1.0);
        assert_eq!(Vec2::new(1.0, 2.0).dot(Vec2::new(3.0, 4.0)), 11.0);
    }

    #[test]
    fn test_cross() {
        assert_eq!(Vec2::X.cross(Vec2::Y), 1.0);
        assert_eq!(Vec2::Y.cross(Vec2::X), -1.0);
        assert_eq!(Vec2::X.cross(Vec2::X), 0.0);
    }

    #[test]
    fn test_length() {
        assert_eq!(Vec2::new(3.0, 4.0).length(), 5.0);
        assert_eq!(Vec2::new(3.0, 4.0).length_squared(), 25.0);
        assert_eq!(Vec2::ZERO.length(), 0.0);
        assert_eq!(Vec2::X.length(), 1.0);
    }

    #[test]
    fn test_normalized() {
        let v = Vec2::new(3.0, 4.0).normalized();
        assert!((v.length() - 1.0).abs() < 1e-6);
        assert!((v.x - 0.6).abs() < 1e-6);
        assert!((v.y - 0.8).abs() < 1e-6);

        // Zero vector stays zero
        assert_eq!(Vec2::ZERO.normalized(), Vec2::ZERO);
    }

    #[test]
    fn test_distance() {
        let a = Vec2::new(0.0, 0.0);
        let b = Vec2::new(3.0, 4.0);
        assert_eq!(a.distance(b), 5.0);
        assert_eq!(a.distance_squared(b), 25.0);
    }

    #[test]
    fn test_lerp() {
        let a = Vec2::new(0.0, 0.0);
        let b = Vec2::new(10.0, 20.0);

        assert_eq!(a.lerp(b, 0.0), a);
        assert_eq!(a.lerp(b, 1.0), b);
        assert_eq!(a.lerp(b, 0.5), Vec2::new(5.0, 10.0));
    }

    #[test]
    fn test_abs() {
        assert_eq!(Vec2::new(-3.0, 4.0).abs(), Vec2::new(3.0, 4.0));
        assert_eq!(Vec2::new(3.0, -4.0).abs(), Vec2::new(3.0, 4.0));
        assert_eq!(Vec2::new(-3.0, -4.0).abs(), Vec2::new(3.0, 4.0));
    }

    #[test]
    fn test_clamp() {
        let v = Vec2::new(-5.0, 15.0);
        let clamped = v.clamp(Vec2::ZERO, Vec2::new(10.0, 10.0));
        assert_eq!(clamped, Vec2::new(0.0, 10.0));
    }

    #[test]
    fn test_min_max() {
        let a = Vec2::new(1.0, 4.0);
        let b = Vec2::new(3.0, 2.0);

        assert_eq!(a.min(b), Vec2::new(1.0, 2.0));
        assert_eq!(a.max(b), Vec2::new(3.0, 4.0));
    }

    #[test]
    fn test_perp() {
        assert_eq!(Vec2::X.perp(), Vec2::Y);
        assert_eq!(Vec2::Y.perp(), Vec2::NEG_X);
    }

    #[test]
    fn test_rotate() {
        let v = Vec2::X;

        let rotated = v.rotate(PI / 2.0);
        assert!(rotated.approx_eq(Vec2::Y));

        let rotated = v.rotate(PI);
        assert!(rotated.approx_eq(Vec2::NEG_X));

        let rotated = v.rotate(2.0 * PI);
        assert!(rotated.approx_eq(Vec2::X));
    }

    #[test]
    fn test_floor_ceil_round() {
        let v = Vec2::new(1.5, 2.7);
        assert_eq!(v.floor(), Vec2::new(1.0, 2.0));
        assert_eq!(v.ceil(), Vec2::new(2.0, 3.0));
        assert_eq!(v.round(), Vec2::new(2.0, 3.0));
    }

    #[test]
    fn test_reflect() {
        let v = Vec2::new(1.0, -1.0);
        let normal = Vec2::new(0.0, 1.0);
        let reflected = v.reflect(normal);
        assert!(reflected.approx_eq(Vec2::new(1.0, 1.0)));
    }

    #[test]
    fn test_project() {
        let v = Vec2::new(3.0, 4.0);
        let onto = Vec2::new(1.0, 0.0);
        let projected = v.project(onto);
        assert_eq!(projected, Vec2::new(3.0, 0.0));

        // Project onto zero vector
        assert_eq!(v.project(Vec2::ZERO), Vec2::ZERO);
    }

    #[test]
    fn test_operators() {
        let a = Vec2::new(1.0, 2.0);
        let b = Vec2::new(3.0, 4.0);

        assert_eq!(a + b, Vec2::new(4.0, 6.0));
        assert_eq!(a - b, Vec2::new(-2.0, -2.0));
        assert_eq!(a * 2.0, Vec2::new(2.0, 4.0));
        assert_eq!(2.0 * a, Vec2::new(2.0, 4.0));
        assert_eq!(a / 2.0, Vec2::new(0.5, 1.0));
        assert_eq!(-a, Vec2::new(-1.0, -2.0));
        assert_eq!(a * b, Vec2::new(3.0, 8.0));
        assert_eq!(a / b, Vec2::new(1.0 / 3.0, 0.5));
    }

    #[test]
    fn test_assign_operators() {
        let mut v = Vec2::new(1.0, 2.0);

        v += Vec2::new(1.0, 1.0);
        assert_eq!(v, Vec2::new(2.0, 3.0));

        v -= Vec2::new(1.0, 1.0);
        assert_eq!(v, Vec2::new(1.0, 2.0));

        v *= 2.0;
        assert_eq!(v, Vec2::new(2.0, 4.0));

        v /= 2.0;
        assert_eq!(v, Vec2::new(1.0, 2.0));

        v *= Vec2::new(2.0, 3.0);
        assert_eq!(v, Vec2::new(2.0, 6.0));
    }

    #[test]
    fn test_conversions() {
        let v = Vec2::new(1.0, 2.0);

        let tuple: (f32, f32) = v.into();
        assert_eq!(tuple, (1.0, 2.0));

        let array: [f32; 2] = v.into();
        assert_eq!(array, [1.0, 2.0]);

        assert_eq!(Vec2::from((1.0, 2.0)), v);
        assert_eq!(Vec2::from([1.0, 2.0]), v);
    }

    #[test]
    fn test_display_debug() {
        let v = Vec2::new(1.0, 2.0);
        assert_eq!(format!("{v}"), "(1, 2)");
        assert_eq!(format!("{v:?}"), "Vec2 { x: 1.0, y: 2.0 }");
    }

    #[test]
    fn test_default() {
        assert_eq!(Vec2::default(), Vec2::ZERO);
    }

    #[test]
    fn test_normalize_in_place() {
        let mut v = Vec2::new(3.0, 4.0);
        v.normalize();
        assert!((v.length() - 1.0).abs() < 1e-6);
    }
}
