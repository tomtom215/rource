// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Three-dimensional vector type.

use std::fmt;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::Vec2;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A three-dimensional vector with `x`, `y`, and `z` components.
///
/// Used for 3D positions, colors (RGB), and homogeneous 2D coordinates.
///
/// # Examples
///
/// ```
/// use rource_math::Vec3;
///
/// let a = Vec3::new(1.0, 2.0, 3.0);
/// let b = Vec3::new(4.0, 5.0, 6.0);
///
/// let sum = a + b;
/// let cross = a.cross(b);
/// let dot = a.dot(b);
/// ```
#[derive(Clone, Copy, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[repr(C)]
pub struct Vec3 {
    /// The x component.
    pub x: f32,
    /// The y component.
    pub y: f32,
    /// The z component.
    pub z: f32,
}

impl Vec3 {
    /// A vector with all components set to zero.
    pub const ZERO: Self = Self {
        x: 0.0,
        y: 0.0,
        z: 0.0,
    };

    /// A vector with all components set to one.
    pub const ONE: Self = Self {
        x: 1.0,
        y: 1.0,
        z: 1.0,
    };

    /// A unit vector pointing in the positive X direction.
    pub const X: Self = Self {
        x: 1.0,
        y: 0.0,
        z: 0.0,
    };

    /// A unit vector pointing in the positive Y direction.
    pub const Y: Self = Self {
        x: 0.0,
        y: 1.0,
        z: 0.0,
    };

    /// A unit vector pointing in the positive Z direction.
    pub const Z: Self = Self {
        x: 0.0,
        y: 0.0,
        z: 1.0,
    };

    /// A unit vector pointing in the negative X direction.
    pub const NEG_X: Self = Self {
        x: -1.0,
        y: 0.0,
        z: 0.0,
    };

    /// A unit vector pointing in the negative Y direction.
    pub const NEG_Y: Self = Self {
        x: 0.0,
        y: -1.0,
        z: 0.0,
    };

    /// A unit vector pointing in the negative Z direction.
    pub const NEG_Z: Self = Self {
        x: 0.0,
        y: 0.0,
        z: -1.0,
    };

    /// Creates a new vector with the given components.
    #[inline]
    #[must_use]
    pub const fn new(x: f32, y: f32, z: f32) -> Self {
        Self { x, y, z }
    }

    /// Creates a vector with all components set to the same value.
    #[inline]
    #[must_use]
    pub const fn splat(value: f32) -> Self {
        Self {
            x: value,
            y: value,
            z: value,
        }
    }

    /// Creates a Vec3 from a Vec2 and a z component.
    #[inline]
    #[must_use]
    pub const fn from_vec2(v: Vec2, z: f32) -> Self {
        Self { x: v.x, y: v.y, z }
    }

    /// Returns the xy components as a Vec2.
    #[inline]
    #[must_use]
    pub const fn xy(self) -> Vec2 {
        Vec2 {
            x: self.x,
            y: self.y,
        }
    }

    /// Returns the xz components as a Vec2.
    #[inline]
    #[must_use]
    pub const fn xz(self) -> Vec2 {
        Vec2 {
            x: self.x,
            y: self.z,
        }
    }

    /// Returns the yz components as a Vec2.
    #[inline]
    #[must_use]
    pub const fn yz(self) -> Vec2 {
        Vec2 {
            x: self.y,
            y: self.z,
        }
    }

    /// Returns the dot product of two vectors.
    #[inline]
    #[must_use]
    pub fn dot(self, other: Self) -> f32 {
        self.x * other.x + self.y * other.y + self.z * other.z
    }

    /// Returns the cross product of two vectors.
    ///
    /// The cross product produces a vector perpendicular to both input vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec3;
    ///
    /// let x = Vec3::X;
    /// let y = Vec3::Y;
    /// let z = x.cross(y);
    /// assert!((z.x - Vec3::Z.x).abs() < 1e-6);
    /// assert!((z.y - Vec3::Z.y).abs() < 1e-6);
    /// assert!((z.z - Vec3::Z.z).abs() < 1e-6);
    /// ```
    #[inline]
    #[must_use]
    pub fn cross(self, other: Self) -> Self {
        Self {
            x: self.y * other.z - self.z * other.y,
            y: self.z * other.x - self.x * other.z,
            z: self.x * other.y - self.y * other.x,
        }
    }

    /// Returns the squared length of the vector.
    #[inline]
    #[must_use]
    pub fn length_squared(self) -> f32 {
        self.dot(self)
    }

    /// Returns the length (magnitude) of the vector.
    #[inline]
    #[must_use]
    pub fn length(self) -> f32 {
        self.length_squared().sqrt()
    }

    /// Returns a normalized (unit length) version of this vector.
    ///
    /// Returns [`Vec3::ZERO`] if the vector has zero length.
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
    #[inline]
    pub fn normalize(&mut self) {
        *self = self.normalized();
    }

    /// Returns the distance between two points.
    #[inline]
    #[must_use]
    pub fn distance(self, other: Self) -> f32 {
        (self - other).length()
    }

    /// Returns the squared distance between two points.
    #[inline]
    #[must_use]
    pub fn distance_squared(self, other: Self) -> f32 {
        (self - other).length_squared()
    }

    /// Linearly interpolates between two vectors.
    #[inline]
    #[must_use]
    pub fn lerp(self, other: Self, t: f32) -> Self {
        Self {
            x: crate::lerp(self.x, other.x, t),
            y: crate::lerp(self.y, other.y, t),
            z: crate::lerp(self.z, other.z, t),
        }
    }

    /// Returns a vector with the absolute value of each component.
    #[inline]
    #[must_use]
    pub fn abs(self) -> Self {
        Self {
            x: self.x.abs(),
            y: self.y.abs(),
            z: self.z.abs(),
        }
    }

    /// Returns a vector with each component clamped to the given range.
    #[inline]
    #[must_use]
    pub fn clamp(self, min: Self, max: Self) -> Self {
        Self {
            x: crate::clamp(self.x, min.x, max.x),
            y: crate::clamp(self.y, min.y, max.y),
            z: crate::clamp(self.z, min.z, max.z),
        }
    }

    /// Returns the component-wise minimum of two vectors.
    #[inline]
    #[must_use]
    pub fn min(self, other: Self) -> Self {
        Self {
            x: self.x.min(other.x),
            y: self.y.min(other.y),
            z: self.z.min(other.z),
        }
    }

    /// Returns the component-wise maximum of two vectors.
    #[inline]
    #[must_use]
    pub fn max(self, other: Self) -> Self {
        Self {
            x: self.x.max(other.x),
            y: self.y.max(other.y),
            z: self.z.max(other.z),
        }
    }

    /// Returns the floor of each component.
    #[inline]
    #[must_use]
    pub fn floor(self) -> Self {
        Self {
            x: self.x.floor(),
            y: self.y.floor(),
            z: self.z.floor(),
        }
    }

    /// Returns the ceiling of each component.
    #[inline]
    #[must_use]
    pub fn ceil(self) -> Self {
        Self {
            x: self.x.ceil(),
            y: self.y.ceil(),
            z: self.z.ceil(),
        }
    }

    /// Returns the rounded value of each component.
    #[inline]
    #[must_use]
    pub fn round(self) -> Self {
        Self {
            x: self.x.round(),
            y: self.y.round(),
            z: self.z.round(),
        }
    }

    /// Checks if this vector is approximately equal to another.
    #[inline]
    #[must_use]
    pub fn approx_eq(self, other: Self) -> bool {
        crate::approx_eq(self.x, other.x)
            && crate::approx_eq(self.y, other.y)
            && crate::approx_eq(self.z, other.z)
    }

    /// Reflects this vector off a surface with the given normal.
    #[inline]
    #[must_use]
    pub fn reflect(self, normal: Self) -> Self {
        self - normal * 2.0 * self.dot(normal)
    }

    /// Projects this vector onto another vector.
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

impl Add for Vec3 {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        Self {
            x: self.x + other.x,
            y: self.y + other.y,
            z: self.z + other.z,
        }
    }
}

impl AddAssign for Vec3 {
    #[inline]
    fn add_assign(&mut self, other: Self) {
        self.x += other.x;
        self.y += other.y;
        self.z += other.z;
    }
}

impl Sub for Vec3 {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        Self {
            x: self.x - other.x,
            y: self.y - other.y,
            z: self.z - other.z,
        }
    }
}

impl SubAssign for Vec3 {
    #[inline]
    fn sub_assign(&mut self, other: Self) {
        self.x -= other.x;
        self.y -= other.y;
        self.z -= other.z;
    }
}

impl Mul<f32> for Vec3 {
    type Output = Self;

    #[inline]
    fn mul(self, scalar: f32) -> Self {
        Self {
            x: self.x * scalar,
            y: self.y * scalar,
            z: self.z * scalar,
        }
    }
}

impl Mul<Vec3> for f32 {
    type Output = Vec3;

    #[inline]
    fn mul(self, vec: Vec3) -> Vec3 {
        Vec3 {
            x: self * vec.x,
            y: self * vec.y,
            z: self * vec.z,
        }
    }
}

impl MulAssign<f32> for Vec3 {
    #[inline]
    fn mul_assign(&mut self, scalar: f32) {
        self.x *= scalar;
        self.y *= scalar;
        self.z *= scalar;
    }
}

impl Mul for Vec3 {
    type Output = Self;

    #[inline]
    fn mul(self, other: Self) -> Self {
        Self {
            x: self.x * other.x,
            y: self.y * other.y,
            z: self.z * other.z,
        }
    }
}

/// Divides a `Vec3` by a scalar.
///
/// # Division by Zero
///
/// Division by zero follows IEEE 754 floating-point semantics:
/// - Positive components divided by 0.0 produce positive infinity
/// - Negative components divided by 0.0 produce negative infinity
/// - 0.0 divided by 0.0 produces NaN
///
/// For safe division, check for zero or use a small epsilon threshold.
impl Div<f32> for Vec3 {
    type Output = Self;

    #[inline]
    fn div(self, scalar: f32) -> Self {
        Self {
            x: self.x / scalar,
            y: self.y / scalar,
            z: self.z / scalar,
        }
    }
}

impl DivAssign<f32> for Vec3 {
    #[inline]
    fn div_assign(&mut self, scalar: f32) {
        self.x /= scalar;
        self.y /= scalar;
        self.z /= scalar;
    }
}

impl Div for Vec3 {
    type Output = Self;

    #[inline]
    fn div(self, other: Self) -> Self {
        Self {
            x: self.x / other.x,
            y: self.y / other.y,
            z: self.z / other.z,
        }
    }
}

impl Neg for Vec3 {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self {
            x: -self.x,
            y: -self.y,
            z: -self.z,
        }
    }
}

impl fmt::Debug for Vec3 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Vec3")
            .field("x", &self.x)
            .field("y", &self.y)
            .field("z", &self.z)
            .finish()
    }
}

impl fmt::Display for Vec3 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {}, {})", self.x, self.y, self.z)
    }
}

impl From<(f32, f32, f32)> for Vec3 {
    #[inline]
    fn from((x, y, z): (f32, f32, f32)) -> Self {
        Self { x, y, z }
    }
}

impl From<[f32; 3]> for Vec3 {
    #[inline]
    fn from([x, y, z]: [f32; 3]) -> Self {
        Self { x, y, z }
    }
}

impl From<Vec3> for (f32, f32, f32) {
    #[inline]
    fn from(v: Vec3) -> Self {
        (v.x, v.y, v.z)
    }
}

impl From<Vec3> for [f32; 3] {
    #[inline]
    fn from(v: Vec3) -> Self {
        [v.x, v.y, v.z]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constants() {
        assert_eq!(Vec3::ZERO, Vec3::new(0.0, 0.0, 0.0));
        assert_eq!(Vec3::ONE, Vec3::new(1.0, 1.0, 1.0));
        assert_eq!(Vec3::X, Vec3::new(1.0, 0.0, 0.0));
        assert_eq!(Vec3::Y, Vec3::new(0.0, 1.0, 0.0));
        assert_eq!(Vec3::Z, Vec3::new(0.0, 0.0, 1.0));
    }

    #[test]
    fn test_new_and_splat() {
        let v = Vec3::new(1.0, 2.0, 3.0);
        assert_eq!(v.x, 1.0);
        assert_eq!(v.y, 2.0);
        assert_eq!(v.z, 3.0);

        let s = Vec3::splat(5.0);
        assert_eq!(s.x, 5.0);
        assert_eq!(s.y, 5.0);
        assert_eq!(s.z, 5.0);
    }

    #[test]
    fn test_from_vec2() {
        let v2 = Vec2::new(1.0, 2.0);
        let v3 = Vec3::from_vec2(v2, 3.0);
        assert_eq!(v3, Vec3::new(1.0, 2.0, 3.0));
    }

    #[test]
    fn test_swizzle() {
        let v = Vec3::new(1.0, 2.0, 3.0);
        assert_eq!(v.xy(), Vec2::new(1.0, 2.0));
        assert_eq!(v.xz(), Vec2::new(1.0, 3.0));
        assert_eq!(v.yz(), Vec2::new(2.0, 3.0));
    }

    #[test]
    fn test_dot() {
        assert_eq!(Vec3::X.dot(Vec3::Y), 0.0);
        assert_eq!(Vec3::X.dot(Vec3::X), 1.0);
        assert_eq!(Vec3::new(1.0, 2.0, 3.0).dot(Vec3::new(4.0, 5.0, 6.0)), 32.0);
    }

    #[test]
    fn test_cross() {
        let z = Vec3::X.cross(Vec3::Y);
        assert!(z.approx_eq(Vec3::Z));

        let x = Vec3::Y.cross(Vec3::Z);
        assert!(x.approx_eq(Vec3::X));

        let y = Vec3::Z.cross(Vec3::X);
        assert!(y.approx_eq(Vec3::Y));
    }

    #[test]
    fn test_length() {
        assert_eq!(Vec3::new(2.0, 3.0, 6.0).length(), 7.0);
        assert_eq!(Vec3::new(2.0, 3.0, 6.0).length_squared(), 49.0);
        assert_eq!(Vec3::ZERO.length(), 0.0);
        assert_eq!(Vec3::X.length(), 1.0);
    }

    #[test]
    fn test_normalized() {
        let v = Vec3::new(2.0, 3.0, 6.0).normalized();
        assert!((v.length() - 1.0).abs() < 1e-6);

        // Zero vector stays zero
        assert_eq!(Vec3::ZERO.normalized(), Vec3::ZERO);
    }

    #[test]
    fn test_distance() {
        let a = Vec3::ZERO;
        let b = Vec3::new(2.0, 3.0, 6.0);
        assert_eq!(a.distance(b), 7.0);
        assert_eq!(a.distance_squared(b), 49.0);
    }

    #[test]
    fn test_lerp() {
        let a = Vec3::ZERO;
        let b = Vec3::new(10.0, 20.0, 30.0);

        assert_eq!(a.lerp(b, 0.0), a);
        assert_eq!(a.lerp(b, 1.0), b);
        assert_eq!(a.lerp(b, 0.5), Vec3::new(5.0, 10.0, 15.0));
    }

    #[test]
    fn test_abs() {
        assert_eq!(Vec3::new(-1.0, 2.0, -3.0).abs(), Vec3::new(1.0, 2.0, 3.0));
    }

    #[test]
    fn test_clamp() {
        let v = Vec3::new(-5.0, 5.0, 15.0);
        let clamped = v.clamp(Vec3::ZERO, Vec3::splat(10.0));
        assert_eq!(clamped, Vec3::new(0.0, 5.0, 10.0));
    }

    #[test]
    fn test_min_max() {
        let a = Vec3::new(1.0, 4.0, 2.0);
        let b = Vec3::new(3.0, 2.0, 5.0);

        assert_eq!(a.min(b), Vec3::new(1.0, 2.0, 2.0));
        assert_eq!(a.max(b), Vec3::new(3.0, 4.0, 5.0));
    }

    #[test]
    fn test_floor_ceil_round() {
        let v = Vec3::new(1.5, 2.7, -0.3);
        assert_eq!(v.floor(), Vec3::new(1.0, 2.0, -1.0));
        assert_eq!(v.ceil(), Vec3::new(2.0, 3.0, 0.0));
        assert_eq!(v.round(), Vec3::new(2.0, 3.0, 0.0));
    }

    #[test]
    fn test_reflect() {
        let v = Vec3::new(1.0, -1.0, 0.0);
        let normal = Vec3::new(0.0, 1.0, 0.0);
        let reflected = v.reflect(normal);
        assert!(reflected.approx_eq(Vec3::new(1.0, 1.0, 0.0)));
    }

    #[test]
    fn test_project() {
        let v = Vec3::new(3.0, 4.0, 5.0);
        let onto = Vec3::X;
        let projected = v.project(onto);
        assert_eq!(projected, Vec3::new(3.0, 0.0, 0.0));
    }

    #[test]
    fn test_operators() {
        let a = Vec3::new(1.0, 2.0, 3.0);
        let b = Vec3::new(4.0, 5.0, 6.0);

        assert_eq!(a + b, Vec3::new(5.0, 7.0, 9.0));
        assert_eq!(a - b, Vec3::new(-3.0, -3.0, -3.0));
        assert_eq!(a * 2.0, Vec3::new(2.0, 4.0, 6.0));
        assert_eq!(2.0 * a, Vec3::new(2.0, 4.0, 6.0));
        assert_eq!(a / 2.0, Vec3::new(0.5, 1.0, 1.5));
        assert_eq!(-a, Vec3::new(-1.0, -2.0, -3.0));
        assert_eq!(a * b, Vec3::new(4.0, 10.0, 18.0));
    }

    #[test]
    fn test_conversions() {
        let v = Vec3::new(1.0, 2.0, 3.0);

        let tuple: (f32, f32, f32) = v.into();
        assert_eq!(tuple, (1.0, 2.0, 3.0));

        let array: [f32; 3] = v.into();
        assert_eq!(array, [1.0, 2.0, 3.0]);

        assert_eq!(Vec3::from((1.0, 2.0, 3.0)), v);
        assert_eq!(Vec3::from([1.0, 2.0, 3.0]), v);
    }

    #[test]
    fn test_display_debug() {
        let v = Vec3::new(1.0, 2.0, 3.0);
        assert_eq!(format!("{v}"), "(1, 2, 3)");
        assert_eq!(format!("{v:?}"), "Vec3 { x: 1.0, y: 2.0, z: 3.0 }");
    }
}
