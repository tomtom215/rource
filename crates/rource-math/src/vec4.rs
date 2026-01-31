// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Four-dimensional vector type.

use std::fmt;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::{Vec2, Vec3};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A four-dimensional vector with `x`, `y`, `z`, and `w` components.
///
/// Used for homogeneous coordinates, RGBA colors, and quaternion representation.
///
/// # Examples
///
/// ```
/// use rource_math::Vec4;
///
/// let v = Vec4::new(1.0, 2.0, 3.0, 4.0);
/// assert_eq!(v.x, 1.0);
/// assert_eq!(v.w, 4.0);
/// ```
#[derive(Clone, Copy, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[repr(C)]
pub struct Vec4 {
    /// The x component.
    pub x: f32,
    /// The y component.
    pub y: f32,
    /// The z component.
    pub z: f32,
    /// The w component.
    pub w: f32,
}

impl Vec4 {
    /// A vector with all components set to zero.
    pub const ZERO: Self = Self {
        x: 0.0,
        y: 0.0,
        z: 0.0,
        w: 0.0,
    };

    /// A vector with all components set to one.
    pub const ONE: Self = Self {
        x: 1.0,
        y: 1.0,
        z: 1.0,
        w: 1.0,
    };

    /// A unit vector in the X direction.
    pub const X: Self = Self {
        x: 1.0,
        y: 0.0,
        z: 0.0,
        w: 0.0,
    };

    /// A unit vector in the Y direction.
    pub const Y: Self = Self {
        x: 0.0,
        y: 1.0,
        z: 0.0,
        w: 0.0,
    };

    /// A unit vector in the Z direction.
    pub const Z: Self = Self {
        x: 0.0,
        y: 0.0,
        z: 1.0,
        w: 0.0,
    };

    /// A unit vector in the W direction.
    pub const W: Self = Self {
        x: 0.0,
        y: 0.0,
        z: 0.0,
        w: 1.0,
    };

    /// Creates a new vector with the given components.
    #[inline]
    #[must_use]
    pub const fn new(x: f32, y: f32, z: f32, w: f32) -> Self {
        Self { x, y, z, w }
    }

    /// Creates a vector with all components set to the same value.
    #[inline]
    #[must_use]
    pub const fn splat(value: f32) -> Self {
        Self {
            x: value,
            y: value,
            z: value,
            w: value,
        }
    }

    /// Creates a Vec4 from a Vec3 and a w component.
    #[inline]
    #[must_use]
    pub const fn from_vec3(v: Vec3, w: f32) -> Self {
        Self {
            x: v.x,
            y: v.y,
            z: v.z,
            w,
        }
    }

    /// Creates a Vec4 from a Vec2 and z, w components.
    #[inline]
    #[must_use]
    pub const fn from_vec2(v: Vec2, z: f32, w: f32) -> Self {
        Self {
            x: v.x,
            y: v.y,
            z,
            w,
        }
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

    /// Returns the xyz components as a Vec3.
    #[inline]
    #[must_use]
    pub const fn xyz(self) -> Vec3 {
        Vec3 {
            x: self.x,
            y: self.y,
            z: self.z,
        }
    }

    /// Returns the dot product of two vectors.
    #[inline]
    #[must_use]
    pub fn dot(self, other: Self) -> f32 {
        self.x * other.x + self.y * other.y + self.z * other.z + self.w * other.w
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

    /// Linearly interpolates between two vectors.
    #[inline]
    #[must_use]
    pub fn lerp(self, other: Self, t: f32) -> Self {
        Self {
            x: crate::lerp(self.x, other.x, t),
            y: crate::lerp(self.y, other.y, t),
            z: crate::lerp(self.z, other.z, t),
            w: crate::lerp(self.w, other.w, t),
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
            w: self.w.abs(),
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
            w: crate::clamp(self.w, min.w, max.w),
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
            w: self.w.min(other.w),
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
            w: self.w.max(other.w),
        }
    }

    /// Checks if this vector is approximately equal to another.
    #[inline]
    #[must_use]
    pub fn approx_eq(self, other: Self) -> bool {
        crate::approx_eq(self.x, other.x)
            && crate::approx_eq(self.y, other.y)
            && crate::approx_eq(self.z, other.z)
            && crate::approx_eq(self.w, other.w)
    }
}

// Operator implementations

impl Add for Vec4 {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        Self {
            x: self.x + other.x,
            y: self.y + other.y,
            z: self.z + other.z,
            w: self.w + other.w,
        }
    }
}

impl AddAssign for Vec4 {
    #[inline]
    fn add_assign(&mut self, other: Self) {
        self.x += other.x;
        self.y += other.y;
        self.z += other.z;
        self.w += other.w;
    }
}

impl Sub for Vec4 {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        Self {
            x: self.x - other.x,
            y: self.y - other.y,
            z: self.z - other.z,
            w: self.w - other.w,
        }
    }
}

impl SubAssign for Vec4 {
    #[inline]
    fn sub_assign(&mut self, other: Self) {
        self.x -= other.x;
        self.y -= other.y;
        self.z -= other.z;
        self.w -= other.w;
    }
}

impl Mul<f32> for Vec4 {
    type Output = Self;

    #[inline]
    fn mul(self, scalar: f32) -> Self {
        Self {
            x: self.x * scalar,
            y: self.y * scalar,
            z: self.z * scalar,
            w: self.w * scalar,
        }
    }
}

impl Mul<Vec4> for f32 {
    type Output = Vec4;

    #[inline]
    fn mul(self, vec: Vec4) -> Vec4 {
        Vec4 {
            x: self * vec.x,
            y: self * vec.y,
            z: self * vec.z,
            w: self * vec.w,
        }
    }
}

impl MulAssign<f32> for Vec4 {
    #[inline]
    fn mul_assign(&mut self, scalar: f32) {
        self.x *= scalar;
        self.y *= scalar;
        self.z *= scalar;
        self.w *= scalar;
    }
}

impl Mul for Vec4 {
    type Output = Self;

    #[inline]
    fn mul(self, other: Self) -> Self {
        Self {
            x: self.x * other.x,
            y: self.y * other.y,
            z: self.z * other.z,
            w: self.w * other.w,
        }
    }
}

/// Divides a `Vec4` by a scalar.
///
/// # Division by Zero
///
/// Division by zero follows IEEE 754 floating-point semantics:
/// - Positive components divided by 0.0 produce positive infinity
/// - Negative components divided by 0.0 produce negative infinity
/// - 0.0 divided by 0.0 produces NaN
///
/// For safe division, check for zero or use a small epsilon threshold.
impl Div<f32> for Vec4 {
    type Output = Self;

    #[inline]
    fn div(self, scalar: f32) -> Self {
        Self {
            x: self.x / scalar,
            y: self.y / scalar,
            z: self.z / scalar,
            w: self.w / scalar,
        }
    }
}

impl DivAssign<f32> for Vec4 {
    #[inline]
    fn div_assign(&mut self, scalar: f32) {
        self.x /= scalar;
        self.y /= scalar;
        self.z /= scalar;
        self.w /= scalar;
    }
}

impl Neg for Vec4 {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self {
            x: -self.x,
            y: -self.y,
            z: -self.z,
            w: -self.w,
        }
    }
}

impl fmt::Debug for Vec4 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Vec4")
            .field("x", &self.x)
            .field("y", &self.y)
            .field("z", &self.z)
            .field("w", &self.w)
            .finish()
    }
}

impl fmt::Display for Vec4 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {}, {}, {})", self.x, self.y, self.z, self.w)
    }
}

impl From<(f32, f32, f32, f32)> for Vec4 {
    #[inline]
    fn from((x, y, z, w): (f32, f32, f32, f32)) -> Self {
        Self { x, y, z, w }
    }
}

impl From<[f32; 4]> for Vec4 {
    #[inline]
    fn from([x, y, z, w]: [f32; 4]) -> Self {
        Self { x, y, z, w }
    }
}

impl From<Vec4> for (f32, f32, f32, f32) {
    #[inline]
    fn from(v: Vec4) -> Self {
        (v.x, v.y, v.z, v.w)
    }
}

impl From<Vec4> for [f32; 4] {
    #[inline]
    fn from(v: Vec4) -> Self {
        [v.x, v.y, v.z, v.w]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constants() {
        assert_eq!(Vec4::ZERO, Vec4::new(0.0, 0.0, 0.0, 0.0));
        assert_eq!(Vec4::ONE, Vec4::new(1.0, 1.0, 1.0, 1.0));
        assert_eq!(Vec4::X, Vec4::new(1.0, 0.0, 0.0, 0.0));
        assert_eq!(Vec4::Y, Vec4::new(0.0, 1.0, 0.0, 0.0));
        assert_eq!(Vec4::Z, Vec4::new(0.0, 0.0, 1.0, 0.0));
        assert_eq!(Vec4::W, Vec4::new(0.0, 0.0, 0.0, 1.0));
    }

    #[test]
    fn test_new_and_splat() {
        let v = Vec4::new(1.0, 2.0, 3.0, 4.0);
        assert_eq!(v.x, 1.0);
        assert_eq!(v.y, 2.0);
        assert_eq!(v.z, 3.0);
        assert_eq!(v.w, 4.0);

        let s = Vec4::splat(5.0);
        assert_eq!(s, Vec4::new(5.0, 5.0, 5.0, 5.0));
    }

    #[test]
    fn test_from_vec3() {
        let v3 = Vec3::new(1.0, 2.0, 3.0);
        let v4 = Vec4::from_vec3(v3, 4.0);
        assert_eq!(v4, Vec4::new(1.0, 2.0, 3.0, 4.0));
    }

    #[test]
    fn test_from_vec2() {
        let v2 = Vec2::new(1.0, 2.0);
        let v4 = Vec4::from_vec2(v2, 3.0, 4.0);
        assert_eq!(v4, Vec4::new(1.0, 2.0, 3.0, 4.0));
    }

    #[test]
    fn test_swizzle() {
        let v = Vec4::new(1.0, 2.0, 3.0, 4.0);
        assert_eq!(v.xy(), Vec2::new(1.0, 2.0));
        assert_eq!(v.xyz(), Vec3::new(1.0, 2.0, 3.0));
    }

    #[test]
    fn test_dot() {
        let a = Vec4::new(1.0, 2.0, 3.0, 4.0);
        let b = Vec4::new(5.0, 6.0, 7.0, 8.0);
        assert_eq!(a.dot(b), 70.0); // 1*5 + 2*6 + 3*7 + 4*8 = 70
    }

    #[test]
    fn test_length() {
        let v = Vec4::new(1.0, 2.0, 2.0, 4.0);
        assert_eq!(v.length_squared(), 25.0);
        assert_eq!(v.length(), 5.0);
    }

    #[test]
    fn test_normalized() {
        let v = Vec4::new(1.0, 2.0, 2.0, 4.0).normalized();
        assert!((v.length() - 1.0).abs() < 1e-6);

        assert_eq!(Vec4::ZERO.normalized(), Vec4::ZERO);
    }

    #[test]
    fn test_lerp() {
        let a = Vec4::ZERO;
        let b = Vec4::new(10.0, 20.0, 30.0, 40.0);

        assert_eq!(a.lerp(b, 0.0), a);
        assert_eq!(a.lerp(b, 1.0), b);
        assert_eq!(a.lerp(b, 0.5), Vec4::new(5.0, 10.0, 15.0, 20.0));
    }

    #[test]
    fn test_abs() {
        assert_eq!(
            Vec4::new(-1.0, 2.0, -3.0, 4.0).abs(),
            Vec4::new(1.0, 2.0, 3.0, 4.0)
        );
    }

    #[test]
    fn test_clamp() {
        let v = Vec4::new(-5.0, 5.0, 15.0, 20.0);
        let clamped = v.clamp(Vec4::ZERO, Vec4::splat(10.0));
        assert_eq!(clamped, Vec4::new(0.0, 5.0, 10.0, 10.0));
    }

    #[test]
    fn test_min_max() {
        let a = Vec4::new(1.0, 4.0, 2.0, 5.0);
        let b = Vec4::new(3.0, 2.0, 5.0, 1.0);

        assert_eq!(a.min(b), Vec4::new(1.0, 2.0, 2.0, 1.0));
        assert_eq!(a.max(b), Vec4::new(3.0, 4.0, 5.0, 5.0));
    }

    #[test]
    fn test_operators() {
        let a = Vec4::new(1.0, 2.0, 3.0, 4.0);
        let b = Vec4::new(5.0, 6.0, 7.0, 8.0);

        assert_eq!(a + b, Vec4::new(6.0, 8.0, 10.0, 12.0));
        assert_eq!(a - b, Vec4::new(-4.0, -4.0, -4.0, -4.0));
        assert_eq!(a * 2.0, Vec4::new(2.0, 4.0, 6.0, 8.0));
        assert_eq!(2.0 * a, Vec4::new(2.0, 4.0, 6.0, 8.0));
        assert_eq!(a / 2.0, Vec4::new(0.5, 1.0, 1.5, 2.0));
        assert_eq!(-a, Vec4::new(-1.0, -2.0, -3.0, -4.0));
        assert_eq!(a * b, Vec4::new(5.0, 12.0, 21.0, 32.0));
    }

    #[test]
    fn test_conversions() {
        let v = Vec4::new(1.0, 2.0, 3.0, 4.0);

        let tuple: (f32, f32, f32, f32) = v.into();
        assert_eq!(tuple, (1.0, 2.0, 3.0, 4.0));

        let array: [f32; 4] = v.into();
        assert_eq!(array, [1.0, 2.0, 3.0, 4.0]);

        assert_eq!(Vec4::from((1.0, 2.0, 3.0, 4.0)), v);
        assert_eq!(Vec4::from([1.0, 2.0, 3.0, 4.0]), v);
    }

    #[test]
    fn test_display_debug() {
        let v = Vec4::new(1.0, 2.0, 3.0, 4.0);
        assert_eq!(format!("{v}"), "(1, 2, 3, 4)");
        assert_eq!(format!("{v:?}"), "Vec4 { x: 1.0, y: 2.0, z: 3.0, w: 4.0 }");
    }

    // ============================================================
    // Edge Case Tests (Phase 3 - Audit Coverage)
    // ============================================================

    #[test]
    fn test_default_is_zero() {
        let v: Vec4 = Vec4::default();
        assert_eq!(v, Vec4::ZERO);
    }

    #[test]
    fn test_division_by_zero() {
        // IEEE 754 semantics
        let v = Vec4::new(1.0, -1.0, 0.0, 2.0);
        let result = v / 0.0;

        assert!(result.x.is_infinite() && result.x > 0.0, "1/0 = +inf");
        assert!(result.y.is_infinite() && result.y < 0.0, "-1/0 = -inf");
        assert!(result.z.is_nan(), "0/0 = NaN");
        assert!(result.w.is_infinite() && result.w > 0.0, "2/0 = +inf");
    }

    #[test]
    fn test_div_assign_by_zero() {
        let mut v = Vec4::new(1.0, -1.0, 0.0, 2.0);
        v /= 0.0;

        assert!(v.x.is_infinite() && v.x > 0.0);
        assert!(v.y.is_infinite() && v.y < 0.0);
        assert!(v.z.is_nan());
        assert!(v.w.is_infinite() && v.w > 0.0);
    }

    #[test]
    fn test_normalize_in_place() {
        let mut v = Vec4::new(1.0, 2.0, 2.0, 4.0);
        v.normalize();

        assert!((v.length() - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_normalize_in_place_zero_vector() {
        let mut v = Vec4::ZERO;
        v.normalize();

        assert_eq!(v, Vec4::ZERO, "Zero vector stays zero after normalize");
    }

    #[test]
    fn test_add_assign() {
        let mut v = Vec4::new(1.0, 2.0, 3.0, 4.0);
        v += Vec4::new(5.0, 6.0, 7.0, 8.0);
        assert_eq!(v, Vec4::new(6.0, 8.0, 10.0, 12.0));
    }

    #[test]
    fn test_sub_assign() {
        let mut v = Vec4::new(6.0, 8.0, 10.0, 12.0);
        v -= Vec4::new(5.0, 6.0, 7.0, 8.0);
        assert_eq!(v, Vec4::new(1.0, 2.0, 3.0, 4.0));
    }

    #[test]
    fn test_mul_assign() {
        let mut v = Vec4::new(1.0, 2.0, 3.0, 4.0);
        v *= 2.0;
        assert_eq!(v, Vec4::new(2.0, 4.0, 6.0, 8.0));
    }

    #[test]
    fn test_lerp_extrapolation() {
        let a = Vec4::ZERO;
        let b = Vec4::new(10.0, 20.0, 30.0, 40.0);

        // t < 0 extrapolates backwards
        let back = a.lerp(b, -0.5);
        assert_eq!(back, Vec4::new(-5.0, -10.0, -15.0, -20.0));

        // t > 1 extrapolates forward
        let forward = a.lerp(b, 1.5);
        assert_eq!(forward, Vec4::new(15.0, 30.0, 45.0, 60.0));
    }

    #[test]
    fn test_clamp_preserves_in_range() {
        let v = Vec4::new(0.5, 0.5, 0.5, 0.5);
        let min = Vec4::ZERO;
        let max = Vec4::ONE;
        let clamped = v.clamp(min, max);
        assert_eq!(clamped, v);
    }

    #[test]
    fn test_clamp_boundary_values() {
        let v = Vec4::new(-1.0, 0.0, 1.0, 2.0);
        let clamped = v.clamp(Vec4::ZERO, Vec4::ONE);
        assert_eq!(clamped, Vec4::new(0.0, 0.0, 1.0, 1.0));
    }

    #[test]
    fn test_approx_eq_with_epsilon() {
        let v1 = Vec4::new(1.0, 2.0, 3.0, 4.0);
        let v2 = Vec4::new(
            1.0 + crate::EPSILON * 0.5,
            2.0 + crate::EPSILON * 0.5,
            3.0 + crate::EPSILON * 0.5,
            4.0 + crate::EPSILON * 0.5,
        );
        assert!(v1.approx_eq(v2));

        let v3 = Vec4::new(1.01, 2.0, 3.0, 4.0);
        assert!(!v1.approx_eq(v3));
    }

    #[test]
    fn test_length_squared_zero() {
        assert_eq!(Vec4::ZERO.length_squared(), 0.0);
        assert_eq!(Vec4::ZERO.length(), 0.0);
    }

    #[test]
    fn test_dot_with_self() {
        let v = Vec4::new(1.0, 2.0, 3.0, 4.0);
        // dot(v, v) = 1 + 4 + 9 + 16 = 30
        assert_eq!(v.dot(v), 30.0);
        assert_eq!(v.dot(v), v.length_squared());
    }

    #[test]
    fn test_dot_orthogonal() {
        // X and Y unit vectors are orthogonal
        assert_eq!(Vec4::X.dot(Vec4::Y), 0.0);
        assert_eq!(Vec4::X.dot(Vec4::Z), 0.0);
        assert_eq!(Vec4::X.dot(Vec4::W), 0.0);
        assert_eq!(Vec4::Y.dot(Vec4::Z), 0.0);
        assert_eq!(Vec4::Y.dot(Vec4::W), 0.0);
        assert_eq!(Vec4::Z.dot(Vec4::W), 0.0);
    }

    #[test]
    fn test_component_wise_multiplication() {
        let a = Vec4::new(1.0, 2.0, 3.0, 4.0);
        let b = Vec4::new(2.0, 3.0, 4.0, 5.0);
        let result = a * b;
        assert_eq!(result, Vec4::new(2.0, 6.0, 12.0, 20.0));
    }

    #[test]
    fn test_negation() {
        let v = Vec4::new(1.0, -2.0, 3.0, -4.0);
        assert_eq!(-v, Vec4::new(-1.0, 2.0, -3.0, 4.0));
    }

    #[test]
    fn test_scalar_multiplication_commutativity() {
        let v = Vec4::new(1.0, 2.0, 3.0, 4.0);
        let s = 2.5;
        assert_eq!(v * s, s * v);
    }

    // =========================================================================
    // Mutation Testing: Kill operator mutants
    // =========================================================================

    /// Kill *→/ and *→+ in f32 * Vec4
    #[test]
    fn test_scalar_mul_vec4_non_trivial() {
        let v = Vec4::new(3.0, 5.0, 7.0, 11.0);
        let result = 4.0 * v;
        assert_eq!(result, Vec4::new(12.0, 20.0, 28.0, 44.0));
    }

    /// Kill *=→+= in MulAssign<f32> with distinguishable values
    #[test]
    fn test_mul_assign_scalar_distinguishable() {
        let mut v = Vec4::new(3.0, 5.0, 7.0, 11.0);
        v *= 4.0;
        assert_eq!(v, Vec4::new(12.0, 20.0, 28.0, 44.0));
    }

    /// Kill /=→%= in DivAssign<f32>
    #[test]
    fn test_div_assign_scalar() {
        let mut v = Vec4::new(12.0, 20.0, 28.0, 44.0);
        v /= 4.0;
        assert_eq!(v, Vec4::new(3.0, 5.0, 7.0, 11.0));
    }
}
