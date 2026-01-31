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

// =============================================================================
// SIMD-Optimized Batch Operations
// =============================================================================
//
// These operations are designed to be auto-vectorized by LLVM when compiled
// with optimizations. They process multiple vectors at once for better
// throughput on modern CPUs with SIMD units (SSE, AVX, NEON).
//
// Design principles:
// 1. Process data in contiguous memory for cache efficiency
// 2. Use simple loops that LLVM can recognize and vectorize
// 3. Avoid branches in hot paths where possible
// 4. Use #[repr(C)] struct layout for predictable memory access

impl Vec2 {
    /// Adds a constant vector to all vectors in a slice.
    ///
    /// This is optimized for auto-vectorization and processes vectors
    /// in batches for better SIMD utilization.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let mut vectors = [Vec2::new(1.0, 2.0), Vec2::new(3.0, 4.0)];
    /// Vec2::batch_add(&mut vectors, Vec2::new(10.0, 20.0));
    /// assert_eq!(vectors[0], Vec2::new(11.0, 22.0));
    /// assert_eq!(vectors[1], Vec2::new(13.0, 24.0));
    /// ```
    #[inline]
    pub fn batch_add(vectors: &mut [Self], offset: Self) {
        // Simple loop that LLVM can auto-vectorize
        for v in vectors.iter_mut() {
            v.x += offset.x;
            v.y += offset.y;
        }
    }

    /// Scales all vectors in a slice by a constant factor.
    ///
    /// This is optimized for auto-vectorization.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let mut vectors = [Vec2::new(1.0, 2.0), Vec2::new(3.0, 4.0)];
    /// Vec2::batch_scale(&mut vectors, 2.0);
    /// assert_eq!(vectors[0], Vec2::new(2.0, 4.0));
    /// assert_eq!(vectors[1], Vec2::new(6.0, 8.0));
    /// ```
    #[inline]
    pub fn batch_scale(vectors: &mut [Self], factor: f32) {
        for v in vectors.iter_mut() {
            v.x *= factor;
            v.y *= factor;
        }
    }

    /// Normalizes all vectors in a slice in place.
    ///
    /// Zero-length vectors remain unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let mut vectors = [Vec2::new(3.0, 4.0), Vec2::new(0.0, 5.0)];
    /// Vec2::batch_normalize(&mut vectors);
    /// assert!((vectors[0].length() - 1.0).abs() < 1e-6);
    /// assert!((vectors[1].length() - 1.0).abs() < 1e-6);
    /// ```
    #[inline]
    pub fn batch_normalize(vectors: &mut [Self]) {
        for v in vectors.iter_mut() {
            let len_sq = v.x * v.x + v.y * v.y;
            if len_sq > 0.0 {
                let inv_len = 1.0 / len_sq.sqrt();
                v.x *= inv_len;
                v.y *= inv_len;
            }
        }
    }

    /// Computes the dot products of corresponding vectors from two slices.
    ///
    /// Returns a vector of dot products. Panics if slices have different lengths.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let a = [Vec2::new(1.0, 0.0), Vec2::new(1.0, 2.0)];
    /// let b = [Vec2::new(0.0, 1.0), Vec2::new(3.0, 4.0)];
    /// let dots = Vec2::batch_dot(&a, &b);
    /// assert_eq!(dots, vec![0.0, 11.0]);
    /// ```
    #[inline]
    #[must_use]
    pub fn batch_dot(a: &[Self], b: &[Self]) -> Vec<f32> {
        assert_eq!(a.len(), b.len(), "Slice lengths must match");

        a.iter()
            .zip(b.iter())
            .map(|(va, vb)| va.x * vb.x + va.y * vb.y)
            .collect()
    }

    /// Computes lengths of all vectors in a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let vectors = [Vec2::new(3.0, 4.0), Vec2::new(5.0, 12.0)];
    /// let lengths = Vec2::batch_lengths(&vectors);
    /// assert_eq!(lengths, vec![5.0, 13.0]);
    /// ```
    #[inline]
    #[must_use]
    pub fn batch_lengths(vectors: &[Self]) -> Vec<f32> {
        vectors.iter().map(|v| v.x.hypot(v.y)).collect()
    }

    /// Computes squared lengths of all vectors (avoids sqrt, faster for comparisons).
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let vectors = [Vec2::new(3.0, 4.0), Vec2::new(1.0, 0.0)];
    /// let lengths_sq = Vec2::batch_lengths_squared(&vectors);
    /// assert_eq!(lengths_sq, vec![25.0, 1.0]);
    /// ```
    #[inline]
    #[must_use]
    pub fn batch_lengths_squared(vectors: &[Self]) -> Vec<f32> {
        vectors.iter().map(|v| v.x * v.x + v.y * v.y).collect()
    }

    /// Linearly interpolates between corresponding vectors from two slices.
    ///
    /// Writes results to the output slice. Panics if slices have different lengths.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let a = [Vec2::new(0.0, 0.0), Vec2::new(10.0, 10.0)];
    /// let b = [Vec2::new(10.0, 10.0), Vec2::new(20.0, 20.0)];
    /// let mut result = [Vec2::ZERO; 2];
    /// Vec2::batch_lerp(&a, &b, 0.5, &mut result);
    /// assert_eq!(result[0], Vec2::new(5.0, 5.0));
    /// assert_eq!(result[1], Vec2::new(15.0, 15.0));
    /// ```
    #[inline]
    pub fn batch_lerp(a: &[Self], b: &[Self], t: f32, out: &mut [Self]) {
        assert_eq!(a.len(), b.len(), "Slice lengths must match");
        assert_eq!(a.len(), out.len(), "Output slice length must match");

        let inv_t = 1.0 - t;
        for ((va, vb), vo) in a.iter().zip(b.iter()).zip(out.iter_mut()) {
            vo.x = va.x * inv_t + vb.x * t;
            vo.y = va.y * inv_t + vb.y * t;
        }
    }

    /// Computes distances between corresponding points from two slices.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let a = [Vec2::new(0.0, 0.0), Vec2::new(0.0, 0.0)];
    /// let b = [Vec2::new(3.0, 4.0), Vec2::new(5.0, 12.0)];
    /// let distances = Vec2::batch_distances(&a, &b);
    /// assert_eq!(distances, vec![5.0, 13.0]);
    /// ```
    #[inline]
    #[must_use]
    pub fn batch_distances(a: &[Self], b: &[Self]) -> Vec<f32> {
        assert_eq!(a.len(), b.len(), "Slice lengths must match");

        a.iter()
            .zip(b.iter())
            .map(|(va, vb)| {
                let dx = vb.x - va.x;
                let dy = vb.y - va.y;
                dx.hypot(dy)
            })
            .collect()
    }

    /// Applies a transformation to all vectors: v = v * scale + offset.
    ///
    /// This is a common pattern in physics simulations and is optimized
    /// for auto-vectorization.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Vec2;
    ///
    /// let mut vectors = [Vec2::new(1.0, 2.0), Vec2::new(3.0, 4.0)];
    /// Vec2::batch_transform_affine(&mut vectors, 2.0, Vec2::new(10.0, 10.0));
    /// assert_eq!(vectors[0], Vec2::new(12.0, 14.0)); // 1*2+10, 2*2+10
    /// assert_eq!(vectors[1], Vec2::new(16.0, 18.0)); // 3*2+10, 4*2+10
    /// ```
    #[inline]
    pub fn batch_transform_affine(vectors: &mut [Self], scale: f32, offset: Self) {
        for v in vectors.iter_mut() {
            v.x = v.x * scale + offset.x;
            v.y = v.y * scale + offset.y;
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

    // ============================================================
    // Batch Operation Tests (Phase 1 CRITICAL - Audit Coverage)
    // ============================================================

    #[test]
    fn test_batch_add_basic() {
        let mut vectors = [
            Vec2::new(1.0, 2.0),
            Vec2::new(3.0, 4.0),
            Vec2::new(5.0, 6.0),
        ];
        Vec2::batch_add(&mut vectors, Vec2::new(10.0, 20.0));
        assert_eq!(vectors[0], Vec2::new(11.0, 22.0));
        assert_eq!(vectors[1], Vec2::new(13.0, 24.0));
        assert_eq!(vectors[2], Vec2::new(15.0, 26.0));
    }

    #[test]
    fn test_batch_add_empty() {
        let mut vectors: [Vec2; 0] = [];
        Vec2::batch_add(&mut vectors, Vec2::new(10.0, 20.0));
        // Should not panic on empty slice
    }

    #[test]
    fn test_batch_add_negative_offset() {
        let mut vectors = [Vec2::new(10.0, 20.0)];
        Vec2::batch_add(&mut vectors, Vec2::new(-5.0, -10.0));
        assert_eq!(vectors[0], Vec2::new(5.0, 10.0));
    }

    #[test]
    fn test_batch_scale_basic() {
        let mut vectors = [Vec2::new(1.0, 2.0), Vec2::new(3.0, 4.0)];
        Vec2::batch_scale(&mut vectors, 3.0);
        assert_eq!(vectors[0], Vec2::new(3.0, 6.0));
        assert_eq!(vectors[1], Vec2::new(9.0, 12.0));
    }

    #[test]
    fn test_batch_scale_zero() {
        let mut vectors = [Vec2::new(5.0, 10.0)];
        Vec2::batch_scale(&mut vectors, 0.0);
        assert_eq!(vectors[0], Vec2::ZERO);
    }

    #[test]
    fn test_batch_scale_negative() {
        let mut vectors = [Vec2::new(2.0, 4.0)];
        Vec2::batch_scale(&mut vectors, -1.0);
        assert_eq!(vectors[0], Vec2::new(-2.0, -4.0));
    }

    #[test]
    fn test_batch_normalize_basic() {
        let mut vectors = [Vec2::new(3.0, 4.0), Vec2::new(5.0, 12.0)];
        Vec2::batch_normalize(&mut vectors);
        assert!((vectors[0].length() - 1.0).abs() < 1e-6);
        assert!((vectors[1].length() - 1.0).abs() < 1e-6);
        // Check direction preserved
        assert!((vectors[0].x - 0.6).abs() < 1e-6);
        assert!((vectors[0].y - 0.8).abs() < 1e-6);
    }

    #[test]
    fn test_batch_normalize_zero_vector() {
        let mut vectors = [Vec2::ZERO, Vec2::new(3.0, 4.0)];
        Vec2::batch_normalize(&mut vectors);
        // Zero vector should remain zero
        assert_eq!(vectors[0], Vec2::ZERO);
        // Non-zero vector should be normalized
        assert!((vectors[1].length() - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_batch_normalize_unit_vectors() {
        let mut vectors = [Vec2::X, Vec2::Y];
        Vec2::batch_normalize(&mut vectors);
        // Already unit vectors should remain unchanged
        assert!(vectors[0].approx_eq(Vec2::X));
        assert!(vectors[1].approx_eq(Vec2::Y));
    }

    #[test]
    fn test_batch_dot_basic() {
        let a = [
            Vec2::new(1.0, 0.0),
            Vec2::new(1.0, 2.0),
            Vec2::new(3.0, 4.0),
        ];
        let b = [
            Vec2::new(0.0, 1.0),
            Vec2::new(3.0, 4.0),
            Vec2::new(5.0, 6.0),
        ];
        let dots = Vec2::batch_dot(&a, &b);
        assert_eq!(dots.len(), 3);
        assert_eq!(dots[0], 0.0); // perpendicular
        assert_eq!(dots[1], 11.0); // 1*3 + 2*4
        assert_eq!(dots[2], 39.0); // 3*5 + 4*6
    }

    #[test]
    fn test_batch_dot_empty() {
        let a: [Vec2; 0] = [];
        let b: [Vec2; 0] = [];
        let dots = Vec2::batch_dot(&a, &b);
        assert!(dots.is_empty());
    }

    #[test]
    #[should_panic(expected = "Slice lengths must match")]
    fn test_batch_dot_mismatched_lengths() {
        let a = [Vec2::X];
        let b = [Vec2::X, Vec2::Y];
        let _ = Vec2::batch_dot(&a, &b);
    }

    #[test]
    fn test_batch_lengths_basic() {
        let vectors = [
            Vec2::new(3.0, 4.0),
            Vec2::new(5.0, 12.0),
            Vec2::new(8.0, 15.0),
        ];
        let lengths = Vec2::batch_lengths(&vectors);
        assert_eq!(lengths.len(), 3);
        assert_eq!(lengths[0], 5.0);
        assert_eq!(lengths[1], 13.0);
        assert_eq!(lengths[2], 17.0);
    }

    #[test]
    fn test_batch_lengths_zero() {
        let vectors = [Vec2::ZERO];
        let lengths = Vec2::batch_lengths(&vectors);
        assert_eq!(lengths[0], 0.0);
    }

    #[test]
    fn test_batch_lengths_squared_basic() {
        let vectors = [Vec2::new(3.0, 4.0), Vec2::new(1.0, 1.0)];
        let lengths_sq = Vec2::batch_lengths_squared(&vectors);
        assert_eq!(lengths_sq.len(), 2);
        assert_eq!(lengths_sq[0], 25.0); // 9 + 16
        assert_eq!(lengths_sq[1], 2.0); // 1 + 1
    }

    #[test]
    fn test_batch_lengths_squared_empty() {
        let vectors: [Vec2; 0] = [];
        let lengths_sq = Vec2::batch_lengths_squared(&vectors);
        assert!(lengths_sq.is_empty());
    }

    #[test]
    fn test_batch_lerp_basic() {
        let a = [Vec2::new(0.0, 0.0), Vec2::new(10.0, 10.0)];
        let b = [Vec2::new(10.0, 10.0), Vec2::new(20.0, 20.0)];
        let mut result = [Vec2::ZERO; 2];
        Vec2::batch_lerp(&a, &b, 0.5, &mut result);
        assert_eq!(result[0], Vec2::new(5.0, 5.0));
        assert_eq!(result[1], Vec2::new(15.0, 15.0));
    }

    #[test]
    fn test_batch_lerp_t_zero() {
        let a = [Vec2::new(1.0, 2.0)];
        let b = [Vec2::new(10.0, 20.0)];
        let mut result = [Vec2::ZERO; 1];
        Vec2::batch_lerp(&a, &b, 0.0, &mut result);
        assert_eq!(result[0], Vec2::new(1.0, 2.0));
    }

    #[test]
    fn test_batch_lerp_t_one() {
        let a = [Vec2::new(1.0, 2.0)];
        let b = [Vec2::new(10.0, 20.0)];
        let mut result = [Vec2::ZERO; 1];
        Vec2::batch_lerp(&a, &b, 1.0, &mut result);
        assert_eq!(result[0], Vec2::new(10.0, 20.0));
    }

    #[test]
    #[should_panic(expected = "Slice lengths must match")]
    fn test_batch_lerp_mismatched_a_b() {
        let a = [Vec2::X];
        let b = [Vec2::X, Vec2::Y];
        let mut result = [Vec2::ZERO; 1];
        Vec2::batch_lerp(&a, &b, 0.5, &mut result);
    }

    #[test]
    #[should_panic(expected = "Output slice length must match")]
    fn test_batch_lerp_mismatched_output() {
        let a = [Vec2::X, Vec2::Y];
        let b = [Vec2::X, Vec2::Y];
        let mut result = [Vec2::ZERO; 1];
        Vec2::batch_lerp(&a, &b, 0.5, &mut result);
    }

    #[test]
    fn test_batch_distances_basic() {
        let a = [
            Vec2::new(0.0, 0.0),
            Vec2::new(0.0, 0.0),
            Vec2::new(1.0, 1.0),
        ];
        let b = [
            Vec2::new(3.0, 4.0),
            Vec2::new(5.0, 12.0),
            Vec2::new(4.0, 5.0),
        ];
        let distances = Vec2::batch_distances(&a, &b);
        assert_eq!(distances.len(), 3);
        assert_eq!(distances[0], 5.0);
        assert_eq!(distances[1], 13.0);
        assert_eq!(distances[2], 5.0); // sqrt((4-1)^2 + (5-1)^2) = sqrt(9+16) = 5
    }

    #[test]
    fn test_batch_distances_same_points() {
        let a = [Vec2::new(5.0, 5.0)];
        let b = [Vec2::new(5.0, 5.0)];
        let distances = Vec2::batch_distances(&a, &b);
        assert_eq!(distances[0], 0.0);
    }

    #[test]
    #[should_panic(expected = "Slice lengths must match")]
    fn test_batch_distances_mismatched() {
        let a = [Vec2::X];
        let b = [Vec2::X, Vec2::Y];
        let _ = Vec2::batch_distances(&a, &b);
    }

    #[test]
    fn test_batch_transform_affine_basic() {
        let mut vectors = [Vec2::new(1.0, 2.0), Vec2::new(3.0, 4.0)];
        Vec2::batch_transform_affine(&mut vectors, 2.0, Vec2::new(10.0, 10.0));
        assert_eq!(vectors[0], Vec2::new(12.0, 14.0)); // 1*2+10, 2*2+10
        assert_eq!(vectors[1], Vec2::new(16.0, 18.0)); // 3*2+10, 4*2+10
    }

    #[test]
    fn test_batch_transform_affine_identity() {
        let original = [Vec2::new(5.0, 7.0)];
        let mut vectors = original;
        Vec2::batch_transform_affine(&mut vectors, 1.0, Vec2::ZERO);
        assert_eq!(vectors[0], original[0]);
    }

    #[test]
    fn test_batch_transform_affine_scale_only() {
        let mut vectors = [Vec2::new(2.0, 3.0)];
        Vec2::batch_transform_affine(&mut vectors, 3.0, Vec2::ZERO);
        assert_eq!(vectors[0], Vec2::new(6.0, 9.0));
    }

    #[test]
    fn test_batch_transform_affine_offset_only() {
        let mut vectors = [Vec2::new(2.0, 3.0)];
        Vec2::batch_transform_affine(&mut vectors, 1.0, Vec2::new(5.0, 10.0));
        assert_eq!(vectors[0], Vec2::new(7.0, 13.0));
    }

    #[test]
    fn test_batch_operations_large_slice() {
        // Test that batch operations work correctly with larger slices
        // (important for auto-vectorization verification)
        let mut vectors: Vec<Vec2> = (0..100)
            .map(|i| Vec2::new(i as f32, i as f32 * 2.0))
            .collect();
        let original = vectors.clone();

        Vec2::batch_scale(&mut vectors, 2.0);
        for (i, v) in vectors.iter().enumerate() {
            assert_eq!(v.x, original[i].x * 2.0);
            assert_eq!(v.y, original[i].y * 2.0);
        }
    }

    // =========================================================================
    // Mutation Testing: Kill operator and boundary mutants
    // =========================================================================

    /// Kill -→+ mutant in distance: use non-zero starting point
    #[test]
    fn test_distance_non_origin() {
        let a = Vec2::new(1.0, 0.0);
        let b = Vec2::new(4.0, 0.0);
        // distance = |b-a| = 3. If -→+: |b+a| = 5.
        assert_eq!(a.distance(b), 3.0);
    }

    /// Kill -→+ mutant in `distance_squared`
    #[test]
    fn test_distance_squared_non_origin() {
        let a = Vec2::new(1.0, 0.0);
        let b = Vec2::new(4.0, 0.0);
        assert_eq!(a.distance_squared(b), 9.0);
    }

    /// Kill /→* mutant in project: use non-unit onto vector
    #[test]
    fn test_project_non_unit() {
        let v = Vec2::new(3.0, 4.0);
        let onto = Vec2::new(2.0, 0.0);
        // dot=6, len_sq=4, result = (2,0) * (6/4) = (3,0)
        // If /→*: (2,0) * (6*4) = (48,0). Different.
        let result = v.project(onto);
        assert!((result.x - 3.0).abs() < 1e-6);
        assert!((result.y - 0.0).abs() < 1e-6);
    }

    /// Kill *→/ and *→+ in f32 * Vec2
    #[test]
    fn test_scalar_mul_vec2_non_trivial() {
        let v = Vec2::new(3.0, 5.0);
        let result = 4.0 * v;
        // If *→/: (4/3, 4/5). If *→+: (7, 9).
        assert_eq!(result, Vec2::new(12.0, 20.0));
    }

    /// Kill *=→+= in `MulAssign<f32>` with values that distinguish
    #[test]
    fn test_mul_assign_scalar_distinguishable() {
        let mut v = Vec2::new(3.0, 5.0);
        v *= 4.0;
        // If *=→+=: (7, 9). Actual: (12, 20).
        assert_eq!(v, Vec2::new(12.0, 20.0));
    }

    /// Kill *=→+= in `MulAssign<Vec2>`
    #[test]
    fn test_mul_assign_vec2_distinguishable() {
        let mut v = Vec2::new(3.0, 5.0);
        v *= Vec2::new(4.0, 7.0);
        // If *=→+=: (7, 12). Actual: (12, 35).
        assert_eq!(v, Vec2::new(12.0, 35.0));
    }

    /// Kill /=→%= in `DivAssign<f32>`
    #[test]
    fn test_div_assign_scalar() {
        let mut v = Vec2::new(12.0, 20.0);
        v /= 4.0;
        // If /=→%=: (0, 0). Actual: (3, 5).
        assert_eq!(v, Vec2::new(3.0, 5.0));
    }
}
