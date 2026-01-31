// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! 3x3 matrix type for 2D transformations.

use std::fmt;
use std::ops::{Mul, MulAssign};

use crate::Vec2;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A 3x3 column-major matrix for 2D transformations.
///
/// This matrix is primarily used for 2D affine transformations including
/// translation, rotation, scaling, and shearing.
///
/// The matrix is stored in column-major order, matching OpenGL conventions.
///
/// # Memory Layout
///
/// ```text
/// | m[0] m[3] m[6] |   | a d tx |
/// | m[1] m[4] m[7] | = | b e ty |
/// | m[2] m[5] m[8] |   | 0 0 1  |
/// ```
///
/// # Examples
///
/// ```
/// use rource_math::{Mat3, Vec2, PI};
///
/// // Create a transformation: translate, then rotate
/// let translate = Mat3::translation(10.0, 20.0);
/// let rotate = Mat3::rotation(PI / 4.0);
/// let transform = rotate * translate;
///
/// // Transform a point
/// let point = Vec2::new(1.0, 0.0);
/// let transformed = transform.transform_point(point);
/// ```
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[repr(C)]
pub struct Mat3 {
    /// The matrix elements in column-major order.
    pub m: [f32; 9],
}

impl Mat3 {
    /// The identity matrix.
    pub const IDENTITY: Self = Self {
        m: [1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0],
    };

    /// A matrix with all elements set to zero.
    pub const ZERO: Self = Self { m: [0.0; 9] };

    /// Creates a new matrix from column-major elements.
    ///
    /// The parameters are named by column and row: `c{col}r{row}`.
    #[inline]
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub const fn new(
        c0r0: f32,
        c0r1: f32,
        c0r2: f32,
        c1r0: f32,
        c1r1: f32,
        c1r2: f32,
        c2r0: f32,
        c2r1: f32,
        c2r2: f32,
    ) -> Self {
        Self {
            m: [c0r0, c0r1, c0r2, c1r0, c1r1, c1r2, c2r0, c2r1, c2r2],
        }
    }

    /// Creates a matrix from three column vectors.
    #[inline]
    #[must_use]
    pub const fn from_cols(col0: [f32; 3], col1: [f32; 3], col2: [f32; 3]) -> Self {
        Self {
            m: [
                col0[0], col0[1], col0[2], col1[0], col1[1], col1[2], col2[0], col2[1], col2[2],
            ],
        }
    }

    /// Creates a translation matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::{Mat3, Vec2};
    ///
    /// let t = Mat3::translation(10.0, 20.0);
    /// let p = t.transform_point(Vec2::ZERO);
    /// assert_eq!(p, Vec2::new(10.0, 20.0));
    /// ```
    #[inline]
    #[must_use]
    pub fn translation(tx: f32, ty: f32) -> Self {
        Self {
            m: [1.0, 0.0, 0.0, 0.0, 1.0, 0.0, tx, ty, 1.0],
        }
    }

    /// Creates a translation matrix from a vector.
    #[inline]
    #[must_use]
    pub fn from_translation(v: Vec2) -> Self {
        Self::translation(v.x, v.y)
    }

    /// Creates a uniform scaling matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::{Mat3, Vec2};
    ///
    /// let s = Mat3::scaling(2.0, 3.0);
    /// let p = s.transform_point(Vec2::new(1.0, 1.0));
    /// assert_eq!(p, Vec2::new(2.0, 3.0));
    /// ```
    #[inline]
    #[must_use]
    pub fn scaling(sx: f32, sy: f32) -> Self {
        Self {
            m: [sx, 0.0, 0.0, 0.0, sy, 0.0, 0.0, 0.0, 1.0],
        }
    }

    /// Creates a uniform scaling matrix.
    #[inline]
    #[must_use]
    pub fn uniform_scaling(s: f32) -> Self {
        Self::scaling(s, s)
    }

    /// Creates a rotation matrix for the given angle in radians.
    ///
    /// Positive angles rotate counter-clockwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::{Mat3, Vec2, PI};
    ///
    /// let r = Mat3::rotation(PI / 2.0);
    /// let p = r.transform_point(Vec2::new(1.0, 0.0));
    /// assert!(p.x.abs() < 1e-6);
    /// assert!((p.y - 1.0).abs() < 1e-6);
    /// ```
    #[inline]
    #[must_use]
    pub fn rotation(radians: f32) -> Self {
        let cos = radians.cos();
        let sin = radians.sin();
        Self {
            m: [cos, sin, 0.0, -sin, cos, 0.0, 0.0, 0.0, 1.0],
        }
    }

    /// Creates a shearing matrix.
    #[inline]
    #[must_use]
    pub fn shearing(shx: f32, shy: f32) -> Self {
        Self {
            m: [1.0, shy, 0.0, shx, 1.0, 0.0, 0.0, 0.0, 1.0],
        }
    }

    /// Returns the determinant of the matrix.
    #[inline]
    #[must_use]
    pub fn determinant(self) -> f32 {
        let [a, b, c, d, e, f, g, h, i] = self.m;
        a * (e * i - f * h) - d * (b * i - c * h) + g * (b * f - c * e)
    }

    /// Returns the inverse of the matrix, if it exists.
    ///
    /// Returns `None` if the matrix is not invertible (determinant is zero).
    #[must_use]
    pub fn inverse(self) -> Option<Self> {
        let det = self.determinant();
        if det.abs() < crate::EPSILON {
            return None;
        }

        let inv_det = 1.0 / det;
        let [a, b, c, d, e, f, g, h, i] = self.m;

        Some(Self {
            m: [
                (e * i - f * h) * inv_det,
                (c * h - b * i) * inv_det,
                (b * f - c * e) * inv_det,
                (f * g - d * i) * inv_det,
                (a * i - c * g) * inv_det,
                (c * d - a * f) * inv_det,
                (d * h - e * g) * inv_det,
                (b * g - a * h) * inv_det,
                (a * e - b * d) * inv_det,
            ],
        })
    }

    /// Returns the transpose of the matrix.
    #[inline]
    #[must_use]
    pub fn transpose(self) -> Self {
        let [a, b, c, d, e, f, g, h, i] = self.m;
        Self {
            m: [a, d, g, b, e, h, c, f, i],
        }
    }

    /// Transforms a 2D point by this matrix.
    ///
    /// The point is treated as having w=1 (homogeneous coordinates),
    /// so translation is applied.
    #[inline]
    #[must_use]
    pub fn transform_point(self, p: Vec2) -> Vec2 {
        Vec2 {
            x: self.m[0] * p.x + self.m[3] * p.y + self.m[6],
            y: self.m[1] * p.x + self.m[4] * p.y + self.m[7],
        }
    }

    /// Transforms a 2D vector by this matrix.
    ///
    /// The vector is treated as having w=0 (homogeneous coordinates),
    /// so translation is NOT applied.
    #[inline]
    #[must_use]
    pub fn transform_vector(self, v: Vec2) -> Vec2 {
        Vec2 {
            x: self.m[0] * v.x + self.m[3] * v.y,
            y: self.m[1] * v.x + self.m[4] * v.y,
        }
    }

    /// Returns the translation component of this matrix.
    #[inline]
    #[must_use]
    pub fn get_translation(self) -> Vec2 {
        Vec2 {
            x: self.m[6],
            y: self.m[7],
        }
    }

    /// Returns the scale factors of this matrix.
    ///
    /// Note: This only works correctly for matrices without rotation/shear.
    #[inline]
    #[must_use]
    pub fn get_scale(self) -> Vec2 {
        Vec2 {
            x: Vec2::new(self.m[0], self.m[1]).length(),
            y: Vec2::new(self.m[3], self.m[4]).length(),
        }
    }

    /// Checks if this matrix is approximately equal to another.
    #[must_use]
    pub fn approx_eq(self, other: Self) -> bool {
        self.m
            .iter()
            .zip(other.m.iter())
            .all(|(a, b)| crate::approx_eq(*a, *b))
    }
}

impl Default for Mat3 {
    #[inline]
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl Mul for Mat3 {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let a = &self.m;
        let b = &other.m;

        Self {
            m: [
                a[0] * b[0] + a[3] * b[1] + a[6] * b[2],
                a[1] * b[0] + a[4] * b[1] + a[7] * b[2],
                a[2] * b[0] + a[5] * b[1] + a[8] * b[2],
                a[0] * b[3] + a[3] * b[4] + a[6] * b[5],
                a[1] * b[3] + a[4] * b[4] + a[7] * b[5],
                a[2] * b[3] + a[5] * b[4] + a[8] * b[5],
                a[0] * b[6] + a[3] * b[7] + a[6] * b[8],
                a[1] * b[6] + a[4] * b[7] + a[7] * b[8],
                a[2] * b[6] + a[5] * b[7] + a[8] * b[8],
            ],
        }
    }
}

impl MulAssign for Mat3 {
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other;
    }
}

impl fmt::Debug for Mat3 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Mat3").field("m", &self.m).finish()
    }
}

impl fmt::Display for Mat3 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "| {:8.4} {:8.4} {:8.4} |\n| {:8.4} {:8.4} {:8.4} |\n| {:8.4} {:8.4} {:8.4} |",
            self.m[0],
            self.m[3],
            self.m[6],
            self.m[1],
            self.m[4],
            self.m[7],
            self.m[2],
            self.m[5],
            self.m[8]
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PI;

    #[test]
    fn test_identity() {
        let m = Mat3::IDENTITY;
        assert_eq!(m.m[0], 1.0);
        assert_eq!(m.m[4], 1.0);
        assert_eq!(m.m[8], 1.0);
        assert_eq!(m.determinant(), 1.0);
    }

    #[test]
    fn test_translation() {
        let t = Mat3::translation(10.0, 20.0);
        let p = t.transform_point(Vec2::ZERO);
        assert_eq!(p, Vec2::new(10.0, 20.0));

        let p = t.transform_point(Vec2::new(5.0, 5.0));
        assert_eq!(p, Vec2::new(15.0, 25.0));

        // Vectors should not be affected by translation
        let v = t.transform_vector(Vec2::new(1.0, 0.0));
        assert_eq!(v, Vec2::new(1.0, 0.0));
    }

    #[test]
    fn test_scaling() {
        let s = Mat3::scaling(2.0, 3.0);
        let p = s.transform_point(Vec2::new(1.0, 1.0));
        assert_eq!(p, Vec2::new(2.0, 3.0));

        let s = Mat3::uniform_scaling(2.0);
        let p = s.transform_point(Vec2::new(1.0, 1.0));
        assert_eq!(p, Vec2::new(2.0, 2.0));
    }

    #[test]
    fn test_rotation() {
        let r = Mat3::rotation(PI / 2.0);
        let p = r.transform_point(Vec2::new(1.0, 0.0));
        assert!(p.x.abs() < 1e-6);
        assert!((p.y - 1.0).abs() < 1e-6);

        let r = Mat3::rotation(PI);
        let p = r.transform_point(Vec2::new(1.0, 0.0));
        assert!((p.x + 1.0).abs() < 1e-6);
        assert!(p.y.abs() < 1e-6);
    }

    #[test]
    fn test_shearing() {
        let s = Mat3::shearing(1.0, 0.0);
        let p = s.transform_point(Vec2::new(1.0, 1.0));
        assert_eq!(p, Vec2::new(2.0, 1.0));
    }

    #[test]
    fn test_determinant() {
        assert_eq!(Mat3::IDENTITY.determinant(), 1.0);
        assert_eq!(Mat3::scaling(2.0, 3.0).determinant(), 6.0);
        assert!((Mat3::rotation(PI / 4.0).determinant() - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_inverse() {
        let t = Mat3::translation(10.0, 20.0);
        let t_inv = t.inverse().unwrap();
        let product = t * t_inv;
        assert!(product.approx_eq(Mat3::IDENTITY));

        let s = Mat3::scaling(2.0, 4.0);
        let s_inv = s.inverse().unwrap();
        let product = s * s_inv;
        assert!(product.approx_eq(Mat3::IDENTITY));

        let r = Mat3::rotation(PI / 3.0);
        let r_inv = r.inverse().unwrap();
        let product = r * r_inv;
        assert!(product.approx_eq(Mat3::IDENTITY));

        // Singular matrix should return None
        let singular = Mat3::ZERO;
        assert!(singular.inverse().is_none());
    }

    #[test]
    fn test_transpose() {
        let m = Mat3::new(1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0);
        let t = m.transpose();
        assert_eq!(t.m[0], 1.0);
        assert_eq!(t.m[1], 4.0);
        assert_eq!(t.m[2], 7.0);
        assert_eq!(t.m[3], 2.0);
        assert_eq!(t.m[4], 5.0);
        assert_eq!(t.m[5], 8.0);
    }

    #[test]
    fn test_matrix_multiplication() {
        let t = Mat3::translation(10.0, 0.0);
        let s = Mat3::scaling(2.0, 2.0);

        // Scale then translate
        let m = t * s;
        let p = m.transform_point(Vec2::new(1.0, 0.0));
        assert_eq!(p, Vec2::new(12.0, 0.0)); // 1*2 + 10 = 12

        // Translate then scale
        let m = s * t;
        let p = m.transform_point(Vec2::new(1.0, 0.0));
        assert_eq!(p, Vec2::new(22.0, 0.0)); // (1 + 10) * 2 = 22
    }

    #[test]
    fn test_get_translation() {
        let t = Mat3::translation(15.0, 25.0);
        assert_eq!(t.get_translation(), Vec2::new(15.0, 25.0));
    }

    #[test]
    fn test_get_scale() {
        let s = Mat3::scaling(3.0, 4.0);
        let scale = s.get_scale();
        assert!((scale.x - 3.0).abs() < 1e-6);
        assert!((scale.y - 4.0).abs() < 1e-6);
    }

    #[test]
    fn test_from_cols() {
        let m = Mat3::from_cols([1.0, 2.0, 3.0], [4.0, 5.0, 6.0], [7.0, 8.0, 9.0]);
        assert_eq!(m.m[0], 1.0);
        assert_eq!(m.m[1], 2.0);
        assert_eq!(m.m[2], 3.0);
        assert_eq!(m.m[3], 4.0);
    }

    #[test]
    fn test_default() {
        assert_eq!(Mat3::default(), Mat3::IDENTITY);
    }

    // ============================================================
    // Edge Case Tests (Phase 3 - Audit Coverage)
    // ============================================================

    #[test]
    fn test_from_translation() {
        let v = Vec2::new(15.0, 25.0);
        let t = Mat3::from_translation(v);
        assert_eq!(t.get_translation(), v);

        // Should produce same matrix as translation()
        let t2 = Mat3::translation(15.0, 25.0);
        assert!(t.approx_eq(t2));
    }

    #[test]
    fn test_mul_assign() {
        let mut m = Mat3::translation(10.0, 0.0);
        let s = Mat3::scaling(2.0, 2.0);
        m *= s;

        // Same as m = m * s
        let expected = Mat3::translation(10.0, 0.0) * Mat3::scaling(2.0, 2.0);
        assert!(m.approx_eq(expected));
    }

    #[test]
    fn test_double_transpose_identity() {
        let m = Mat3::new(1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0);
        let double_transposed = m.transpose().transpose();
        assert!(m.approx_eq(double_transposed), "M^T^T = M");
    }

    #[test]
    fn test_near_singular_matrix() {
        // Create a matrix with very small determinant (close to epsilon)
        let nearly_singular = Mat3::new(
            1.0,
            0.0,
            0.0,
            0.0,
            crate::EPSILON * 0.1, // Very small
            0.0,
            0.0,
            0.0,
            1.0,
        );

        // Determinant should be very small (near epsilon * 0.1)
        let det = nearly_singular.determinant();
        assert!(det.abs() < crate::EPSILON);

        // Inverse should return None for near-singular matrix
        assert!(
            nearly_singular.inverse().is_none(),
            "Near-singular matrix should not be invertible"
        );
    }

    #[test]
    fn test_inverse_times_original_is_identity() {
        let m = Mat3::translation(5.0, 10.0) * Mat3::rotation(PI / 4.0) * Mat3::scaling(2.0, 3.0);

        if let Some(inv) = m.inverse() {
            let product = m * inv;
            assert!(product.approx_eq(Mat3::IDENTITY), "M * M^-1 = I");

            let product2 = inv * m;
            assert!(product2.approx_eq(Mat3::IDENTITY), "M^-1 * M = I");
        }
    }

    #[test]
    fn test_transform_vector_ignores_translation() {
        let t = Mat3::translation(100.0, 200.0);
        let v = Vec2::new(1.0, 0.0);

        // transform_vector should ignore translation
        let result = t.transform_vector(v);
        assert_eq!(result, v, "Translation should not affect vectors");
    }

    #[test]
    fn test_transform_point_applies_translation() {
        let t = Mat3::translation(100.0, 200.0);
        let p = Vec2::ZERO;

        // transform_point should apply translation
        let result = t.transform_point(p);
        assert_eq!(result, Vec2::new(100.0, 200.0));
    }

    #[test]
    fn test_rotation_preserves_length() {
        let r = Mat3::rotation(PI / 3.0);
        let v = Vec2::new(3.0, 4.0);
        let original_len = v.length();

        let transformed = r.transform_vector(v);
        let new_len = transformed.length();

        assert!(
            (original_len - new_len).abs() < 1e-6,
            "Rotation should preserve length"
        );
    }

    #[test]
    fn test_rotation_full_circle() {
        let r = Mat3::rotation(2.0 * PI);
        let v = Vec2::new(1.0, 0.0);

        let result = r.transform_point(v);
        assert!(
            result.approx_eq(v),
            "Full rotation should return to original"
        );
    }

    #[test]
    fn test_scaling_zero() {
        let s = Mat3::scaling(0.0, 0.0);
        let v = Vec2::new(100.0, 200.0);

        let result = s.transform_point(v);
        assert_eq!(result, Vec2::ZERO, "Scaling by 0 produces zero");
    }

    #[test]
    fn test_scaling_negative() {
        let s = Mat3::scaling(-1.0, -1.0);
        let v = Vec2::new(3.0, 4.0);

        let result = s.transform_point(v);
        assert_eq!(result, Vec2::new(-3.0, -4.0), "Negative scaling reflects");
    }

    #[test]
    fn test_shearing_identity_values() {
        let sh = Mat3::shearing(0.0, 0.0);
        assert!(sh.approx_eq(Mat3::IDENTITY), "Zero shear is identity");
    }

    #[test]
    fn test_determinant_scaling() {
        // Determinant of scaling matrix = sx * sy
        let s = Mat3::scaling(3.0, 4.0);
        assert!((s.determinant() - 12.0).abs() < 1e-6);
    }

    #[test]
    fn test_determinant_rotation() {
        // Determinant of rotation matrix = 1 (preserves area)
        let r = Mat3::rotation(PI / 6.0);
        assert!((r.determinant() - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_get_scale_with_uniform_scaling() {
        let s = Mat3::uniform_scaling(5.0);
        let scale = s.get_scale();
        assert!((scale.x - 5.0).abs() < 1e-6);
        assert!((scale.y - 5.0).abs() < 1e-6);
    }

    #[test]
    fn test_identity_multiplication() {
        let m = Mat3::translation(10.0, 20.0) * Mat3::rotation(PI / 4.0);

        // M * I = M
        let result1 = m * Mat3::IDENTITY;
        assert!(result1.approx_eq(m));

        // I * M = M
        let result2 = Mat3::IDENTITY * m;
        assert!(result2.approx_eq(m));
    }

    #[test]
    fn test_zero_matrix() {
        let m = Mat3::ZERO;
        assert_eq!(m.determinant(), 0.0);
        assert!(m.inverse().is_none());

        // Zero * anything = Zero
        let result = m * Mat3::IDENTITY;
        assert!(result.approx_eq(Mat3::ZERO));
    }

    #[test]
    fn test_approx_eq_with_epsilon() {
        let m1 = Mat3::IDENTITY;
        let mut m2_elements = [0.0f32; 9];
        for (i, elem) in m2_elements.iter_mut().enumerate() {
            *elem = Mat3::IDENTITY.m[i] + crate::EPSILON * 0.5;
        }
        let m2 = Mat3 { m: m2_elements };

        assert!(m1.approx_eq(m2));

        let m3 = Mat3::new(1.01, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0);
        assert!(!m1.approx_eq(m3));
    }

    // ========================================================================
    // Additional Coverage Tests (CI Coverage)
    // ========================================================================

    #[test]
    fn test_mat3_display() {
        let m = Mat3::IDENTITY;
        let display = format!("{m}");

        // Verify display contains the expected values
        assert!(display.contains("1.0000"), "Display should show 1.0000");
        assert!(display.contains("0.0000"), "Display should show 0.0000");
        assert!(display.contains('|'), "Display should use | delimiters");
    }

    #[test]
    fn test_mat3_debug() {
        let m = Mat3::IDENTITY;
        let debug = format!("{m:?}");

        // Verify debug output contains Mat3 struct info
        assert!(debug.contains("Mat3"), "Debug should contain Mat3");
        assert!(debug.contains("m:"), "Debug should contain m field");
    }

    // =========================================================================
    // Mutation Testing: Kill MISSED mutants in mat3.rs
    // =========================================================================

    /// Kill mutants in `Mat3::determinant` (arithmetic operator swaps)
    /// Use a matrix with known, asymmetric values where +/- swaps change the result.
    #[test]
    fn test_determinant_specific_values() {
        // Use a matrix where determinant is known analytically
        // | 2  3  1 |
        // | 1  4  2 |   (column-major: col0=[2,1,0], col1=[3,4,0], col2=[1,2,1])
        // | 0  0  1 |
        let m = Mat3::new(2.0, 1.0, 0.0, 3.0, 4.0, 0.0, 1.0, 2.0, 1.0);
        // det = 2*(4*1 - 0*2) - 3*(1*1 - 0*0) + 1*(1*0 - 4*0) = 2*4 - 3*1 + 0 = 5
        let det = m.determinant();
        assert!(
            (det - 5.0).abs() < 1e-6,
            "Determinant should be 5.0, got {det}"
        );

        // Another matrix with all non-zero elements
        // | 1  2  3 |
        // | 4  5  6 |
        // | 7  8  10 |
        let m2 = Mat3::new(1.0, 4.0, 7.0, 2.0, 5.0, 8.0, 3.0, 6.0, 10.0);
        // det = 1*(5*10 - 6*8) - 2*(4*10 - 6*7) + 3*(4*8 - 5*7)
        //     = 1*(50-48) - 2*(40-42) + 3*(32-35)
        //     = 2 + 4 - 9 = -3
        let det2 = m2.determinant();
        assert!(
            (det2 - (-3.0)).abs() < 1e-6,
            "Determinant should be -3.0, got {det2}"
        );
    }

    /// Kill mutants in `Mat3::inverse` (arithmetic operator swaps, * -> /)
    /// Test inverse with a known non-trivial matrix and verify each element.
    #[test]
    fn test_inverse_specific_values() {
        // Use a matrix with known inverse
        // | 2  1  0 |
        // | 0  2  1 |  column-major: col0=[2,0,0], col1=[1,2,0], col2=[0,1,1]
        // | 0  0  1 |
        let m = Mat3::new(2.0, 0.0, 0.0, 1.0, 2.0, 0.0, 0.0, 1.0, 1.0);
        let inv = m.inverse().expect("Matrix should be invertible");

        // Verify M * M^-1 = I
        let product = m * inv;
        assert!(product.approx_eq(Mat3::IDENTITY), "M * M^-1 should equal I");

        // Also verify M^-1 * M = I
        let product2 = inv * m;
        assert!(
            product2.approx_eq(Mat3::IDENTITY),
            "M^-1 * M should equal I"
        );

        // Verify specific inverse values
        // For upper triangular matrix, det = 2*2*1 = 4
        let det = m.determinant();
        assert!((det - 4.0).abs() < 1e-6, "Det should be 4, got {det}");

        // Transform a point through M and then M^-1 to verify roundtrip
        let p = Vec2::new(3.0, 7.0);
        let transformed = m.transform_point(p);
        let recovered = inv.transform_point(transformed);
        assert!(
            recovered.approx_eq(p),
            "Roundtrip should preserve point: {p:?} -> {transformed:?} -> {recovered:?}"
        );
    }

    /// Kill mutants in `Mat3::inverse` for < with <= on det check
    #[test]
    fn test_inverse_det_at_epsilon_boundary() {
        // Matrix with determinant exactly at EPSILON threshold
        // Should return None when |det| < EPSILON
        let tiny_det = Mat3::new(crate::EPSILON * 0.5, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0);
        assert!(
            tiny_det.inverse().is_none(),
            "Matrix with det < EPSILON should not be invertible"
        );

        // Matrix with determinant just above EPSILON
        let small_det = Mat3::new(crate::EPSILON * 2.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0);
        assert!(
            small_det.inverse().is_some(),
            "Matrix with det > EPSILON should be invertible"
        );
    }

    /// Kill mutants in Mat3 Mul (arithmetic + and * swaps)
    /// Use matrices with all-distinct, non-trivial values.
    #[test]
    fn test_mul_specific_values() {
        // Two non-trivial matrices with known product
        let a = Mat3::new(1.0, 4.0, 7.0, 2.0, 5.0, 8.0, 3.0, 6.0, 9.0);
        let b = Mat3::new(9.0, 6.0, 3.0, 8.0, 5.0, 2.0, 7.0, 4.0, 1.0);

        let c = a * b;

        // Manually compute expected result (column-major multiplication)
        // c[0] = a[0]*b[0] + a[3]*b[1] + a[6]*b[2] = 1*9 + 2*6 + 3*3 = 9+12+9 = 30
        // c[1] = a[1]*b[0] + a[4]*b[1] + a[7]*b[2] = 4*9 + 5*6 + 6*3 = 36+30+18 = 84
        // c[2] = a[2]*b[0] + a[5]*b[1] + a[8]*b[2] = 7*9 + 8*6 + 9*3 = 63+48+27 = 138
        assert!(
            (c.m[0] - 30.0).abs() < 1e-6,
            "c[0] = {}, expected 30",
            c.m[0]
        );
        assert!(
            (c.m[1] - 84.0).abs() < 1e-6,
            "c[1] = {}, expected 84",
            c.m[1]
        );
        assert!(
            (c.m[2] - 138.0).abs() < 1e-6,
            "c[2] = {}, expected 138",
            c.m[2]
        );

        // c[3] = a[0]*b[3] + a[3]*b[4] + a[6]*b[5] = 1*8 + 2*5 + 3*2 = 8+10+6 = 24
        // c[4] = a[1]*b[3] + a[4]*b[4] + a[7]*b[5] = 4*8 + 5*5 + 6*2 = 32+25+12 = 69
        // c[5] = a[2]*b[3] + a[5]*b[4] + a[8]*b[5] = 7*8 + 8*5 + 9*2 = 56+40+18 = 114
        assert!(
            (c.m[3] - 24.0).abs() < 1e-6,
            "c[3] = {}, expected 24",
            c.m[3]
        );
        assert!(
            (c.m[4] - 69.0).abs() < 1e-6,
            "c[4] = {}, expected 69",
            c.m[4]
        );
        assert!(
            (c.m[5] - 114.0).abs() < 1e-6,
            "c[5] = {}, expected 114",
            c.m[5]
        );

        // c[6] = a[0]*b[6] + a[3]*b[7] + a[6]*b[8] = 1*7 + 2*4 + 3*1 = 7+8+3 = 18
        // c[7] = a[1]*b[6] + a[4]*b[7] + a[7]*b[8] = 4*7 + 5*4 + 6*1 = 28+20+6 = 54
        // c[8] = a[2]*b[6] + a[5]*b[7] + a[8]*b[8] = 7*7 + 8*4 + 9*1 = 49+32+9 = 90
        assert!(
            (c.m[6] - 18.0).abs() < 1e-6,
            "c[6] = {}, expected 18",
            c.m[6]
        );
        assert!(
            (c.m[7] - 54.0).abs() < 1e-6,
            "c[7] = {}, expected 54",
            c.m[7]
        );
        assert!(
            (c.m[8] - 90.0).abs() < 1e-6,
            "c[8] = {}, expected 90",
            c.m[8]
        );
    }

    /// Additional inverse test with transform roundtrip using combined transforms
    #[test]
    fn test_inverse_combined_transforms() {
        let m = Mat3::translation(7.0, -3.0) * Mat3::rotation(1.2) * Mat3::scaling(2.5, 0.8);
        let inv = m
            .inverse()
            .expect("Combined transform should be invertible");

        // Multiple point roundtrips
        for (px, py) in [(1.0, 0.0), (0.0, 1.0), (-3.0, 7.0), (100.0, -50.0)] {
            let p = Vec2::new(px, py);
            let transformed = m.transform_point(p);
            let recovered = inv.transform_point(transformed);
            assert!(
                (recovered.x - p.x).abs() < 1e-3 && (recovered.y - p.y).abs() < 1e-3,
                "Roundtrip failed for ({px}, {py}): got ({}, {})",
                recovered.x,
                recovered.y
            );
        }
    }
}
