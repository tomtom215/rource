// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! 4x4 matrix type for 3D transformations.

use std::fmt;
use std::ops::{Mul, MulAssign};

use crate::{Vec3, Vec4};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A 4x4 column-major matrix for 3D transformations.
///
/// This matrix is used for 3D transformations including translation, rotation,
/// scaling, and projection (orthographic and perspective).
///
/// The matrix is stored in column-major order, matching OpenGL conventions.
///
/// # Memory Layout
///
/// ```text
/// | m[0]  m[4]  m[8]  m[12] |
/// | m[1]  m[5]  m[9]  m[13] |
/// | m[2]  m[6]  m[10] m[14] |
/// | m[3]  m[7]  m[11] m[15] |
/// ```
///
/// # Examples
///
/// ```
/// use rource_math::{Mat4, Vec3};
///
/// // Create an orthographic projection for 2D rendering
/// let projection = Mat4::orthographic(0.0, 800.0, 600.0, 0.0, -1.0, 1.0);
///
/// // Create a view matrix
/// let view = Mat4::translation(-100.0, -50.0, 0.0);
///
/// // Combine matrices
/// let mvp = projection * view;
/// ```
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[repr(C)]
pub struct Mat4 {
    /// The matrix elements in column-major order.
    pub m: [f32; 16],
}

impl Mat4 {
    /// The identity matrix.
    pub const IDENTITY: Self = Self {
        m: [
            1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0,
        ],
    };

    /// A matrix with all elements set to zero.
    pub const ZERO: Self = Self { m: [0.0; 16] };

    /// Creates a new matrix from column-major elements.
    #[inline]
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub const fn new(
        c0r0: f32,
        c0r1: f32,
        c0r2: f32,
        c0r3: f32,
        c1r0: f32,
        c1r1: f32,
        c1r2: f32,
        c1r3: f32,
        c2r0: f32,
        c2r1: f32,
        c2r2: f32,
        c2r3: f32,
        c3r0: f32,
        c3r1: f32,
        c3r2: f32,
        c3r3: f32,
    ) -> Self {
        Self {
            m: [
                c0r0, c0r1, c0r2, c0r3, c1r0, c1r1, c1r2, c1r3, c2r0, c2r1, c2r2, c2r3, c3r0, c3r1,
                c3r2, c3r3,
            ],
        }
    }

    /// Creates a matrix from four column vectors.
    #[inline]
    #[must_use]
    pub const fn from_cols(col0: Vec4, col1: Vec4, col2: Vec4, col3: Vec4) -> Self {
        Self {
            m: [
                col0.x, col0.y, col0.z, col0.w, col1.x, col1.y, col1.z, col1.w, col2.x, col2.y,
                col2.z, col2.w, col3.x, col3.y, col3.z, col3.w,
            ],
        }
    }

    /// Creates a translation matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::{Mat4, Vec3};
    ///
    /// let t = Mat4::translation(10.0, 20.0, 30.0);
    /// let p = t.transform_point(Vec3::ZERO);
    /// assert_eq!(p, Vec3::new(10.0, 20.0, 30.0));
    /// ```
    #[inline]
    #[must_use]
    pub fn translation(tx: f32, ty: f32, tz: f32) -> Self {
        Self {
            m: [
                1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, tx, ty, tz, 1.0,
            ],
        }
    }

    /// Creates a translation matrix from a vector.
    #[inline]
    #[must_use]
    pub fn from_translation(v: Vec3) -> Self {
        Self::translation(v.x, v.y, v.z)
    }

    /// Creates a scaling matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::{Mat4, Vec3};
    ///
    /// let s = Mat4::scaling(2.0, 3.0, 4.0);
    /// let p = s.transform_point(Vec3::ONE);
    /// assert_eq!(p, Vec3::new(2.0, 3.0, 4.0));
    /// ```
    #[inline]
    #[must_use]
    pub fn scaling(sx: f32, sy: f32, sz: f32) -> Self {
        Self {
            m: [
                sx, 0.0, 0.0, 0.0, 0.0, sy, 0.0, 0.0, 0.0, 0.0, sz, 0.0, 0.0, 0.0, 0.0, 1.0,
            ],
        }
    }

    /// Creates a uniform scaling matrix.
    #[inline]
    #[must_use]
    pub fn uniform_scaling(s: f32) -> Self {
        Self::scaling(s, s, s)
    }

    /// Creates a rotation matrix around the X axis.
    ///
    /// # Arguments
    ///
    /// * `radians` - The rotation angle in radians
    #[inline]
    #[must_use]
    pub fn rotation_x(radians: f32) -> Self {
        let cos = radians.cos();
        let sin = radians.sin();
        Self {
            m: [
                1.0, 0.0, 0.0, 0.0, 0.0, cos, sin, 0.0, 0.0, -sin, cos, 0.0, 0.0, 0.0, 0.0, 1.0,
            ],
        }
    }

    /// Creates a rotation matrix around the Y axis.
    #[inline]
    #[must_use]
    pub fn rotation_y(radians: f32) -> Self {
        let cos = radians.cos();
        let sin = radians.sin();
        Self {
            m: [
                cos, 0.0, -sin, 0.0, 0.0, 1.0, 0.0, 0.0, sin, 0.0, cos, 0.0, 0.0, 0.0, 0.0, 1.0,
            ],
        }
    }

    /// Creates a rotation matrix around the Z axis.
    ///
    /// This is the most common rotation for 2D rendering.
    #[inline]
    #[must_use]
    pub fn rotation_z(radians: f32) -> Self {
        let cos = radians.cos();
        let sin = radians.sin();
        Self {
            m: [
                cos, sin, 0.0, 0.0, -sin, cos, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0,
            ],
        }
    }

    /// Creates an orthographic projection matrix.
    ///
    /// This is the standard projection for 2D rendering.
    ///
    /// # Arguments
    ///
    /// * `left` - Left edge of the viewing volume
    /// * `right` - Right edge of the viewing volume
    /// * `bottom` - Bottom edge of the viewing volume
    /// * `top` - Top edge of the viewing volume
    /// * `near` - Near clipping plane
    /// * `far` - Far clipping plane
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Mat4;
    ///
    /// // Standard 2D projection with Y-down (screen coordinates)
    /// let proj = Mat4::orthographic(0.0, 800.0, 600.0, 0.0, -1.0, 1.0);
    /// ```
    #[must_use]
    pub fn orthographic(left: f32, right: f32, bottom: f32, top: f32, near: f32, far: f32) -> Self {
        let rml = right - left;
        let tmb = top - bottom;
        let fmn = far - near;

        Self {
            m: [
                2.0 / rml,
                0.0,
                0.0,
                0.0,
                0.0,
                2.0 / tmb,
                0.0,
                0.0,
                0.0,
                0.0,
                -2.0 / fmn,
                0.0,
                -(right + left) / rml,
                -(top + bottom) / tmb,
                -(far + near) / fmn,
                1.0,
            ],
        }
    }

    /// Creates a perspective projection matrix.
    ///
    /// # Arguments
    ///
    /// * `fov_y` - Vertical field of view in radians (must be > 0 and < PI)
    /// * `aspect` - Aspect ratio (width / height, must be > 0)
    /// * `near` - Near clipping plane (must be > 0)
    /// * `far` - Far clipping plane (must be > near)
    ///
    /// # Panics
    ///
    /// Panics in debug builds if any parameter is invalid. In release builds,
    /// invalid parameters may produce a matrix with NaN or infinity values.
    #[must_use]
    pub fn perspective(fov_y: f32, aspect: f32, near: f32, far: f32) -> Self {
        debug_assert!(
            fov_y > 0.0 && fov_y < std::f32::consts::PI,
            "fov_y must be between 0 and PI radians"
        );
        debug_assert!(aspect > 0.0, "aspect ratio must be positive");
        debug_assert!(near > 0.0, "near plane must be positive");
        debug_assert!(far > near, "far plane must be greater than near plane");

        // Guard against division by zero in release builds
        let half_fov = fov_y / 2.0;
        let tan_half_fov = half_fov.tan();
        let f = if tan_half_fov.abs() < f32::EPSILON {
            f32::MAX // Prevent division by zero
        } else {
            1.0 / tan_half_fov
        };

        let plane_diff = near - far;
        let nf = if plane_diff.abs() < f32::EPSILON {
            0.0 // Degenerate case: near == far
        } else {
            1.0 / plane_diff
        };

        let safe_aspect = if aspect.abs() < f32::EPSILON {
            1.0
        } else {
            aspect
        };

        Self {
            m: [
                f / safe_aspect,
                0.0,
                0.0,
                0.0,
                0.0,
                f,
                0.0,
                0.0,
                0.0,
                0.0,
                (far + near) * nf,
                -1.0,
                0.0,
                0.0,
                2.0 * far * near * nf,
                0.0,
            ],
        }
    }

    /// Creates a look-at view matrix.
    ///
    /// # Arguments
    ///
    /// * `eye` - Camera position
    /// * `target` - Point the camera is looking at
    /// * `up` - Up direction (usually `Vec3::Y`)
    ///
    /// # Degenerate Cases
    ///
    /// - If `eye == target`, returns identity matrix (camera has no direction)
    /// - If forward direction is parallel to up, uses a fallback up vector
    #[must_use]
    pub fn look_at(eye: Vec3, target: Vec3, up: Vec3) -> Self {
        let forward = target - eye;

        // Handle degenerate case: eye == target
        if forward.length_squared() < f32::EPSILON {
            return Self::IDENTITY;
        }

        let f = forward.normalized();
        let mut s = f.cross(up);

        // Handle degenerate case: forward parallel to up
        // When forward and up are parallel, cross product is zero
        // Fall back to a perpendicular vector
        if s.length_squared() < f32::EPSILON {
            // Choose a different "up" vector that isn't parallel to forward
            let alt_up = if f.y.abs() < 0.9 { Vec3::Y } else { Vec3::X };
            s = f.cross(alt_up);
        }

        s = s.normalized();
        let u = s.cross(f);

        Self {
            m: [
                s.x,
                u.x,
                -f.x,
                0.0,
                s.y,
                u.y,
                -f.y,
                0.0,
                s.z,
                u.z,
                -f.z,
                0.0,
                -s.dot(eye),
                -u.dot(eye),
                f.dot(eye),
                1.0,
            ],
        }
    }

    /// Returns the determinant of the matrix.
    #[must_use]
    pub fn determinant(self) -> f32 {
        let m = &self.m;

        let s0 = m[0] * m[5] - m[4] * m[1];
        let s1 = m[0] * m[6] - m[4] * m[2];
        let s2 = m[0] * m[7] - m[4] * m[3];
        let s3 = m[1] * m[6] - m[5] * m[2];
        let s4 = m[1] * m[7] - m[5] * m[3];
        let s5 = m[2] * m[7] - m[6] * m[3];

        let c5 = m[10] * m[15] - m[14] * m[11];
        let c4 = m[9] * m[15] - m[13] * m[11];
        let c3 = m[9] * m[14] - m[13] * m[10];
        let c2 = m[8] * m[15] - m[12] * m[11];
        let c1 = m[8] * m[14] - m[12] * m[10];
        let c0 = m[8] * m[13] - m[12] * m[9];

        s0 * c5 - s1 * c4 + s2 * c3 + s3 * c2 - s4 * c1 + s5 * c0
    }

    /// Returns the inverse of the matrix, if it exists.
    ///
    /// Returns `None` if the matrix is not invertible (determinant is zero).
    #[must_use]
    pub fn inverse(self) -> Option<Self> {
        let m = &self.m;

        let s0 = m[0] * m[5] - m[4] * m[1];
        let s1 = m[0] * m[6] - m[4] * m[2];
        let s2 = m[0] * m[7] - m[4] * m[3];
        let s3 = m[1] * m[6] - m[5] * m[2];
        let s4 = m[1] * m[7] - m[5] * m[3];
        let s5 = m[2] * m[7] - m[6] * m[3];

        let c5 = m[10] * m[15] - m[14] * m[11];
        let c4 = m[9] * m[15] - m[13] * m[11];
        let c3 = m[9] * m[14] - m[13] * m[10];
        let c2 = m[8] * m[15] - m[12] * m[11];
        let c1 = m[8] * m[14] - m[12] * m[10];
        let c0 = m[8] * m[13] - m[12] * m[9];

        let det = s0 * c5 - s1 * c4 + s2 * c3 + s3 * c2 - s4 * c1 + s5 * c0;

        if det.abs() < crate::EPSILON {
            return None;
        }

        let inv_det = 1.0 / det;

        Some(Self {
            m: [
                (m[5] * c5 - m[6] * c4 + m[7] * c3) * inv_det,
                (-m[1] * c5 + m[2] * c4 - m[3] * c3) * inv_det,
                (m[13] * s5 - m[14] * s4 + m[15] * s3) * inv_det,
                (-m[9] * s5 + m[10] * s4 - m[11] * s3) * inv_det,
                (-m[4] * c5 + m[6] * c2 - m[7] * c1) * inv_det,
                (m[0] * c5 - m[2] * c2 + m[3] * c1) * inv_det,
                (-m[12] * s5 + m[14] * s2 - m[15] * s1) * inv_det,
                (m[8] * s5 - m[10] * s2 + m[11] * s1) * inv_det,
                (m[4] * c4 - m[5] * c2 + m[7] * c0) * inv_det,
                (-m[0] * c4 + m[1] * c2 - m[3] * c0) * inv_det,
                (m[12] * s4 - m[13] * s2 + m[15] * s0) * inv_det,
                (-m[8] * s4 + m[9] * s2 - m[11] * s0) * inv_det,
                (-m[4] * c3 + m[5] * c1 - m[6] * c0) * inv_det,
                (m[0] * c3 - m[1] * c1 + m[2] * c0) * inv_det,
                (-m[12] * s3 + m[13] * s1 - m[14] * s0) * inv_det,
                (m[8] * s3 - m[9] * s1 + m[10] * s0) * inv_det,
            ],
        })
    }

    /// Returns the transpose of the matrix.
    #[must_use]
    pub fn transpose(self) -> Self {
        let m = &self.m;
        Self {
            m: [
                m[0], m[4], m[8], m[12], m[1], m[5], m[9], m[13], m[2], m[6], m[10], m[14], m[3],
                m[7], m[11], m[15],
            ],
        }
    }

    /// Transforms a 3D point by this matrix.
    ///
    /// The point is treated as having w=1, so translation is applied.
    /// The result is divided by w (perspective division).
    #[inline]
    #[must_use]
    pub fn transform_point(self, p: Vec3) -> Vec3 {
        let w = self.m[3] * p.x + self.m[7] * p.y + self.m[11] * p.z + self.m[15];
        let inv_w = if w == 0.0 { 1.0 } else { 1.0 / w };

        Vec3 {
            x: (self.m[0] * p.x + self.m[4] * p.y + self.m[8] * p.z + self.m[12]) * inv_w,
            y: (self.m[1] * p.x + self.m[5] * p.y + self.m[9] * p.z + self.m[13]) * inv_w,
            z: (self.m[2] * p.x + self.m[6] * p.y + self.m[10] * p.z + self.m[14]) * inv_w,
        }
    }

    /// Transforms a 3D vector by this matrix.
    ///
    /// The vector is treated as having w=0, so translation is NOT applied.
    #[inline]
    #[must_use]
    pub fn transform_vector(self, v: Vec3) -> Vec3 {
        Vec3 {
            x: self.m[0] * v.x + self.m[4] * v.y + self.m[8] * v.z,
            y: self.m[1] * v.x + self.m[5] * v.y + self.m[9] * v.z,
            z: self.m[2] * v.x + self.m[6] * v.y + self.m[10] * v.z,
        }
    }

    /// Transforms a Vec4 by this matrix.
    #[inline]
    #[must_use]
    pub fn transform_vec4(self, v: Vec4) -> Vec4 {
        Vec4 {
            x: self.m[0] * v.x + self.m[4] * v.y + self.m[8] * v.z + self.m[12] * v.w,
            y: self.m[1] * v.x + self.m[5] * v.y + self.m[9] * v.z + self.m[13] * v.w,
            z: self.m[2] * v.x + self.m[6] * v.y + self.m[10] * v.z + self.m[14] * v.w,
            w: self.m[3] * v.x + self.m[7] * v.y + self.m[11] * v.z + self.m[15] * v.w,
        }
    }

    /// Returns the translation component of this matrix.
    #[inline]
    #[must_use]
    pub fn get_translation(self) -> Vec3 {
        Vec3 {
            x: self.m[12],
            y: self.m[13],
            z: self.m[14],
        }
    }

    /// Returns the scale factors of this matrix.
    ///
    /// Note: This only works correctly for matrices without rotation/shear.
    #[inline]
    #[must_use]
    pub fn get_scale(self) -> Vec3 {
        Vec3 {
            x: Vec3::new(self.m[0], self.m[1], self.m[2]).length(),
            y: Vec3::new(self.m[4], self.m[5], self.m[6]).length(),
            z: Vec3::new(self.m[8], self.m[9], self.m[10]).length(),
        }
    }

    /// Gets a column of the matrix as a Vec4.
    #[inline]
    #[must_use]
    pub fn col(self, index: usize) -> Vec4 {
        let i = index * 4;
        Vec4::new(self.m[i], self.m[i + 1], self.m[i + 2], self.m[i + 3])
    }

    /// Gets a row of the matrix as a Vec4.
    #[inline]
    #[must_use]
    pub fn row(self, index: usize) -> Vec4 {
        Vec4::new(
            self.m[index],
            self.m[index + 4],
            self.m[index + 8],
            self.m[index + 12],
        )
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

impl Default for Mat4 {
    #[inline]
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl Mul for Mat4 {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let a = &self.m;
        let b = &other.m;

        Self {
            m: [
                a[0] * b[0] + a[4] * b[1] + a[8] * b[2] + a[12] * b[3],
                a[1] * b[0] + a[5] * b[1] + a[9] * b[2] + a[13] * b[3],
                a[2] * b[0] + a[6] * b[1] + a[10] * b[2] + a[14] * b[3],
                a[3] * b[0] + a[7] * b[1] + a[11] * b[2] + a[15] * b[3],
                a[0] * b[4] + a[4] * b[5] + a[8] * b[6] + a[12] * b[7],
                a[1] * b[4] + a[5] * b[5] + a[9] * b[6] + a[13] * b[7],
                a[2] * b[4] + a[6] * b[5] + a[10] * b[6] + a[14] * b[7],
                a[3] * b[4] + a[7] * b[5] + a[11] * b[6] + a[15] * b[7],
                a[0] * b[8] + a[4] * b[9] + a[8] * b[10] + a[12] * b[11],
                a[1] * b[8] + a[5] * b[9] + a[9] * b[10] + a[13] * b[11],
                a[2] * b[8] + a[6] * b[9] + a[10] * b[10] + a[14] * b[11],
                a[3] * b[8] + a[7] * b[9] + a[11] * b[10] + a[15] * b[11],
                a[0] * b[12] + a[4] * b[13] + a[8] * b[14] + a[12] * b[15],
                a[1] * b[12] + a[5] * b[13] + a[9] * b[14] + a[13] * b[15],
                a[2] * b[12] + a[6] * b[13] + a[10] * b[14] + a[14] * b[15],
                a[3] * b[12] + a[7] * b[13] + a[11] * b[14] + a[15] * b[15],
            ],
        }
    }
}

impl MulAssign for Mat4 {
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other;
    }
}

impl Mul<Vec4> for Mat4 {
    type Output = Vec4;

    #[inline]
    fn mul(self, v: Vec4) -> Vec4 {
        self.transform_vec4(v)
    }
}

impl fmt::Debug for Mat4 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Mat4").field("m", &self.m).finish()
    }
}

impl fmt::Display for Mat4 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "| {:8.4} {:8.4} {:8.4} {:8.4} |\n\
             | {:8.4} {:8.4} {:8.4} {:8.4} |\n\
             | {:8.4} {:8.4} {:8.4} {:8.4} |\n\
             | {:8.4} {:8.4} {:8.4} {:8.4} |",
            self.m[0],
            self.m[4],
            self.m[8],
            self.m[12],
            self.m[1],
            self.m[5],
            self.m[9],
            self.m[13],
            self.m[2],
            self.m[6],
            self.m[10],
            self.m[14],
            self.m[3],
            self.m[7],
            self.m[11],
            self.m[15]
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PI;

    #[test]
    fn test_identity() {
        let m = Mat4::IDENTITY;
        assert_eq!(m.determinant(), 1.0);

        let p = m.transform_point(Vec3::new(1.0, 2.0, 3.0));
        assert_eq!(p, Vec3::new(1.0, 2.0, 3.0));
    }

    #[test]
    fn test_translation() {
        let t = Mat4::translation(10.0, 20.0, 30.0);
        let p = t.transform_point(Vec3::ZERO);
        assert_eq!(p, Vec3::new(10.0, 20.0, 30.0));

        let p = t.transform_point(Vec3::new(1.0, 2.0, 3.0));
        assert_eq!(p, Vec3::new(11.0, 22.0, 33.0));

        // Vectors should not be affected by translation
        let v = t.transform_vector(Vec3::X);
        assert_eq!(v, Vec3::X);
    }

    #[test]
    fn test_scaling() {
        let s = Mat4::scaling(2.0, 3.0, 4.0);
        let p = s.transform_point(Vec3::ONE);
        assert_eq!(p, Vec3::new(2.0, 3.0, 4.0));

        let s = Mat4::uniform_scaling(2.0);
        let p = s.transform_point(Vec3::ONE);
        assert_eq!(p, Vec3::new(2.0, 2.0, 2.0));
    }

    #[test]
    fn test_rotation_x() {
        let r = Mat4::rotation_x(PI / 2.0);
        let p = r.transform_point(Vec3::Y);
        assert!(p.x.abs() < 1e-6);
        assert!(p.y.abs() < 1e-6);
        assert!((p.z - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_rotation_y() {
        let r = Mat4::rotation_y(PI / 2.0);
        let p = r.transform_point(Vec3::X);
        assert!(p.x.abs() < 1e-6);
        assert!(p.y.abs() < 1e-6);
        assert!((p.z + 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_rotation_z() {
        let r = Mat4::rotation_z(PI / 2.0);
        let p = r.transform_point(Vec3::X);
        assert!(p.x.abs() < 1e-6);
        assert!((p.y - 1.0).abs() < 1e-6);
        assert!(p.z.abs() < 1e-6);
    }

    #[test]
    fn test_orthographic() {
        let proj = Mat4::orthographic(0.0, 800.0, 600.0, 0.0, -1.0, 1.0);

        // Center of screen should map to origin
        let p = proj.transform_point(Vec3::new(400.0, 300.0, 0.0));
        assert!(p.x.abs() < 1e-6);
        assert!(p.y.abs() < 1e-6);

        // Top-left corner
        let p = proj.transform_point(Vec3::new(0.0, 0.0, 0.0));
        assert!((p.x + 1.0).abs() < 1e-6);
        assert!((p.y - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_perspective() {
        let proj = Mat4::perspective(PI / 4.0, 16.0 / 9.0, 0.1, 100.0);
        assert!(proj.determinant().abs() > crate::EPSILON);
    }

    #[test]
    fn test_look_at() {
        let view = Mat4::look_at(Vec3::new(0.0, 0.0, 5.0), Vec3::ZERO, Vec3::Y);

        // Origin should be transformed to (0, 0, -5) in view space
        let p = view.transform_point(Vec3::ZERO);
        assert!(p.x.abs() < 1e-6);
        assert!(p.y.abs() < 1e-6);
        assert!((p.z + 5.0).abs() < 1e-6);
    }

    #[test]
    fn test_determinant() {
        assert_eq!(Mat4::IDENTITY.determinant(), 1.0);
        assert_eq!(Mat4::scaling(2.0, 3.0, 4.0).determinant(), 24.0);
    }

    #[test]
    fn test_inverse() {
        let t = Mat4::translation(10.0, 20.0, 30.0);
        let t_inv = t.inverse().unwrap();
        let product = t * t_inv;
        assert!(product.approx_eq(Mat4::IDENTITY));

        let s = Mat4::scaling(2.0, 4.0, 8.0);
        let s_inv = s.inverse().unwrap();
        let product = s * s_inv;
        assert!(product.approx_eq(Mat4::IDENTITY));

        let r = Mat4::rotation_z(PI / 3.0);
        let r_inv = r.inverse().unwrap();
        let product = r * r_inv;
        assert!(product.approx_eq(Mat4::IDENTITY));

        // Singular matrix should return None
        assert!(Mat4::ZERO.inverse().is_none());
    }

    #[test]
    fn test_transpose() {
        let m = Mat4::new(
            1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0,
        );
        let t = m.transpose();
        assert_eq!(t.m[0], 1.0);
        assert_eq!(t.m[1], 5.0);
        assert_eq!(t.m[4], 2.0);
        assert_eq!(t.m[5], 6.0);
    }

    #[test]
    fn test_matrix_multiplication() {
        let t = Mat4::translation(10.0, 0.0, 0.0);
        let s = Mat4::scaling(2.0, 2.0, 2.0);

        // Scale then translate
        let m = t * s;
        let p = m.transform_point(Vec3::new(1.0, 0.0, 0.0));
        assert_eq!(p, Vec3::new(12.0, 0.0, 0.0)); // 1*2 + 10 = 12

        // Translate then scale
        let m = s * t;
        let p = m.transform_point(Vec3::new(1.0, 0.0, 0.0));
        assert_eq!(p, Vec3::new(22.0, 0.0, 0.0)); // (1 + 10) * 2 = 22
    }

    #[test]
    fn test_get_translation() {
        let t = Mat4::translation(15.0, 25.0, 35.0);
        assert_eq!(t.get_translation(), Vec3::new(15.0, 25.0, 35.0));
    }

    #[test]
    fn test_get_scale() {
        let s = Mat4::scaling(3.0, 4.0, 5.0);
        let scale = s.get_scale();
        assert!((scale.x - 3.0).abs() < 1e-6);
        assert!((scale.y - 4.0).abs() < 1e-6);
        assert!((scale.z - 5.0).abs() < 1e-6);
    }

    #[test]
    fn test_col_row() {
        let m = Mat4::IDENTITY;
        assert_eq!(m.col(0), Vec4::new(1.0, 0.0, 0.0, 0.0));
        assert_eq!(m.row(0), Vec4::new(1.0, 0.0, 0.0, 0.0));
    }

    #[test]
    fn test_from_cols() {
        let m = Mat4::from_cols(Vec4::X, Vec4::Y, Vec4::Z, Vec4::W);
        assert!(m.approx_eq(Mat4::IDENTITY));
    }

    #[test]
    fn test_transform_vec4() {
        let t = Mat4::translation(10.0, 20.0, 30.0);
        let v = t.transform_vec4(Vec4::new(1.0, 2.0, 3.0, 1.0));
        assert_eq!(v, Vec4::new(11.0, 22.0, 33.0, 1.0));

        // w=0 should not apply translation
        let v = t.transform_vec4(Vec4::new(1.0, 2.0, 3.0, 0.0));
        assert_eq!(v, Vec4::new(1.0, 2.0, 3.0, 0.0));
    }

    #[test]
    fn test_mat4_mul_vec4() {
        let t = Mat4::translation(10.0, 20.0, 30.0);
        let v = t * Vec4::new(1.0, 2.0, 3.0, 1.0);
        assert_eq!(v, Vec4::new(11.0, 22.0, 33.0, 1.0));
    }

    #[test]
    fn test_default() {
        assert_eq!(Mat4::default(), Mat4::IDENTITY);
    }

    #[test]
    fn test_look_at_degenerate_eye_equals_target() {
        // When eye == target, should return identity (no valid direction)
        let eye = Vec3::new(1.0, 2.0, 3.0);
        let target = eye; // Same position
        let up = Vec3::Y;

        let m = Mat4::look_at(eye, target, up);

        // Should return identity matrix instead of NaN
        assert!(m.approx_eq(Mat4::IDENTITY));
    }

    #[test]
    fn test_look_at_forward_parallel_to_up() {
        // When looking straight up, forward is parallel to the up vector
        let eye = Vec3::ZERO;
        let target = Vec3::new(0.0, 10.0, 0.0); // Looking straight up
        let up = Vec3::Y;

        let m = Mat4::look_at(eye, target, up);

        // Should produce a valid matrix (no NaN values)
        for i in 0..16 {
            assert!(m.m[i].is_finite(), "Matrix element {i} is not finite");
        }
    }

    #[test]
    fn test_perspective_valid_inputs() {
        use std::f32::consts::PI;

        let fov = PI / 4.0; // 45 degrees
        let aspect = 16.0 / 9.0;
        let near = 0.1;
        let far = 100.0;

        let m = Mat4::perspective(fov, aspect, near, far);

        // Should produce valid matrix
        for i in 0..16 {
            assert!(m.m[i].is_finite(), "Matrix element {i} is not finite");
        }
    }

    /// Tests degenerate perspective matrix case.
    /// This test only runs in release mode because debug builds
    /// assert valid input parameters.
    #[test]
    #[cfg(not(debug_assertions))]
    fn test_perspective_degenerate_near_equals_far() {
        use std::f32::consts::PI;

        // This is invalid but should not produce NaN in release builds
        let m = Mat4::perspective(PI / 4.0, 1.0, 1.0, 1.0);

        // Should produce valid (though possibly incorrect) matrix
        for i in 0..16 {
            assert!(
                m.m[i].is_finite(),
                "Matrix element {} is not finite with near==far",
                i
            );
        }
    }

    // ============================================================
    // Perspective Edge Case Tests (Phase 1 - Audit Coverage)
    // ============================================================

    /// Tests perspective with near-zero aspect ratio (release build)
    #[test]
    #[cfg(not(debug_assertions))]
    fn test_perspective_near_zero_aspect() {
        use std::f32::consts::PI;

        // Near-zero aspect ratio should not produce NaN in release builds
        let m = Mat4::perspective(PI / 4.0, 0.0001, 0.1, 100.0);

        for i in 0..16 {
            assert!(
                m.m[i].is_finite(),
                "Matrix element {} is not finite with near-zero aspect",
                i
            );
        }
    }

    /// Tests perspective with zero aspect ratio (release build)
    #[test]
    #[cfg(not(debug_assertions))]
    fn test_perspective_zero_aspect() {
        use std::f32::consts::PI;

        // Zero aspect ratio should not produce NaN in release builds
        let m = Mat4::perspective(PI / 4.0, 0.0, 0.1, 100.0);

        for i in 0..16 {
            assert!(
                m.m[i].is_finite(),
                "Matrix element {} is not finite with zero aspect",
                i
            );
        }
    }

    /// Tests perspective with very small FOV (release build)
    #[test]
    #[cfg(not(debug_assertions))]
    fn test_perspective_very_small_fov() {
        // Very small FOV should produce finite values
        let m = Mat4::perspective(0.001, 1.0, 0.1, 100.0);

        for i in 0..16 {
            assert!(
                m.m[i].is_finite(),
                "Matrix element {} is not finite with very small FOV",
                i
            );
        }
    }

    /// Tests perspective with FOV near PI (release build)
    #[test]
    #[cfg(not(debug_assertions))]
    fn test_perspective_fov_near_pi() {
        use std::f32::consts::PI;

        // FOV near PI (but still valid) should produce finite values
        let m = Mat4::perspective(PI - 0.001, 1.0, 0.1, 100.0);

        for i in 0..16 {
            assert!(
                m.m[i].is_finite(),
                "Matrix element {} is not finite with FOV near PI",
                i
            );
        }
    }

    /// Tests perspective with very close near/far planes (release build)
    #[test]
    #[cfg(not(debug_assertions))]
    fn test_perspective_close_near_far() {
        use std::f32::consts::PI;

        // Very close near and far planes should not produce NaN
        let m = Mat4::perspective(PI / 4.0, 1.0, 1.0, 1.001);

        for i in 0..16 {
            assert!(
                m.m[i].is_finite(),
                "Matrix element {} is not finite with close near/far",
                i
            );
        }
    }

    /// Tests that perspective panics in debug build with invalid FOV
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "fov_y must be between 0 and PI")]
    fn test_perspective_invalid_fov_negative_debug() {
        let _ = Mat4::perspective(-0.1, 1.0, 0.1, 100.0);
    }

    /// Tests that perspective panics in debug build with FOV >= PI
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "fov_y must be between 0 and PI")]
    fn test_perspective_invalid_fov_too_large_debug() {
        use std::f32::consts::PI;
        let _ = Mat4::perspective(PI, 1.0, 0.1, 100.0);
    }

    /// Tests that perspective panics in debug build with zero aspect
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "aspect ratio must be positive")]
    fn test_perspective_invalid_aspect_debug() {
        use std::f32::consts::PI;
        let _ = Mat4::perspective(PI / 4.0, 0.0, 0.1, 100.0);
    }

    /// Tests that perspective panics in debug build with negative near
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "near plane must be positive")]
    fn test_perspective_invalid_near_debug() {
        use std::f32::consts::PI;
        let _ = Mat4::perspective(PI / 4.0, 1.0, -0.1, 100.0);
    }

    /// Tests that perspective panics in debug build with far <= near
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "far plane must be greater than near")]
    fn test_perspective_invalid_far_debug() {
        use std::f32::consts::PI;
        let _ = Mat4::perspective(PI / 4.0, 1.0, 100.0, 10.0);
    }

    // =========================================================================
    // Mutation Testing: Kill mutants for Mat4 functions
    // =========================================================================

    /// Kill return-Default mutant for from_translation
    #[test]
    fn test_from_translation_not_default() {
        let v = Vec3::new(5.0, 10.0, 15.0);
        let m = Mat4::from_translation(v);
        assert_ne!(m, Mat4::default());
        assert_eq!(m.m[12], 5.0);
        assert_eq!(m.m[13], 10.0);
        assert_eq!(m.m[14], 15.0);
    }

    /// Kill arithmetic mutants in orthographic (2.0/rml, -(right+left)/rml, etc.)
    #[test]
    fn test_orthographic_specific_elements() {
        // Non-symmetric bounds: left=1, right=5, bottom=2, top=8, near=0, far=10
        let proj = Mat4::orthographic(1.0, 5.0, 2.0, 8.0, 0.0, 10.0);
        // rml=4, tmb=6, fmn=10
        assert!((proj.m[0] - 0.5).abs() < 1e-6, "m[0]=2/rml=0.5");
        assert!((proj.m[5] - 2.0 / 6.0).abs() < 1e-6, "m[5]=2/tmb");
        assert!((proj.m[10] - (-0.2)).abs() < 1e-6, "m[10]=-2/fmn");
        assert!((proj.m[12] - (-1.5)).abs() < 1e-6, "m[12]=-(5+1)/4");
        assert!((proj.m[13] - (-10.0 / 6.0)).abs() < 1e-6, "m[13]=-(8+2)/6");
        assert!((proj.m[14] - (-1.0)).abs() < 1e-6, "m[14]=-(10+0)/10");
        assert!((proj.m[15] - 1.0).abs() < 1e-6, "m[15]=1");
    }

    /// Kill arithmetic mutants in perspective
    #[test]
    fn test_perspective_specific_elements() {
        let fov_y = PI / 3.0;
        let aspect = 1.5_f32;
        let near = 1.0_f32;
        let far = 100.0_f32;
        let proj = Mat4::perspective(fov_y, aspect, near, far);

        let tan_half = (fov_y / 2.0).tan();
        let f = 1.0 / tan_half;
        let nf = 1.0 / (near - far);

        assert!((proj.m[0] - f / aspect).abs() < 1e-5, "m[0]=f/aspect got {}", proj.m[0]);
        assert!((proj.m[5] - f).abs() < 1e-5, "m[5]=f got {}", proj.m[5]);
        assert!((proj.m[10] - (far + near) * nf).abs() < 1e-5, "m[10] got {}", proj.m[10]);
        assert!((proj.m[11] - (-1.0)).abs() < 1e-5, "m[11]=-1");
        assert!((proj.m[14] - 2.0 * far * near * nf).abs() < 1e-5, "m[14] got {}", proj.m[14]);
        assert!(proj.m[15].abs() < 1e-6, "m[15]=0");
    }

    /// Kill boundary mutants in perspective guards
    #[test]
    fn test_perspective_aspect_scaling() {
        let proj1 = Mat4::perspective(PI / 4.0, 1.0, 0.1, 100.0);
        let proj2 = Mat4::perspective(PI / 4.0, 2.0, 0.1, 100.0);
        assert!((proj2.m[0] - proj1.m[0] / 2.0).abs() < 1e-5,
            "Doubling aspect should halve m[0]");
    }

    /// Kill negation mutants in look_at
    #[test]
    fn test_look_at_specific_elements() {
        // Non-axis-aligned camera
        let eye = Vec3::new(1.0, 2.0, 3.0);
        let target = Vec3::new(4.0, 6.0, 3.0);
        let view = Mat4::look_at(eye, target, Vec3::Y);

        // f=(0.6,0.8,0), s=(0,0,1), u=(-0.8,0.6,0)
        assert!((view.m[0] - 0.0).abs() < 1e-5, "s.x");
        assert!((view.m[1] - (-0.8)).abs() < 1e-5, "u.x={}", view.m[1]);
        assert!((view.m[2] - (-0.6)).abs() < 1e-5, "-f.x={}", view.m[2]);

        assert!((view.m[5] - 0.6).abs() < 1e-5, "u.y={}", view.m[5]);
        assert!((view.m[6] - (-0.8)).abs() < 1e-5, "-f.y={}", view.m[6]);

        assert!((view.m[8] - 1.0).abs() < 1e-5, "s.z");
        assert!((view.m[10] - 0.0).abs() < 1e-5, "-f.z");

        assert!((view.m[12] - (-3.0)).abs() < 1e-5, "-s.dot(eye)={}", view.m[12]);
        assert!((view.m[13] - (-0.4)).abs() < 1e-5, "-u.dot(eye)={}", view.m[13]);
        assert!((view.m[14] - 2.2).abs() < 1e-5, "f.dot(eye)={}", view.m[14]);
    }

    /// Kill arithmetic mutants in determinant with non-trivial matrices
    #[test]
    fn test_determinant_non_trivial() {
        // Combined rotation * scaling: det = det(R) * det(S) = 1 * 30 = 30
        let m = Mat4::rotation_z(1.0) * Mat4::scaling(2.0, 3.0, 5.0);
        assert!((m.determinant() - 30.0).abs() < 1e-3, "det={}", m.determinant());

        // Upper triangular: det = product of diagonal = 2*3*7*11 = 462
        let upper = Mat4::new(
            2.0, 0.0, 0.0, 0.0,
            1.0, 3.0, 0.0, 0.0,
            4.0, 5.0, 7.0, 0.0,
            1.0, 2.0, 3.0, 11.0,
        );
        assert!((upper.determinant() - 462.0).abs() < 1e-2, "det={}", upper.determinant());

        // Reflection: det = -1
        assert!((Mat4::scaling(-1.0, 1.0, 1.0).determinant() - (-1.0)).abs() < 1e-6);
    }

    /// Kill arithmetic mutants in inverse - verify specific elements and roundtrips
    #[test]
    fn test_inverse_specific_elements() {
        let s = Mat4::scaling(2.0, 3.0, 5.0);
        let s_inv = s.inverse().unwrap();
        assert!((s_inv.m[0] - 0.5).abs() < 1e-6);
        assert!((s_inv.m[5] - 1.0 / 3.0).abs() < 1e-6);
        assert!((s_inv.m[10] - 0.2).abs() < 1e-6);

        let t = Mat4::translation(7.0, 11.0, 13.0);
        let t_inv = t.inverse().unwrap();
        assert!((t_inv.m[12] - (-7.0)).abs() < 1e-6);
        assert!((t_inv.m[13] - (-11.0)).abs() < 1e-6);
        assert!((t_inv.m[14] - (-13.0)).abs() < 1e-6);

        // Dense matrix roundtrip
        let m = Mat4::rotation_x(0.7) * Mat4::scaling(2.0, 3.0, 5.0) * Mat4::translation(1.0, 2.0, 3.0);
        let m_inv = m.inverse().unwrap();
        assert!((m * m_inv).approx_eq(Mat4::IDENTITY));

        for p in [Vec3::new(1.0, 2.0, 3.0), Vec3::new(-5.0, 7.0, -11.0)] {
            let recovered = m_inv.transform_point(m.transform_point(p));
            assert!(recovered.approx_eq(p), "roundtrip failed for {p:?}");
        }
    }

    /// Kill boundary mutant: det.abs() < EPSILON
    #[test]
    fn test_inverse_det_boundary() {
        assert!(Mat4::ZERO.inverse().is_none());

        // det = 0.01^3 = 1e-6 = EPSILON, strict < means invertible
        let at_epsilon = Mat4::scaling(0.01, 0.01, 0.01);
        assert!(at_epsilon.inverse().is_some());

        // det = 0.001^3 = 1e-9 < EPSILON, not invertible
        let below_epsilon = Mat4::scaling(0.001, 0.001, 0.001);
        assert!(below_epsilon.inverse().is_none());
    }

    /// Kill arithmetic mutants in transform_point
    #[test]
    fn test_transform_point_dense() {
        let m = Mat4::scaling(2.0, 3.0, 4.0) * Mat4::translation(1.0, 2.0, 3.0);
        // Translation first: (1,1,1)→(2,3,4), then scale: (4,9,16)
        let result = m.transform_point(Vec3::ONE);
        assert!((result.x - 4.0).abs() < 1e-5);
        assert!((result.y - 9.0).abs() < 1e-5);
        assert!((result.z - 16.0).abs() < 1e-5);
    }

    /// Kill arithmetic mutants in transform_vector
    #[test]
    fn test_transform_vector_dense() {
        let s = Mat4::scaling(2.0, 3.0, 4.0);
        let result = s.transform_vector(Vec3::ONE);
        assert_eq!(result, Vec3::new(2.0, 3.0, 4.0));

        // Translation must NOT affect vectors
        let t = Mat4::translation(100.0, 200.0, 300.0);
        assert_eq!(t.transform_vector(Vec3::new(1.0, 2.0, 3.0)), Vec3::new(1.0, 2.0, 3.0));
    }

    /// Kill arithmetic mutants in transform_vec4 - verify all 4 components
    #[test]
    fn test_transform_vec4_all_components() {
        let m = Mat4::new(
            1.0, 5.0, 9.0, 13.0,
            2.0, 6.0, 10.0, 14.0,
            3.0, 7.0, 11.0, 15.0,
            4.0, 8.0, 12.0, 16.0,
        );
        let v = Vec4::new(1.0, 2.0, 3.0, 4.0);
        let result = m.transform_vec4(v);
        // x = 1*1+2*2+3*3+4*4 = 30
        // y = 5*1+6*2+7*3+8*4 = 70
        // z = 9*1+10*2+11*3+12*4 = 110
        // w = 13*1+14*2+15*3+16*4 = 150
        assert_eq!(result.x, 30.0);
        assert_eq!(result.y, 70.0);
        assert_eq!(result.z, 110.0);
        assert_eq!(result.w, 150.0);
    }

    /// Kill *→/ mutant in col (index * 4)
    #[test]
    fn test_col_all_indices() {
        let m = Mat4::new(
            1.0, 2.0, 3.0, 4.0,
            5.0, 6.0, 7.0, 8.0,
            9.0, 10.0, 11.0, 12.0,
            13.0, 14.0, 15.0, 16.0,
        );
        assert_eq!(m.col(0), Vec4::new(1.0, 2.0, 3.0, 4.0));
        assert_eq!(m.col(1), Vec4::new(5.0, 6.0, 7.0, 8.0));
        assert_eq!(m.col(2), Vec4::new(9.0, 10.0, 11.0, 12.0));
        assert_eq!(m.col(3), Vec4::new(13.0, 14.0, 15.0, 16.0));
    }

    /// Kill return-true mutant in approx_eq
    #[test]
    fn test_approx_eq_returns_false() {
        assert!(!Mat4::IDENTITY.approx_eq(Mat4::scaling(2.0, 3.0, 4.0)));
    }

    /// Kill return-() mutant in MulAssign
    #[test]
    fn test_mul_assign_modifies() {
        let mut m = Mat4::IDENTITY;
        m *= Mat4::scaling(2.0, 3.0, 4.0);
        assert_ne!(m, Mat4::IDENTITY);
        assert_eq!(m.m[0], 2.0);
        assert_eq!(m.m[5], 3.0);
        assert_eq!(m.m[10], 4.0);
    }

    /// Kill Mul arithmetic mutants with verifiable product
    #[test]
    fn test_mul_specific_elements() {
        let a = Mat4::new(
            1.0, 0.0, 0.0, 0.0,
            0.0, 2.0, 0.0, 0.0,
            0.0, 0.0, 3.0, 0.0,
            4.0, 5.0, 6.0, 1.0,
        );
        let b = Mat4::new(
            7.0, 0.0, 0.0, 0.0,
            0.0, 8.0, 0.0, 0.0,
            0.0, 0.0, 9.0, 0.0,
            10.0, 11.0, 12.0, 1.0,
        );
        let c = a * b;
        assert_eq!(c.m[0], 7.0);
        assert_eq!(c.m[5], 16.0);
        assert_eq!(c.m[10], 27.0);
        assert_eq!(c.m[12], 14.0);
        assert_eq!(c.m[13], 27.0);
        assert_eq!(c.m[14], 42.0);
        assert_eq!(c.m[15], 1.0);
    }

    /// Kill dense Mul mutants via transform equivalence
    #[test]
    fn test_mul_dense_equivalence() {
        let a = Mat4::rotation_x(0.3) * Mat4::rotation_y(0.5);
        let b = Mat4::rotation_y(0.7) * Mat4::rotation_z(1.1);
        let c = a * b;
        let p = Vec3::new(1.0, 2.0, 3.0);
        // Column-major: c = a * b means c*p = a*(b*p), so apply b first, then a.
        let via_separate = a.transform_point(b.transform_point(p));
        let via_product = c.transform_point(p);
        assert!(via_separate.approx_eq(via_product));
    }

    /// Kill Debug/Display return-Default mutants
    #[test]
    fn test_mat4_debug_display_not_empty() {
        let m = Mat4::scaling(2.0, 3.0, 4.0);
        let debug_str = format!("{m:?}");
        assert!(debug_str.contains("Mat4"));
        assert!(debug_str.contains("2.0"));

        let display_str = format!("{m}");
        assert!(!display_str.is_empty());
        assert!(display_str.contains("2.0"));
        assert!(display_str.contains("3.0"));
    }
}
