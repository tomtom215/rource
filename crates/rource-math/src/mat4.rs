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
    /// * `fov_y` - Vertical field of view in radians
    /// * `aspect` - Aspect ratio (width / height)
    /// * `near` - Near clipping plane (must be positive)
    /// * `far` - Far clipping plane (must be greater than near)
    #[must_use]
    pub fn perspective(fov_y: f32, aspect: f32, near: f32, far: f32) -> Self {
        let f = 1.0 / (fov_y / 2.0).tan();
        let nf = 1.0 / (near - far);

        Self {
            m: [
                f / aspect,
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
    /// * `up` - Up direction (usually Vec3::Y)
    #[must_use]
    pub fn look_at(eye: Vec3, target: Vec3, up: Vec3) -> Self {
        let f = (target - eye).normalized();
        let s = f.cross(up).normalized();
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
        let inv_w = if w != 0.0 { 1.0 / w } else { 1.0 };

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
}
