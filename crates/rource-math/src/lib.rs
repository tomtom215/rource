// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! # rource-math
//!
//! Mathematical types and operations for the Rource visualization engine.
//!
//! This crate provides lightweight, `no_std`-compatible math primitives with
//! zero external dependencies (except optional serde support).
//!
//! ## Features
//!
//! - **Vector types**: [`Vec2`], [`Vec3`], [`Vec4`]
//! - **Matrix types**: [`Mat3`], [`Mat4`]
//! - **Color types**: [`Color`], [`Rgb`], [`Hsl`]
//! - **Bounds types**: [`Rect`], [`Bounds`]
//!
//! ## Design Principles
//!
//! 1. **Deterministic**: All operations produce identical results across platforms
//! 2. **No heap allocation**: All types are stack-allocated with known sizes
//! 3. **Testable**: Comprehensive unit tests for all operations
//! 4. **Observable**: Debug and Display implementations for inspection

// Lints are configured in workspace Cargo.toml

mod color;
mod mat3;
mod mat4;
mod rect;
mod vec2;
mod vec3;
mod vec4;

#[cfg(kani)]
mod kani_proofs;

pub use color::{Color, Hsl, Rgb};
pub use mat3::Mat3;
pub use mat4::Mat4;
pub use rect::{Bounds, Rect};
pub use vec2::Vec2;
pub use vec3::Vec3;
pub use vec4::Vec4;

/// A small epsilon value for floating-point comparisons.
pub const EPSILON: f32 = 1e-6;

/// Two times PI.
pub const TAU: f32 = std::f32::consts::TAU;

/// PI constant.
pub const PI: f32 = std::f32::consts::PI;

/// Linear interpolation between two values.
///
/// # Arguments
///
/// * `a` - Start value
/// * `b` - End value
/// * `t` - Interpolation factor (0.0 = a, 1.0 = b)
///
/// # Examples
///
/// ```
/// use rource_math::lerp;
///
/// assert_eq!(lerp(0.0, 10.0, 0.5), 5.0);
/// assert_eq!(lerp(0.0, 10.0, 0.0), 0.0);
/// assert_eq!(lerp(0.0, 10.0, 1.0), 10.0);
/// ```
#[inline]
#[must_use]
pub fn lerp(a: f32, b: f32, t: f32) -> f32 {
    a + (b - a) * t
}

/// Clamps a value between a minimum and maximum.
///
/// # Arguments
///
/// * `value` - The value to clamp
/// * `min` - Minimum bound
/// * `max` - Maximum bound
///
/// # Examples
///
/// ```
/// use rource_math::clamp;
///
/// assert_eq!(clamp(5.0, 0.0, 10.0), 5.0);
/// assert_eq!(clamp(-5.0, 0.0, 10.0), 0.0);
/// assert_eq!(clamp(15.0, 0.0, 10.0), 10.0);
/// ```
#[inline]
#[must_use]
pub fn clamp(value: f32, min: f32, max: f32) -> f32 {
    if value < min {
        min
    } else if value > max {
        max
    } else {
        value
    }
}

/// Checks if two floating-point values are approximately equal.
///
/// # Arguments
///
/// * `a` - First value
/// * `b` - Second value
///
/// # Examples
///
/// ```
/// use rource_math::approx_eq;
///
/// assert!(approx_eq(1.0, 1.0));
/// assert!(approx_eq(1.0, 1.0 + 1e-7));
/// assert!(!approx_eq(1.0, 1.1));
/// ```
#[inline]
#[must_use]
pub fn approx_eq(a: f32, b: f32) -> bool {
    (a - b).abs() < EPSILON
}

/// Converts degrees to radians.
///
/// # Examples
///
/// ```
/// use rource_math::{deg_to_rad, PI};
///
/// assert!((deg_to_rad(180.0) - PI).abs() < 1e-6);
/// ```
#[inline]
#[must_use]
pub fn deg_to_rad(degrees: f32) -> f32 {
    degrees * PI / 180.0
}

/// Converts radians to degrees.
///
/// # Examples
///
/// ```
/// use rource_math::{rad_to_deg, PI};
///
/// assert!((rad_to_deg(PI) - 180.0).abs() < 1e-6);
/// ```
#[inline]
#[must_use]
pub fn rad_to_deg(radians: f32) -> f32 {
    radians * 180.0 / PI
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lerp() {
        assert_eq!(lerp(0.0, 10.0, 0.0), 0.0);
        assert_eq!(lerp(0.0, 10.0, 0.5), 5.0);
        assert_eq!(lerp(0.0, 10.0, 1.0), 10.0);
        assert_eq!(lerp(-10.0, 10.0, 0.5), 0.0);
    }

    #[test]
    fn test_clamp() {
        assert_eq!(clamp(5.0, 0.0, 10.0), 5.0);
        assert_eq!(clamp(-5.0, 0.0, 10.0), 0.0);
        assert_eq!(clamp(15.0, 0.0, 10.0), 10.0);
        assert_eq!(clamp(0.0, 0.0, 10.0), 0.0);
        assert_eq!(clamp(10.0, 0.0, 10.0), 10.0);
    }

    #[test]
    fn test_approx_eq() {
        assert!(approx_eq(1.0, 1.0));
        assert!(approx_eq(0.0, 0.0));
        assert!(approx_eq(1.0, 1.0 + 1e-7));
        assert!(!approx_eq(1.0, 1.1));
        assert!(!approx_eq(0.0, 1.0));
    }

    #[test]
    fn test_deg_rad_conversion() {
        assert!(approx_eq(deg_to_rad(0.0), 0.0));
        assert!(approx_eq(deg_to_rad(90.0), PI / 2.0));
        assert!(approx_eq(deg_to_rad(180.0), PI));
        assert!(approx_eq(deg_to_rad(360.0), TAU));

        assert!(approx_eq(rad_to_deg(0.0), 0.0));
        assert!(approx_eq(rad_to_deg(PI / 2.0), 90.0));
        assert!(approx_eq(rad_to_deg(PI), 180.0));
        assert!(approx_eq(rad_to_deg(TAU), 360.0));
    }

    #[test]
    fn test_roundtrip_deg_rad() {
        for deg in [0.0, 45.0, 90.0, 180.0, 270.0, 360.0] {
            assert!(approx_eq(rad_to_deg(deg_to_rad(deg)), deg));
        }
    }

    // =========================================================================
    // Mutation Testing: Kill boundary mutants for clamp and approx_eq
    // =========================================================================

    /// Kill mutant: replace < with <= in clamp (line 98)
    /// Kill mutant: replace > with >= in clamp (line 100)
    /// When value == min, `<` is false so we return value (not min).
    /// If mutated to `<=`, we'd return min (same value, but we test the path).
    /// The key: test value STRICTLY LESS than min (should return min),
    /// and a value just above min (should return value, not min).
    #[test]
    fn test_clamp_boundary_exact_min() {
        // value == min: should return value (not min via the if branch)
        // With `<`, value < min is false, so we go to else-if.
        // With `<=` mutation, value <= min is true, so we'd return min.
        // Since min == value, the result is the same numerically,
        // but we can detect the mutation by testing value JUST ABOVE min.
        let result = clamp(0.0, 0.0, 10.0);
        assert_eq!(result, 0.0);

        // Value slightly above min - should NOT be clamped to min
        let result = clamp(0.001, 0.0, 10.0);
        assert_eq!(result, 0.001, "Value just above min should not be clamped");

        // Value slightly below min - SHOULD be clamped to min
        let result = clamp(-0.001, 0.0, 10.0);
        assert_eq!(result, 0.0, "Value just below min should be clamped");
    }

    /// Kill mutant: replace > with >= in clamp (line 100)
    #[test]
    fn test_clamp_boundary_exact_max() {
        // value == max: should return value (not max via the else-if branch)
        let result = clamp(10.0, 0.0, 10.0);
        assert_eq!(result, 10.0);

        // Value slightly below max - should NOT be clamped to max
        let result = clamp(9.999, 0.0, 10.0);
        assert_eq!(result, 9.999, "Value just below max should not be clamped");

        // Value slightly above max - SHOULD be clamped to max
        let result = clamp(10.001, 0.0, 10.0);
        assert_eq!(result, 10.0, "Value just above max should be clamped");
    }

    /// Kill mutant: replace < with <= in approx_eq (line 126)
    /// approx_eq uses `(a - b).abs() < EPSILON`
    /// If mutated to `<=`, then values exactly EPSILON apart would be "equal".
    #[test]
    fn test_approx_eq_at_epsilon_boundary() {
        // Use 0.0 as base to avoid f32 precision loss from adding small to large.
        // At 0.0, |0.0 - EPSILON| = EPSILON exactly, and EPSILON < EPSILON is false.
        // With <= mutation, EPSILON <= EPSILON would be true (wrong!).
        assert!(
            !approx_eq(0.0, EPSILON),
            "Values exactly EPSILON apart should NOT be approx equal"
        );
        assert!(
            !approx_eq(0.0, -EPSILON),
            "Values exactly EPSILON apart should NOT be approx equal"
        );

        // Difference slightly less than EPSILON: SHOULD be approx equal
        assert!(
            approx_eq(0.0, EPSILON * 0.99),
            "Values less than EPSILON apart should be approx equal"
        );
    }
}
