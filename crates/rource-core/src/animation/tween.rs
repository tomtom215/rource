// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Tweening and easing functions for smooth animations.
//!
//! This module provides easing functions that map a linear progress value
//! (0.0 to 1.0) to a curved output, creating smooth animation effects.
//!
//! # Easing Functions
//!
//! Easing functions are used to create natural-looking animations by
//! varying the rate of change over time. Common types include:
//!
//! - **Linear**: Constant speed (no easing)
//! - **Ease-In**: Starts slow, ends fast
//! - **Ease-Out**: Starts fast, ends slow
//! - **Ease-In-Out**: Starts slow, peaks in middle, ends slow
//!
//! # Example
//!
//! ```
//! use rource_core::animation::{Easing, ease};
//!
//! // Animate from 0 to 100 with ease-out
//! let t = 0.5; // 50% progress
//! let eased_t = ease(t, Easing::QuadOut);
//! let value = 0.0 + (100.0 - 0.0) * eased_t;
//! ```

use std::f32::consts::{FRAC_PI_2, PI};

/// Easing function types.
///
/// Each easing type defines a different curve for the animation.
/// The naming convention follows standard easing terminology:
///
/// - **In**: Acceleration from zero velocity
/// - **Out**: Deceleration to zero velocity
/// - **`InOut`**: Acceleration then deceleration
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Easing {
    /// Constant speed, no easing.
    #[default]
    Linear,

    /// Quadratic ease-in (t²)
    QuadIn,
    /// Quadratic ease-out (1 - (1-t)²)
    QuadOut,
    /// Quadratic ease-in-out
    QuadInOut,

    /// Cubic ease-in (t³)
    CubicIn,
    /// Cubic ease-out (1 - (1-t)³)
    CubicOut,
    /// Cubic ease-in-out
    CubicInOut,

    /// Quartic ease-in (t⁴)
    QuartIn,
    /// Quartic ease-out
    QuartOut,
    /// Quartic ease-in-out
    QuartInOut,

    /// Quintic ease-in (t⁵)
    QuintIn,
    /// Quintic ease-out
    QuintOut,
    /// Quintic ease-in-out
    QuintInOut,

    /// Sinusoidal ease-in
    SineIn,
    /// Sinusoidal ease-out
    SineOut,
    /// Sinusoidal ease-in-out
    SineInOut,

    /// Exponential ease-in
    ExpoIn,
    /// Exponential ease-out
    ExpoOut,
    /// Exponential ease-in-out
    ExpoInOut,

    /// Circular ease-in
    CircIn,
    /// Circular ease-out
    CircOut,
    /// Circular ease-in-out
    CircInOut,

    /// Elastic ease-in (bouncy overshoot)
    ElasticIn,
    /// Elastic ease-out
    ElasticOut,
    /// Elastic ease-in-out
    ElasticInOut,

    /// Back ease-in (slight overshoot at start)
    BackIn,
    /// Back ease-out (slight overshoot at end)
    BackOut,
    /// Back ease-in-out
    BackInOut,

    /// Bounce ease-in
    BounceIn,
    /// Bounce ease-out
    BounceOut,
    /// Bounce ease-in-out
    BounceInOut,
}

/// Applies an easing function to a progress value.
///
/// # Arguments
///
/// * `t` - Progress value, typically 0.0 to 1.0 (clamped internally)
/// * `easing` - The easing function to apply
///
/// # Returns
///
/// The eased value, typically 0.0 to 1.0 (may exceed for elastic/back)
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn ease(t: f32, easing: Easing) -> f32 {
    let t = t.clamp(0.0, 1.0);

    match easing {
        Easing::Linear => t,

        // Quadratic
        // Optimization: Direct multiplication is ~2-3x faster than powi()
        Easing::QuadIn => t * t,
        Easing::QuadOut => 1.0 - (1.0 - t) * (1.0 - t),
        Easing::QuadInOut => {
            if t < 0.5 {
                2.0 * t * t
            } else {
                let u = -2.0 * t + 2.0;
                1.0 - (u * u) * 0.5
            }
        }

        // Cubic
        // Optimization: x³ = x * x * x (direct multiplication)
        Easing::CubicIn => t * t * t,
        Easing::CubicOut => {
            let u = 1.0 - t;
            1.0 - u * u * u
        }
        Easing::CubicInOut => {
            if t < 0.5 {
                4.0 * t * t * t
            } else {
                let u = -2.0 * t + 2.0;
                1.0 - (u * u * u) * 0.5
            }
        }

        // Quartic
        // Optimization: x⁴ = (x²)² - compute x² once, then square it
        Easing::QuartIn => {
            let t2 = t * t;
            t2 * t2
        }
        Easing::QuartOut => {
            let u = 1.0 - t;
            let u2 = u * u;
            1.0 - u2 * u2
        }
        Easing::QuartInOut => {
            if t < 0.5 {
                let t2 = t * t;
                8.0 * t2 * t2
            } else {
                let u = -2.0 * t + 2.0;
                let u2 = u * u;
                1.0 - (u2 * u2) * 0.5
            }
        }

        // Quintic
        // Optimization: x⁵ = (x²)² * x
        Easing::QuintIn => {
            let t2 = t * t;
            t2 * t2 * t
        }
        Easing::QuintOut => {
            let u = 1.0 - t;
            let u2 = u * u;
            1.0 - u2 * u2 * u
        }
        Easing::QuintInOut => {
            if t < 0.5 {
                let t2 = t * t;
                16.0 * t2 * t2 * t
            } else {
                let u = -2.0 * t + 2.0;
                let u2 = u * u;
                1.0 - (u2 * u2 * u) * 0.5
            }
        }

        // Sine
        Easing::SineIn => 1.0 - (t * FRAC_PI_2).cos(),
        Easing::SineOut => (t * FRAC_PI_2).sin(),
        Easing::SineInOut => (1.0 - (t * PI).cos()) * 0.5,

        // Exponential
        // Optimization: Use exp2() instead of powf() for 2^x.
        // exp2() is a single CPU instruction (~3 cycles) vs powf() (~40-50 cycles).
        // 2^(10t - 10) = 2^(-10) * 2^(10t) = TWO_POW_NEG_10 * exp2(10t)
        Easing::ExpoIn => {
            if t == 0.0 {
                0.0
            } else {
                TWO_POW_NEG_10 * f32::exp2(10.0 * t)
            }
        }
        Easing::ExpoOut => {
            if t == 1.0 {
                1.0
            } else {
                1.0 - f32::exp2(-10.0 * t)
            }
        }
        Easing::ExpoInOut => {
            if t == 0.0 {
                0.0
            } else if t == 1.0 {
                1.0
            } else if t < 0.5 {
                // 2^(20t - 10) * 0.5 = 2^(-10) * 2^(20t) * 0.5 = 2^(-11) * 2^(20t)
                TWO_POW_NEG_11 * f32::exp2(20.0 * t)
            } else {
                // (2 - 2^(-20t + 10)) * 0.5 = (2 - 2^10 * 2^(-20t)) * 0.5
                (2.0 - TWO_POW_10 * f32::exp2(-20.0 * t)) * 0.5
            }
        }

        // Circular
        // Optimization: Replace powi(2) with direct multiplication
        Easing::CircIn => 1.0 - (1.0 - t * t).sqrt(),
        Easing::CircOut => {
            let u = t - 1.0;
            (1.0 - u * u).sqrt()
        }
        Easing::CircInOut => {
            if t < 0.5 {
                let u = 2.0 * t;
                (1.0 - (1.0 - u * u).sqrt()) * 0.5
            } else {
                let u = -2.0 * t + 2.0;
                ((1.0 - u * u).sqrt() + 1.0) * 0.5
            }
        }

        // Elastic
        Easing::ElasticIn => elastic_in(t),
        Easing::ElasticOut => elastic_out(t),
        Easing::ElasticInOut => elastic_in_out(t),

        // Back
        Easing::BackIn => back_in(t),
        Easing::BackOut => back_out(t),
        Easing::BackInOut => back_in_out(t),

        // Bounce
        Easing::BounceIn => 1.0 - bounce_out(1.0 - t),
        Easing::BounceOut => bounce_out(t),
        Easing::BounceInOut => {
            if t < 0.5 {
                (1.0 - bounce_out(1.0 - 2.0 * t)) * 0.5
            } else {
                (1.0 + bounce_out(2.0 * t - 1.0)) * 0.5
            }
        }
    }
}

// Precomputed power-of-two constants for exp2() optimization.
// Using exp2() instead of powf(2.0, x) saves ~40 CPU cycles per call.
const TWO_POW_NEG_10: f32 = 0.000_976_562_5; // 2^(-10) = 1/1024
const TWO_POW_NEG_11: f32 = 0.000_488_281_25; // 2^(-11) = 1/2048
const TWO_POW_10: f32 = 1024.0; // 2^10

// Elastic helper functions
const ELASTIC_C4: f32 = (2.0 * PI) / 3.0;
const ELASTIC_C5: f32 = (2.0 * PI) / 4.5;

fn elastic_in(t: f32) -> f32 {
    if t == 0.0 {
        0.0
    } else if t == 1.0 {
        1.0
    } else {
        // -(2^(10t - 10)) * sin(...) = -(2^(-10) * 2^(10t)) * sin(...)
        -(TWO_POW_NEG_10 * f32::exp2(10.0 * t)) * ((t * 10.0 - 10.75) * ELASTIC_C4).sin()
    }
}

fn elastic_out(t: f32) -> f32 {
    if t == 0.0 {
        0.0
    } else if t == 1.0 {
        1.0
    } else {
        f32::exp2(-10.0 * t) * ((t * 10.0 - 0.75) * ELASTIC_C4).sin() + 1.0
    }
}

fn elastic_in_out(t: f32) -> f32 {
    if t == 0.0 {
        0.0
    } else if t == 1.0 {
        1.0
    } else if t < 0.5 {
        // -(2^(20t - 10) * sin(...)) * 0.5 = -(2^(-10) * 2^(20t) * sin(...)) * 0.5
        -(TWO_POW_NEG_10 * f32::exp2(20.0 * t) * ((20.0 * t - 11.125) * ELASTIC_C5).sin()) * 0.5
    } else {
        // (2^(-20t + 10) * sin(...)) * 0.5 + 1 = (2^10 * 2^(-20t) * sin(...)) * 0.5 + 1
        (TWO_POW_10 * f32::exp2(-20.0 * t) * ((20.0 * t - 11.125) * ELASTIC_C5).sin()) * 0.5 + 1.0
    }
}

// Back helper functions
const BACK_C1: f32 = 1.70158;
const BACK_C2: f32 = BACK_C1 * 1.525;
const BACK_C3: f32 = BACK_C1 + 1.0;

fn back_in(t: f32) -> f32 {
    BACK_C3 * t * t * t - BACK_C1 * t * t
}

fn back_out(t: f32) -> f32 {
    // Optimization: Replace powi() with direct multiplication
    let u = t - 1.0;
    let u2 = u * u;
    1.0 + BACK_C3 * u2 * u + BACK_C1 * u2
}

fn back_in_out(t: f32) -> f32 {
    // Optimization: Replace powi() with direct multiplication
    if t < 0.5 {
        let u = 2.0 * t;
        let u2 = u * u;
        (u2 * ((BACK_C2 + 1.0) * u - BACK_C2)) * 0.5
    } else {
        let u = 2.0 * t - 2.0;
        let u2 = u * u;
        (u2 * ((BACK_C2 + 1.0) * u + BACK_C2) + 2.0) * 0.5
    }
}

// Bounce helper
#[allow(clippy::unreadable_literal)]
fn bounce_out(t: f32) -> f32 {
    const N1: f32 = 7.5625;
    const D1: f32 = 2.75;

    if t < 1.0 / D1 {
        N1 * t * t
    } else if t < 2.0 / D1 {
        let t = t - 1.5 / D1;
        N1 * t * t + 0.75
    } else if t < 2.5 / D1 {
        let t = t - 2.25 / D1;
        N1 * t * t + 0.9375
    } else {
        let t = t - 2.625 / D1;
        N1 * t * t + 0.984_375
    }
}

/// A tween that interpolates a value over time.
///
/// A tween represents a smooth transition from one value to another
/// over a specified duration using an easing function.
///
/// # Example
///
/// ```
/// use rource_core::animation::{Tween, Easing};
///
/// let mut tween = Tween::new(0.0, 100.0, 1.0, Easing::QuadOut);
///
/// // Update each frame
/// let dt = 0.016; // ~60 FPS
/// tween.update(dt);
///
/// // Get current value
/// let current = tween.value();
/// ```
#[derive(Debug, Clone, Copy)]
pub struct Tween {
    /// Starting value.
    start: f32,

    /// Ending value.
    end: f32,

    /// Duration in seconds.
    duration: f32,

    /// Precomputed reciprocal of duration for fast progress calculation.
    /// Using multiplication (`elapsed * inv_duration`) instead of division
    /// (`elapsed / duration`) saves ~10-15 CPU cycles per call.
    inv_duration: f32,

    /// Current elapsed time.
    elapsed: f32,

    /// Easing function.
    easing: Easing,

    /// Whether the tween has completed.
    complete: bool,
}

impl Tween {
    /// Creates a new tween.
    ///
    /// # Arguments
    ///
    /// * `start` - Starting value
    /// * `end` - Ending value
    /// * `duration` - Duration in seconds
    /// * `easing` - Easing function to use
    #[must_use]
    pub fn new(start: f32, end: f32, duration: f32, easing: Easing) -> Self {
        // Precompute inverse duration for fast progress calculation.
        // If duration is zero or negative, use 0.0 (progress() handles this case).
        let inv_duration = if duration > 0.0 { 1.0 / duration } else { 0.0 };
        Self {
            start,
            end,
            duration,
            inv_duration,
            elapsed: 0.0,
            easing,
            complete: false,
        }
    }

    /// Creates a linear tween.
    #[must_use]
    pub fn linear(start: f32, end: f32, duration: f32) -> Self {
        Self::new(start, end, duration, Easing::Linear)
    }

    /// Creates an ease-out tween (good for most UI animations).
    #[must_use]
    pub fn ease_out(start: f32, end: f32, duration: f32) -> Self {
        Self::new(start, end, duration, Easing::QuadOut)
    }

    /// Creates an ease-in-out tween (smooth start and end).
    #[must_use]
    pub fn ease_in_out(start: f32, end: f32, duration: f32) -> Self {
        Self::new(start, end, duration, Easing::QuadInOut)
    }

    /// Returns the starting value.
    #[inline]
    #[must_use]
    pub const fn start(&self) -> f32 {
        self.start
    }

    /// Returns the ending value.
    #[inline]
    #[must_use]
    pub const fn end(&self) -> f32 {
        self.end
    }

    /// Returns the duration.
    #[inline]
    #[must_use]
    pub const fn duration(&self) -> f32 {
        self.duration
    }

    /// Returns the elapsed time.
    #[inline]
    #[must_use]
    pub const fn elapsed(&self) -> f32 {
        self.elapsed
    }

    /// Returns the easing function.
    #[inline]
    #[must_use]
    pub const fn easing(&self) -> Easing {
        self.easing
    }

    /// Returns true if the tween has completed.
    #[inline]
    #[must_use]
    pub const fn is_complete(&self) -> bool {
        self.complete
    }

    /// Returns the linear progress (0.0 to 1.0).
    ///
    /// Uses precomputed `inv_duration` for O(1) multiplication instead of division.
    #[inline]
    #[must_use]
    pub fn progress(&self) -> f32 {
        if self.inv_duration == 0.0 {
            // Duration was zero or negative - return complete
            1.0
        } else {
            // Fast path: multiplication instead of division
            (self.elapsed * self.inv_duration).clamp(0.0, 1.0)
        }
    }

    /// Returns the eased progress.
    #[must_use]
    pub fn eased_progress(&self) -> f32 {
        ease(self.progress(), self.easing)
    }

    /// Returns the current interpolated value.
    #[must_use]
    pub fn value(&self) -> f32 {
        let t = self.eased_progress();
        self.start + (self.end - self.start) * t
    }

    /// Updates the tween by the given delta time.
    ///
    /// Returns `true` if the tween is still running, `false` if complete.
    pub fn update(&mut self, dt: f32) -> bool {
        if self.complete {
            return false;
        }

        self.elapsed += dt;

        if self.elapsed >= self.duration {
            self.elapsed = self.duration;
            self.complete = true;
        }

        !self.complete
    }

    /// Resets the tween to the beginning.
    pub fn reset(&mut self) {
        self.elapsed = 0.0;
        self.complete = false;
    }

    /// Reverses the tween direction.
    pub fn reverse(&mut self) {
        std::mem::swap(&mut self.start, &mut self.end);
        self.reset();
    }

    /// Sets a new target value without resetting.
    ///
    /// The current value becomes the new start value.
    pub fn retarget(&mut self, new_end: f32) {
        self.start = self.value();
        self.end = new_end;
        self.reset();
    }
}

/// Interpolates between two values using an easing function.
///
/// This is a convenience function for one-off interpolation.
///
/// # Arguments
///
/// * `start` - Starting value
/// * `end` - Ending value
/// * `t` - Progress (0.0 to 1.0)
/// * `easing` - Easing function
#[must_use]
pub fn interpolate(start: f32, end: f32, t: f32, easing: Easing) -> f32 {
    let eased_t = ease(t, easing);
    start + (end - start) * eased_t
}

/// Linear interpolation (lerp) without easing.
///
/// # Arguments
///
/// * `start` - Starting value
/// * `end` - Ending value
/// * `t` - Progress (0.0 to 1.0)
#[inline]
#[must_use]
pub fn lerp(start: f32, end: f32, t: f32) -> f32 {
    start + (end - start) * t.clamp(0.0, 1.0)
}

/// Inverse linear interpolation.
///
/// Given a value between start and end, returns the progress (0.0 to 1.0).
///
/// # Arguments
///
/// * `start` - Starting value
/// * `end` - Ending value
/// * `value` - The value to find progress for
#[inline]
#[must_use]
pub fn inverse_lerp(start: f32, end: f32, value: f32) -> f32 {
    if (end - start).abs() < f32::EPSILON {
        0.0
    } else {
        ((value - start) / (end - start)).clamp(0.0, 1.0)
    }
}

/// Remaps a value from one range to another.
///
/// # Arguments
///
/// * `value` - The value to remap
/// * `in_start` - Start of input range
/// * `in_end` - End of input range
/// * `out_start` - Start of output range
/// * `out_end` - End of output range
#[inline]
#[must_use]
pub fn remap(value: f32, in_start: f32, in_end: f32, out_start: f32, out_end: f32) -> f32 {
    let t = inverse_lerp(in_start, in_end, value);
    lerp(out_start, out_end, t)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPSILON: f32 = 0.0001;

    fn approx_eq(a: f32, b: f32) -> bool {
        (a - b).abs() < EPSILON
    }

    #[test]
    fn test_ease_linear() {
        assert!(approx_eq(ease(0.0, Easing::Linear), 0.0));
        assert!(approx_eq(ease(0.5, Easing::Linear), 0.5));
        assert!(approx_eq(ease(1.0, Easing::Linear), 1.0));
    }

    #[test]
    fn test_ease_quad_in() {
        assert!(approx_eq(ease(0.0, Easing::QuadIn), 0.0));
        assert!(approx_eq(ease(0.5, Easing::QuadIn), 0.25)); // 0.5^2
        assert!(approx_eq(ease(1.0, Easing::QuadIn), 1.0));
    }

    #[test]
    fn test_ease_quad_out() {
        assert!(approx_eq(ease(0.0, Easing::QuadOut), 0.0));
        assert!(approx_eq(ease(0.5, Easing::QuadOut), 0.75)); // 1 - (1-0.5)^2
        assert!(approx_eq(ease(1.0, Easing::QuadOut), 1.0));
    }

    #[test]
    fn test_ease_quad_in_out() {
        assert!(approx_eq(ease(0.0, Easing::QuadInOut), 0.0));
        assert!(approx_eq(ease(0.5, Easing::QuadInOut), 0.5));
        assert!(approx_eq(ease(1.0, Easing::QuadInOut), 1.0));
    }

    #[test]
    fn test_ease_cubic() {
        assert!(approx_eq(ease(0.0, Easing::CubicIn), 0.0));
        assert!(approx_eq(ease(0.5, Easing::CubicIn), 0.125)); // 0.5^3
        assert!(approx_eq(ease(1.0, Easing::CubicIn), 1.0));

        assert!(approx_eq(ease(0.0, Easing::CubicOut), 0.0));
        assert!(approx_eq(ease(1.0, Easing::CubicOut), 1.0));
    }

    #[test]
    fn test_ease_sine() {
        assert!(approx_eq(ease(0.0, Easing::SineIn), 0.0));
        assert!(approx_eq(ease(1.0, Easing::SineIn), 1.0));

        assert!(approx_eq(ease(0.0, Easing::SineOut), 0.0));
        assert!(approx_eq(ease(1.0, Easing::SineOut), 1.0));

        assert!(approx_eq(ease(0.0, Easing::SineInOut), 0.0));
        assert!(approx_eq(ease(0.5, Easing::SineInOut), 0.5));
        assert!(approx_eq(ease(1.0, Easing::SineInOut), 1.0));
    }

    #[test]
    fn test_ease_expo() {
        assert!(approx_eq(ease(0.0, Easing::ExpoIn), 0.0));
        assert!(approx_eq(ease(1.0, Easing::ExpoIn), 1.0));

        assert!(approx_eq(ease(0.0, Easing::ExpoOut), 0.0));
        assert!(approx_eq(ease(1.0, Easing::ExpoOut), 1.0));
    }

    #[test]
    fn test_ease_circ() {
        assert!(approx_eq(ease(0.0, Easing::CircIn), 0.0));
        assert!(approx_eq(ease(1.0, Easing::CircIn), 1.0));

        assert!(approx_eq(ease(0.0, Easing::CircOut), 0.0));
        assert!(approx_eq(ease(1.0, Easing::CircOut), 1.0));
    }

    #[test]
    fn test_ease_elastic() {
        assert!(approx_eq(ease(0.0, Easing::ElasticIn), 0.0));
        assert!(approx_eq(ease(1.0, Easing::ElasticIn), 1.0));

        assert!(approx_eq(ease(0.0, Easing::ElasticOut), 0.0));
        assert!(approx_eq(ease(1.0, Easing::ElasticOut), 1.0));
    }

    #[test]
    fn test_ease_back() {
        assert!(approx_eq(ease(0.0, Easing::BackIn), 0.0));
        assert!(approx_eq(ease(1.0, Easing::BackIn), 1.0));

        // Back should overshoot
        let mid_back_out = ease(0.5, Easing::BackOut);
        assert!(mid_back_out > 0.5); // Overshoots at midpoint
    }

    #[test]
    fn test_ease_bounce() {
        assert!(approx_eq(ease(0.0, Easing::BounceOut), 0.0));
        assert!(approx_eq(ease(1.0, Easing::BounceOut), 1.0));

        assert!(approx_eq(ease(0.0, Easing::BounceIn), 0.0));
        assert!(approx_eq(ease(1.0, Easing::BounceIn), 1.0));
    }

    #[test]
    fn test_ease_clamps_input() {
        // Values outside 0-1 should be clamped
        assert!(approx_eq(ease(-0.5, Easing::Linear), 0.0));
        assert!(approx_eq(ease(1.5, Easing::Linear), 1.0));
    }

    #[test]
    fn test_tween_new() {
        let tween = Tween::new(0.0, 100.0, 1.0, Easing::Linear);

        assert_eq!(tween.start(), 0.0);
        assert_eq!(tween.end(), 100.0);
        assert_eq!(tween.duration(), 1.0);
        assert_eq!(tween.elapsed(), 0.0);
        assert!(!tween.is_complete());
    }

    #[test]
    fn test_tween_value() {
        let tween = Tween::new(0.0, 100.0, 1.0, Easing::Linear);

        assert!(approx_eq(tween.value(), 0.0));
    }

    #[test]
    fn test_tween_update() {
        let mut tween = Tween::new(0.0, 100.0, 1.0, Easing::Linear);

        tween.update(0.5);
        assert!(approx_eq(tween.progress(), 0.5));
        assert!(approx_eq(tween.value(), 50.0));
        assert!(!tween.is_complete());

        tween.update(0.5);
        assert!(approx_eq(tween.progress(), 1.0));
        assert!(approx_eq(tween.value(), 100.0));
        assert!(tween.is_complete());
    }

    #[test]
    fn test_tween_with_easing() {
        let mut tween = Tween::new(0.0, 100.0, 1.0, Easing::QuadIn);

        tween.update(0.5);
        // QuadIn at 0.5 = 0.25, so value should be 25
        assert!(approx_eq(tween.value(), 25.0));
    }

    #[test]
    fn test_tween_reset() {
        let mut tween = Tween::new(0.0, 100.0, 1.0, Easing::Linear);

        tween.update(1.0);
        assert!(tween.is_complete());

        tween.reset();
        assert!(!tween.is_complete());
        assert_eq!(tween.elapsed(), 0.0);
    }

    #[test]
    fn test_tween_reverse() {
        let mut tween = Tween::new(0.0, 100.0, 1.0, Easing::Linear);

        tween.update(1.0);
        tween.reverse();

        assert_eq!(tween.start(), 100.0);
        assert_eq!(tween.end(), 0.0);
        assert_eq!(tween.elapsed(), 0.0);
    }

    #[test]
    fn test_tween_retarget() {
        let mut tween = Tween::new(0.0, 100.0, 1.0, Easing::Linear);

        tween.update(0.5);
        let current = tween.value();
        tween.retarget(200.0);

        assert!(approx_eq(tween.start(), current));
        assert_eq!(tween.end(), 200.0);
        assert_eq!(tween.elapsed(), 0.0);
    }

    #[test]
    fn test_lerp() {
        assert!(approx_eq(lerp(0.0, 100.0, 0.0), 0.0));
        assert!(approx_eq(lerp(0.0, 100.0, 0.5), 50.0));
        assert!(approx_eq(lerp(0.0, 100.0, 1.0), 100.0));

        // Should clamp
        assert!(approx_eq(lerp(0.0, 100.0, -0.5), 0.0));
        assert!(approx_eq(lerp(0.0, 100.0, 1.5), 100.0));
    }

    #[test]
    fn test_inverse_lerp() {
        assert!(approx_eq(inverse_lerp(0.0, 100.0, 0.0), 0.0));
        assert!(approx_eq(inverse_lerp(0.0, 100.0, 50.0), 0.5));
        assert!(approx_eq(inverse_lerp(0.0, 100.0, 100.0), 1.0));

        // Edge case: start == end
        assert!(approx_eq(inverse_lerp(50.0, 50.0, 50.0), 0.0));
    }

    #[test]
    fn test_remap() {
        // Remap 0-10 to 0-100
        assert!(approx_eq(remap(5.0, 0.0, 10.0, 0.0, 100.0), 50.0));

        // Remap with different ranges
        assert!(approx_eq(remap(0.5, 0.0, 1.0, 100.0, 200.0), 150.0));
    }

    #[test]
    fn test_interpolate() {
        let result = interpolate(0.0, 100.0, 0.5, Easing::QuadIn);
        assert!(approx_eq(result, 25.0)); // QuadIn at 0.5 = 0.25
    }

    #[test]
    fn test_tween_zero_duration() {
        let tween = Tween::new(0.0, 100.0, 0.0, Easing::Linear);

        // Zero duration should immediately complete
        assert!(approx_eq(tween.progress(), 1.0));
        assert!(approx_eq(tween.value(), 100.0));
    }

    #[test]
    fn test_easing_default() {
        let easing = Easing::default();
        assert_eq!(easing, Easing::Linear);
    }

    // ========================================================================
    // Edge Case Tests (Expert+ Audit Phase 2)
    // ========================================================================

    #[test]
    fn test_tween_negative_duration() {
        let tween = Tween::new(0.0, 100.0, -1.0, Easing::Linear);

        // Negative duration should behave like zero duration
        assert!(approx_eq(tween.progress(), 1.0));
        assert!(approx_eq(tween.value(), 100.0));
    }

    #[test]
    fn test_tween_very_small_duration() {
        let tween = Tween::new(0.0, 100.0, 0.0001, Easing::Linear);

        // Very small duration should work correctly
        assert!(!tween.is_complete());
        assert!(approx_eq(tween.progress(), 0.0));
    }

    #[test]
    fn test_tween_update_past_completion() {
        let mut tween = Tween::new(0.0, 100.0, 1.0, Easing::Linear);

        // Update past completion
        tween.update(2.0);
        assert!(tween.is_complete());
        assert!(approx_eq(tween.value(), 100.0));

        // Further updates should return false
        assert!(!tween.update(0.5));
        assert!(tween.is_complete());
    }

    #[test]
    fn test_tween_update_negative_dt() {
        let mut tween = Tween::new(0.0, 100.0, 1.0, Easing::Linear);

        // Update with positive dt first
        tween.update(0.5);
        assert!(approx_eq(tween.progress(), 0.5));

        // Update with negative dt - should still add (allowing time reversal if needed)
        tween.update(-0.3);
        // Progress is clamped to 0-1 in the progress() function
        assert!(tween.progress() >= 0.0);
    }

    #[test]
    fn test_tween_same_start_end() {
        let mut tween = Tween::new(50.0, 50.0, 1.0, Easing::Linear);

        tween.update(0.5);
        assert!(approx_eq(tween.value(), 50.0));

        tween.update(0.5);
        assert!(approx_eq(tween.value(), 50.0));
    }

    #[test]
    fn test_tween_reverse_direction() {
        let mut tween = Tween::new(100.0, 0.0, 1.0, Easing::Linear);

        tween.update(0.5);
        assert!(approx_eq(tween.value(), 50.0));

        tween.update(0.5);
        assert!(approx_eq(tween.value(), 0.0));
    }

    #[test]
    fn test_ease_all_functions_at_boundaries() {
        // All easing functions should return 0.0 at t=0.0 and 1.0 at t=1.0
        let easings = [
            Easing::Linear,
            Easing::QuadIn,
            Easing::QuadOut,
            Easing::QuadInOut,
            Easing::CubicIn,
            Easing::CubicOut,
            Easing::CubicInOut,
            Easing::QuartIn,
            Easing::QuartOut,
            Easing::QuartInOut,
            Easing::QuintIn,
            Easing::QuintOut,
            Easing::QuintInOut,
            Easing::SineIn,
            Easing::SineOut,
            Easing::SineInOut,
            Easing::ExpoIn,
            Easing::ExpoOut,
            Easing::ExpoInOut,
            Easing::CircIn,
            Easing::CircOut,
            Easing::CircInOut,
            Easing::ElasticIn,
            Easing::ElasticOut,
            Easing::ElasticInOut,
            Easing::BackIn,
            Easing::BackOut,
            Easing::BackInOut,
            Easing::BounceIn,
            Easing::BounceOut,
            Easing::BounceInOut,
        ];

        for easing in &easings {
            let at_0 = ease(0.0, *easing);
            let at_1 = ease(1.0, *easing);
            assert!(
                approx_eq(at_0, 0.0),
                "{easing:?} at t=0: expected 0.0, got {at_0}"
            );
            assert!(
                approx_eq(at_1, 1.0),
                "{easing:?} at t=1: expected 1.0, got {at_1}"
            );
        }
    }

    #[test]
    fn test_ease_in_out_symmetry() {
        // InOut functions should be symmetric around t=0.5
        let in_out_easings = [
            Easing::QuadInOut,
            Easing::CubicInOut,
            Easing::QuartInOut,
            Easing::QuintInOut,
            Easing::SineInOut,
            Easing::CircInOut,
        ];

        for easing in &in_out_easings {
            let at_half = ease(0.5, *easing);
            assert!(
                approx_eq(at_half, 0.5),
                "{easing:?} at t=0.5: expected 0.5, got {at_half}"
            );
        }
    }

    #[test]
    fn test_ease_overshoot_back() {
        // Back easing should overshoot
        let at_quarter = ease(0.25, Easing::BackIn);
        assert!(
            at_quarter < 0.0,
            "BackIn should undershoot at start: {at_quarter}"
        );

        let at_three_quarter = ease(0.75, Easing::BackOut);
        assert!(
            at_three_quarter > 1.0,
            "BackOut should overshoot at end: {at_three_quarter}"
        );
    }

    #[test]
    fn test_lerp_edge_cases() {
        // Large values
        assert!(approx_eq(lerp(0.0, 1_000_000.0, 0.5), 500_000.0));

        // Negative values
        assert!(approx_eq(lerp(-100.0, 100.0, 0.5), 0.0));

        // Negative range
        assert!(approx_eq(lerp(100.0, -100.0, 0.5), 0.0));
    }

    #[test]
    fn test_inverse_lerp_edge_cases() {
        // Value at start
        assert!(approx_eq(inverse_lerp(0.0, 100.0, 0.0), 0.0));

        // Value beyond range (should clamp)
        assert!(approx_eq(inverse_lerp(0.0, 100.0, 150.0), 1.0));
        assert!(approx_eq(inverse_lerp(0.0, 100.0, -50.0), 0.0));

        // Reverse range
        assert!(approx_eq(inverse_lerp(100.0, 0.0, 50.0), 0.5));
    }

    #[test]
    fn test_remap_edge_cases() {
        // Same range
        assert!(approx_eq(remap(50.0, 0.0, 100.0, 0.0, 100.0), 50.0));

        // Inverted output range
        assert!(approx_eq(remap(25.0, 0.0, 100.0, 100.0, 0.0), 75.0));

        // Very small input range
        assert!(approx_eq(remap(0.5, 0.0, 1.0, 0.0, 1000.0), 500.0));
    }

    #[test]
    fn test_interpolate_all_easings() {
        // Verify interpolate works with all easings
        let result_linear = interpolate(0.0, 100.0, 0.5, Easing::Linear);
        assert!(approx_eq(result_linear, 50.0));

        let result_cubic = interpolate(0.0, 100.0, 0.5, Easing::CubicIn);
        assert!(approx_eq(result_cubic, 12.5)); // 0.5^3 = 0.125
    }

    #[test]
    fn test_tween_linear_constructor() {
        let tween = Tween::linear(0.0, 100.0, 2.0);
        assert_eq!(tween.easing(), Easing::Linear);
        assert_eq!(tween.duration(), 2.0);
    }

    #[test]
    fn test_tween_ease_out_constructor() {
        let tween = Tween::ease_out(0.0, 100.0, 2.0);
        assert_eq!(tween.easing(), Easing::QuadOut);
    }

    #[test]
    fn test_tween_ease_in_out_constructor() {
        let tween = Tween::ease_in_out(0.0, 100.0, 2.0);
        assert_eq!(tween.easing(), Easing::QuadInOut);
    }

    #[test]
    fn test_tween_multiple_resets() {
        let mut tween = Tween::new(0.0, 100.0, 1.0, Easing::Linear);

        for _ in 0..3 {
            tween.update(1.0);
            assert!(tween.is_complete());
            tween.reset();
            assert!(!tween.is_complete());
            assert_eq!(tween.elapsed(), 0.0);
        }
    }

    #[test]
    fn test_tween_retarget_preserves_easing() {
        let mut tween = Tween::new(0.0, 100.0, 1.0, Easing::CubicInOut);

        tween.update(0.5);
        tween.retarget(200.0);

        assert_eq!(tween.easing(), Easing::CubicInOut);
        assert_eq!(tween.end(), 200.0);
    }

    #[test]
    fn test_bounce_characteristic() {
        // Bounce out should produce values between 0 and 1 (mostly)
        // and end at 1.0
        let at_end = ease(1.0, Easing::BounceOut);
        assert!(
            approx_eq(at_end, 1.0),
            "BounceOut at t=1.0 should be 1.0"
        );

        // Bounce should have valid intermediate values
        let at_half = ease(0.5, Easing::BounceOut);
        assert!(
            at_half > 0.5 && at_half < 1.0,
            "BounceOut at t=0.5 should be between 0.5 and 1.0: {at_half}"
        );
    }

    #[test]
    fn test_elastic_characteristic() {
        // Elastic easing should produce valid start and end values
        let at_start = ease(0.0, Easing::ElasticOut);
        let at_end = ease(1.0, Easing::ElasticOut);

        assert!(approx_eq(at_start, 0.0), "ElasticOut at t=0.0 should be 0.0");
        assert!(approx_eq(at_end, 1.0), "ElasticOut at t=1.0 should be 1.0");

        // Elastic out should overshoot at some point (value > 1.0)
        // Check at various points
        let mut found_overshoot = false;
        for i in 1..20 {
            let t = i as f32 / 20.0;
            let v = ease(t, Easing::ElasticOut);
            if v > 1.0 {
                found_overshoot = true;
                break;
            }
        }
        assert!(
            found_overshoot,
            "ElasticOut should overshoot 1.0 at some point"
        );
    }
}
