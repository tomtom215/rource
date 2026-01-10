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

use std::f32::consts::PI;

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
pub fn ease(t: f32, easing: Easing) -> f32 {
    let t = t.clamp(0.0, 1.0);

    match easing {
        Easing::Linear => t,

        // Quadratic
        Easing::QuadIn => t * t,
        Easing::QuadOut => 1.0 - (1.0 - t) * (1.0 - t),
        Easing::QuadInOut => {
            if t < 0.5 {
                2.0 * t * t
            } else {
                1.0 - (-2.0 * t + 2.0).powi(2) / 2.0
            }
        }

        // Cubic
        Easing::CubicIn => t * t * t,
        Easing::CubicOut => 1.0 - (1.0 - t).powi(3),
        Easing::CubicInOut => {
            if t < 0.5 {
                4.0 * t * t * t
            } else {
                1.0 - (-2.0 * t + 2.0).powi(3) / 2.0
            }
        }

        // Quartic
        Easing::QuartIn => t * t * t * t,
        Easing::QuartOut => 1.0 - (1.0 - t).powi(4),
        Easing::QuartInOut => {
            if t < 0.5 {
                8.0 * t.powi(4)
            } else {
                1.0 - (-2.0 * t + 2.0).powi(4) / 2.0
            }
        }

        // Quintic
        Easing::QuintIn => t.powi(5),
        Easing::QuintOut => 1.0 - (1.0 - t).powi(5),
        Easing::QuintInOut => {
            if t < 0.5 {
                16.0 * t.powi(5)
            } else {
                1.0 - (-2.0 * t + 2.0).powi(5) / 2.0
            }
        }

        // Sine
        Easing::SineIn => 1.0 - (t * PI / 2.0).cos(),
        Easing::SineOut => (t * PI / 2.0).sin(),
        Easing::SineInOut => (1.0 - (t * PI).cos()) / 2.0,

        // Exponential
        Easing::ExpoIn => {
            if t == 0.0 {
                0.0
            } else {
                2.0_f32.powf(10.0 * t - 10.0)
            }
        }
        Easing::ExpoOut => {
            if t == 1.0 {
                1.0
            } else {
                1.0 - 2.0_f32.powf(-10.0 * t)
            }
        }
        Easing::ExpoInOut => {
            if t == 0.0 {
                0.0
            } else if t == 1.0 {
                1.0
            } else if t < 0.5 {
                2.0_f32.powf(20.0 * t - 10.0) / 2.0
            } else {
                (2.0 - 2.0_f32.powf(-20.0 * t + 10.0)) / 2.0
            }
        }

        // Circular
        Easing::CircIn => 1.0 - (1.0 - t * t).sqrt(),
        Easing::CircOut => (1.0 - (t - 1.0).powi(2)).sqrt(),
        Easing::CircInOut => {
            if t < 0.5 {
                (1.0 - (1.0 - (2.0 * t).powi(2)).sqrt()) / 2.0
            } else {
                ((1.0 - (-2.0 * t + 2.0).powi(2)).sqrt() + 1.0) / 2.0
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
                (1.0 - bounce_out(1.0 - 2.0 * t)) / 2.0
            } else {
                (1.0 + bounce_out(2.0 * t - 1.0)) / 2.0
            }
        }
    }
}

// Elastic helper functions
const ELASTIC_C4: f32 = (2.0 * PI) / 3.0;
const ELASTIC_C5: f32 = (2.0 * PI) / 4.5;

fn elastic_in(t: f32) -> f32 {
    if t == 0.0 {
        0.0
    } else if t == 1.0 {
        1.0
    } else {
        -(2.0_f32.powf(10.0 * t - 10.0)) * ((t * 10.0 - 10.75) * ELASTIC_C4).sin()
    }
}

fn elastic_out(t: f32) -> f32 {
    if t == 0.0 {
        0.0
    } else if t == 1.0 {
        1.0
    } else {
        2.0_f32.powf(-10.0 * t) * ((t * 10.0 - 0.75) * ELASTIC_C4).sin() + 1.0
    }
}

fn elastic_in_out(t: f32) -> f32 {
    if t == 0.0 {
        0.0
    } else if t == 1.0 {
        1.0
    } else if t < 0.5 {
        -(2.0_f32.powf(20.0 * t - 10.0) * ((20.0 * t - 11.125) * ELASTIC_C5).sin()) / 2.0
    } else {
        (2.0_f32.powf(-20.0 * t + 10.0) * ((20.0 * t - 11.125) * ELASTIC_C5).sin()) / 2.0 + 1.0
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
    1.0 + BACK_C3 * (t - 1.0).powi(3) + BACK_C1 * (t - 1.0).powi(2)
}

fn back_in_out(t: f32) -> f32 {
    if t < 0.5 {
        ((2.0 * t).powi(2) * ((BACK_C2 + 1.0) * 2.0 * t - BACK_C2)) / 2.0
    } else {
        ((2.0 * t - 2.0).powi(2) * ((BACK_C2 + 1.0) * (t * 2.0 - 2.0) + BACK_C2) + 2.0) / 2.0
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
    pub const fn new(start: f32, end: f32, duration: f32, easing: Easing) -> Self {
        Self {
            start,
            end,
            duration,
            elapsed: 0.0,
            easing,
            complete: false,
        }
    }

    /// Creates a linear tween.
    #[must_use]
    pub const fn linear(start: f32, end: f32, duration: f32) -> Self {
        Self::new(start, end, duration, Easing::Linear)
    }

    /// Creates an ease-out tween (good for most UI animations).
    #[must_use]
    pub const fn ease_out(start: f32, end: f32, duration: f32) -> Self {
        Self::new(start, end, duration, Easing::QuadOut)
    }

    /// Creates an ease-in-out tween (smooth start and end).
    #[must_use]
    pub const fn ease_in_out(start: f32, end: f32, duration: f32) -> Self {
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
    #[must_use]
    pub fn progress(&self) -> f32 {
        if self.duration <= 0.0 {
            1.0
        } else {
            (self.elapsed / self.duration).clamp(0.0, 1.0)
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
}
