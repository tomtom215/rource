// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Animation system for the visualization.
//!
//! This module provides:
//!
//! - **Tweening**: Smooth interpolation between values with easing functions
//! - **Splines**: Catmull-Rom spline interpolation for smooth curves
//!
//! # Example
//!
//! ```
//! use rource_core::animation::{Tween, Easing, ease};
//!
//! // Create a tween that animates from 0 to 100 over 1 second
//! let mut tween = Tween::new(0.0, 100.0, 1.0, Easing::QuadOut);
//!
//! // Update each frame (assuming 60 FPS)
//! tween.update(0.016);
//!
//! // Get the current value
//! let current = tween.value();
//! ```

pub mod spline;
pub mod tween;

pub use spline::{CatmullRomSpline, SplinePoint};
pub use tween::{ease, interpolate, inverse_lerp, lerp, remap, Easing, Tween};
