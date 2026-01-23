// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Post-processing effects.
//!
//! This module provides CPU-efficient post-processing effects:
//! - [`BloomEffect`]: Glow effect for bright areas
//! - [`ShadowEffect`]: Drop shadow effect for depth

pub mod bloom;
pub mod shadow;

pub use bloom::BloomEffect;
pub use shadow::ShadowEffect;
