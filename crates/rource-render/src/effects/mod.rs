//! Post-processing effects.
//!
//! This module provides CPU-efficient post-processing effects:
//! - [`Bloom`]: Glow effect for bright areas
//! - [`Shadow`]: Drop shadow effect (future)

pub mod bloom;

pub use bloom::BloomEffect;
