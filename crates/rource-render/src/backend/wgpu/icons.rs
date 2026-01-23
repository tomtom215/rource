//! Procedural file icon generator (re-exports from shared module).
//!
//! This module re-exports the shared icon generation functions from
//! [`crate::backend::icons`]. See that module for detailed documentation.
//!
//! # Usage
//!
//! ```ignore
//! use rource_render::backend::wgpu::icons::{generate_icon, ICON_SIZE};
//! use rource_math::Color;
//!
//! let icon_data = generate_icon(Color::from_rgb8(222, 165, 132)); // Rust orange
//! assert_eq!(icon_data.len(), ICON_SIZE * ICON_SIZE * 4);
//! ```

// Re-export all icon generation functions from the shared module
pub use crate::backend::icons::{
    common_extensions, generate_circle_icon, generate_common_icons, generate_default_icon,
    generate_icon, ICON_SIZE,
};
