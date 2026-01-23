// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Enhanced visual rendering helpers for Rource WASM.
//!
//! This module re-exports shared rendering utilities from `rource_render::visual`
//! that are used by the WASM render phases.
//!
//! ## Shared Rendering Code
//!
//! The core rendering functions (avatar drawing, beam effects, curved branches)
//! are defined in `rource_render::visual` and shared between CLI and WASM builds
//! to ensure visual parity.

// Re-export only the functions used by render_phases.rs
pub use rource_render::visual::{draw_action_beam, draw_avatar_shape, draw_curved_branch};

#[cfg(test)]
mod tests {
    use rource_math::Vec2;
    use rource_render::visual::{catmull_rom_spline, create_branch_curve};

    #[test]
    fn test_shared_visual_functions_accessible() {
        // Verify that shared visual functions are accessible from rource_render
        let points = vec![Vec2::new(0.0, 0.0), Vec2::new(10.0, 10.0)];
        let result = catmull_rom_spline(&points, 4);
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_branch_curve() {
        let start = Vec2::new(0.0, 0.0);
        let end = Vec2::new(100.0, 100.0);
        let curve = create_branch_curve(start, end, 0.4);
        assert!(curve.len() > 2);
    }
}
