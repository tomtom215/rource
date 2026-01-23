//! Frame statistics for WebGL2 renderer debugging and profiling.
//!
//! This module provides statistics tracking for draw calls, instance counts,
//! and API call overhead. Statistics are collected per-frame and can be used
//! for performance analysis and optimization.
//!
//! ## Usage
//!
//! ```ignore
//! let stats = renderer.frame_stats();
//! println!("Draw calls: {}", stats.draw_calls);
//! println!("Total instances: {}", stats.total_instances);
//! println!("Batch efficiency: {:.1}%", stats.batch_efficiency() * 100.0);
//! ```

/// Bitflags for tracking which primitive types were rendered this frame.
#[derive(Debug, Clone, Copy, Default)]
pub struct ActivePrimitives {
    bits: u8,
}

impl ActivePrimitives {
    /// Circles are active.
    pub const CIRCLES: u8 = 1 << 0;
    /// Rings are active.
    pub const RINGS: u8 = 1 << 1;
    /// Lines are active.
    pub const LINES: u8 = 1 << 2;
    /// Solid quads are active.
    pub const QUADS: u8 = 1 << 3;
    /// Textured quads are active.
    pub const TEXTURED_QUADS: u8 = 1 << 4;
    /// Text glyphs are active.
    pub const TEXT: u8 = 1 << 5;
    /// Texture array quads (file icons) are active.
    pub const TEXTURE_ARRAYS: u8 = 1 << 6;

    /// Creates an empty set.
    #[inline]
    pub const fn none() -> Self {
        Self { bits: 0 }
    }

    /// Sets a primitive type as active.
    #[inline]
    pub fn set(&mut self, flag: u8) {
        self.bits |= flag;
    }

    /// Returns whether a primitive type is active.
    #[inline]
    pub fn is_set(&self, flag: u8) -> bool {
        (self.bits & flag) != 0
    }

    /// Returns the number of active primitive types.
    #[inline]
    pub fn count(&self) -> u32 {
        self.bits.count_ones()
    }

    /// Returns whether any primitive types are active.
    #[inline]
    pub fn any(&self) -> bool {
        self.bits != 0
    }

    /// Returns the raw bits.
    #[inline]
    pub fn bits(&self) -> u8 {
        self.bits
    }
}

/// Frame rendering statistics.
///
/// Contains metrics about the most recently rendered frame, useful for
/// performance debugging and optimization.
#[derive(Debug, Clone, Copy, Default)]
pub struct FrameStats {
    /// Number of draw calls issued this frame.
    ///
    /// Lower is generally better. With instanced rendering, this should be
    /// roughly equal to the number of unique primitive/shader combinations
    /// (circles, rings, lines, quads, textured quads, text).
    pub draw_calls: u32,

    /// Total number of instances rendered across all draw calls.
    ///
    /// This counts individual primitives: each circle, line, glyph, etc.
    pub total_instances: u32,

    /// Number of circle instances rendered.
    pub circle_instances: u32,

    /// Number of ring instances rendered.
    pub ring_instances: u32,

    /// Number of line instances rendered.
    pub line_instances: u32,

    /// Number of solid quad instances rendered.
    pub quad_instances: u32,

    /// Number of textured quad instances rendered (including text glyphs).
    pub textured_quad_instances: u32,

    /// Number of text glyph instances rendered.
    pub text_instances: u32,

    /// Number of texture array instances (file icons) rendered.
    pub texture_array_instances: u32,

    /// Number of uniform calls made (legacy mode only).
    ///
    /// In UBO mode, this should be 0 since uniforms are uploaded once via buffer.
    pub uniform_calls: u32,

    /// Number of shader program switches.
    pub program_switches: u32,

    /// Number of VAO switches.
    pub vao_switches: u32,

    /// Number of texture binds.
    pub texture_binds: u32,

    /// Whether UBO mode is active.
    pub ubo_enabled: bool,

    /// Number of redundant program binds skipped by state cache.
    pub skipped_program_binds: u32,

    /// Number of redundant VAO binds skipped by state cache.
    pub skipped_vao_binds: u32,

    /// Number of redundant texture binds skipped by state cache.
    pub skipped_texture_binds: u32,

    /// Which primitive types were rendered this frame.
    pub active_primitives: ActivePrimitives,

    /// Whether bloom effect was applied.
    pub bloom_applied: bool,

    /// Whether shadow effect was applied.
    pub shadow_applied: bool,
}

impl FrameStats {
    /// Creates a new empty stats struct.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Resets all counters to zero for a new frame.
    #[inline]
    pub fn reset(&mut self) {
        *self = Self {
            ubo_enabled: self.ubo_enabled,
            ..Self::default()
        };
    }

    /// Returns the average instances per draw call.
    ///
    /// Higher is generally better, indicating effective batching.
    #[inline]
    pub fn instances_per_draw_call(&self) -> f32 {
        if self.draw_calls == 0 {
            0.0
        } else {
            self.total_instances as f32 / self.draw_calls as f32
        }
    }

    /// Returns the batch efficiency as a ratio (0.0 - 1.0).
    ///
    /// This measures how effectively primitives are batched. Higher is better.
    /// A value of 1.0 means each draw call renders the maximum possible instances.
    ///
    /// The efficiency is calculated as:
    /// `active_primitive_types / program_switches`
    ///
    /// Perfect efficiency means `program_switches` equals the number of active
    /// primitive types (no redundant switches).
    #[inline]
    pub fn batch_efficiency(&self) -> f32 {
        let active_count = self.active_primitives.count();
        if active_count == 0 || self.program_switches == 0 {
            return 1.0; // No rendering = perfect efficiency
        }
        // Efficiency is optimal when program_switches == active_count
        (active_count as f32 / self.program_switches as f32).min(1.0)
    }

    /// Returns the number of redundant state changes avoided by caching.
    #[inline]
    pub fn total_skipped_binds(&self) -> u32 {
        self.skipped_program_binds + self.skipped_vao_binds + self.skipped_texture_binds
    }

    /// Returns whether any post-processing effects were applied.
    #[inline]
    pub fn has_post_processing(&self) -> bool {
        self.bloom_applied || self.shadow_applied
    }

    /// Returns a human-readable summary string.
    pub fn summary(&self) -> String {
        format!(
            "Draws: {}, Instances: {} ({:.1}/draw), Programs: {}, VAOs: {}, UBO: {}",
            self.draw_calls,
            self.total_instances,
            self.instances_per_draw_call(),
            self.program_switches,
            self.vao_switches,
            if self.ubo_enabled { "on" } else { "off" }
        )
    }

    /// Returns a detailed summary string with all statistics.
    pub fn detailed_summary(&self) -> String {
        let mut parts = vec![
            format!("Draw calls: {}", self.draw_calls),
            format!("Total instances: {}", self.total_instances),
            format!("Instances/draw: {:.1}", self.instances_per_draw_call()),
            format!("Active primitives: {}", self.active_primitives.count()),
            format!("Program switches: {}", self.program_switches),
            format!("VAO switches: {}", self.vao_switches),
            format!("Texture binds: {}", self.texture_binds),
            format!("Batch efficiency: {:.1}%", self.batch_efficiency() * 100.0),
            format!(
                "Skipped binds: {} (prog: {}, vao: {}, tex: {})",
                self.total_skipped_binds(),
                self.skipped_program_binds,
                self.skipped_vao_binds,
                self.skipped_texture_binds
            ),
            format!("UBO: {}", if self.ubo_enabled { "on" } else { "off" }),
        ];

        if self.bloom_applied || self.shadow_applied {
            let effects: Vec<&str> = [
                self.bloom_applied.then_some("bloom"),
                self.shadow_applied.then_some("shadow"),
            ]
            .into_iter()
            .flatten()
            .collect();
            parts.push(format!("Post-processing: {}", effects.join(", ")));
        }

        parts.join(" | ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_frame_stats_new() {
        let stats = FrameStats::new();
        assert_eq!(stats.draw_calls, 0);
        assert_eq!(stats.total_instances, 0);
        assert!(!stats.ubo_enabled);
    }

    #[test]
    fn test_frame_stats_reset() {
        let mut stats = FrameStats {
            draw_calls: 10,
            total_instances: 1000,
            ubo_enabled: true,
            ..Default::default()
        };

        stats.reset();

        assert_eq!(stats.draw_calls, 0);
        assert_eq!(stats.total_instances, 0);
        assert!(stats.ubo_enabled); // Should preserve ubo_enabled
    }

    #[test]
    fn test_instances_per_draw_call() {
        let mut stats = FrameStats::new();
        assert!((stats.instances_per_draw_call() - 0.0).abs() < 0.001);

        stats.draw_calls = 6;
        stats.total_instances = 1200;
        assert!((stats.instances_per_draw_call() - 200.0).abs() < 0.001);
    }

    #[test]
    fn test_summary() {
        let stats = FrameStats {
            draw_calls: 6,
            total_instances: 1000,
            program_switches: 6,
            vao_switches: 6,
            ubo_enabled: true,
            ..Default::default()
        };

        let summary = stats.summary();
        assert!(summary.contains("Draws: 6"));
        assert!(summary.contains("Instances: 1000"));
        assert!(summary.contains("UBO: on"));
    }

    #[test]
    fn test_active_primitives() {
        let mut active = ActivePrimitives::none();
        assert!(!active.any());
        assert_eq!(active.count(), 0);

        active.set(ActivePrimitives::CIRCLES);
        assert!(active.any());
        assert!(active.is_set(ActivePrimitives::CIRCLES));
        assert!(!active.is_set(ActivePrimitives::LINES));
        assert_eq!(active.count(), 1);

        active.set(ActivePrimitives::LINES);
        active.set(ActivePrimitives::TEXT);
        assert_eq!(active.count(), 3);
    }

    #[test]
    fn test_batch_efficiency() {
        // No rendering = perfect efficiency
        let stats = FrameStats::new();
        assert!((stats.batch_efficiency() - 1.0).abs() < 0.001);

        // Optimal: 3 active primitives, 3 program switches
        let mut stats = FrameStats {
            program_switches: 3,
            ..Default::default()
        };
        stats.active_primitives.set(ActivePrimitives::CIRCLES);
        stats.active_primitives.set(ActivePrimitives::LINES);
        stats.active_primitives.set(ActivePrimitives::TEXT);
        assert!((stats.batch_efficiency() - 1.0).abs() < 0.001);

        // Sub-optimal: 3 active primitives, 6 program switches
        stats.program_switches = 6;
        assert!((stats.batch_efficiency() - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_total_skipped_binds() {
        let stats = FrameStats {
            skipped_program_binds: 10,
            skipped_vao_binds: 5,
            skipped_texture_binds: 3,
            ..Default::default()
        };
        assert_eq!(stats.total_skipped_binds(), 18);
    }

    #[test]
    fn test_has_post_processing() {
        let mut stats = FrameStats::new();
        assert!(!stats.has_post_processing());

        stats.bloom_applied = true;
        assert!(stats.has_post_processing());

        stats.bloom_applied = false;
        stats.shadow_applied = true;
        assert!(stats.has_post_processing());
    }

    #[test]
    fn test_detailed_summary() {
        let mut stats = FrameStats {
            draw_calls: 6,
            total_instances: 1000,
            program_switches: 6,
            vao_switches: 6,
            texture_binds: 2,
            ubo_enabled: true,
            bloom_applied: true,
            ..Default::default()
        };
        stats.active_primitives.set(ActivePrimitives::CIRCLES);
        stats.active_primitives.set(ActivePrimitives::TEXT);

        let summary = stats.detailed_summary();
        assert!(summary.contains("Draw calls: 6"));
        assert!(summary.contains("Active primitives: 2"));
        assert!(summary.contains("bloom"));
    }
}
