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
//! ```

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
}
