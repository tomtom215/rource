// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Frame statistics for wgpu renderer debugging and profiling.
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
//!
//! ## Compatibility
//!
//! This module provides the same API as the WebGL2 [`FrameStats`] for
//! consistent observability across backends. Field names use wgpu terminology
//! where appropriate (e.g., `pipeline_switches` instead of `program_switches`).

/// Bitflags for tracking which primitive types were rendered this frame.
///
/// This enables efficient tracking of active primitive types without
/// needing a separate boolean for each type.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
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
    /// Curves are active.
    pub const CURVES: u8 = 1 << 6;
    /// Texture array quads are active.
    pub const TEXTURE_ARRAYS: u8 = 1 << 7;

    /// Creates an empty set with no active primitives.
    #[inline]
    pub const fn none() -> Self {
        Self { bits: 0 }
    }

    /// Creates a set with all primitive types active.
    #[inline]
    pub const fn all() -> Self {
        Self {
            bits: Self::CIRCLES
                | Self::RINGS
                | Self::LINES
                | Self::QUADS
                | Self::TEXTURED_QUADS
                | Self::TEXT
                | Self::CURVES
                | Self::TEXTURE_ARRAYS,
        }
    }

    /// Sets a primitive type as active.
    #[inline]
    pub fn set(&mut self, flag: u8) {
        self.bits |= flag;
    }

    /// Clears a primitive type (sets inactive).
    #[inline]
    pub fn clear(&mut self, flag: u8) {
        self.bits &= !flag;
    }

    /// Returns whether a primitive type is active.
    #[inline]
    pub const fn is_set(&self, flag: u8) -> bool {
        (self.bits & flag) != 0
    }

    /// Returns the number of active primitive types.
    #[inline]
    pub const fn count(&self) -> u32 {
        self.bits.count_ones()
    }

    /// Returns whether any primitive types are active.
    #[inline]
    pub const fn any(&self) -> bool {
        self.bits != 0
    }

    /// Returns whether no primitive types are active.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.bits == 0
    }

    /// Returns the raw bits.
    #[inline]
    pub const fn bits(&self) -> u8 {
        self.bits
    }

    /// Creates from raw bits.
    #[inline]
    pub const fn from_bits(bits: u8) -> Self {
        Self { bits }
    }
}

/// Frame rendering statistics for the wgpu backend.
///
/// Contains metrics about the most recently rendered frame, useful for
/// performance debugging and optimization. This struct maintains API
/// compatibility with the WebGL2 `FrameStats` while using wgpu terminology.
///
/// ## Performance Interpretation
///
/// - **`draw_calls`**: Lower is better. With instanced rendering, this should
///   roughly equal the number of unique primitive/pipeline combinations.
/// - **`instances_per_draw_call()`**: Higher is better, indicating effective batching.
/// - **`batch_efficiency()`**: 1.0 is optimal, meaning no redundant pipeline switches.
/// - **`total_skipped_binds()`**: Higher indicates effective state caching.
#[derive(Debug, Clone, Copy, Default)]
pub struct FrameStats {
    /// Number of draw calls issued this frame.
    ///
    /// Lower is generally better. With instanced rendering, this should be
    /// roughly equal to the number of unique primitive/pipeline combinations
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

    /// Number of curve instances rendered.
    pub curve_instances: u32,

    /// Number of solid quad instances rendered.
    pub quad_instances: u32,

    /// Number of textured quad instances rendered.
    pub textured_quad_instances: u32,

    /// Number of text glyph instances rendered.
    pub text_instances: u32,

    /// Number of texture array quad instances rendered.
    pub texture_array_instances: u32,

    /// Number of render pipeline switches.
    ///
    /// In wgpu, this corresponds to `set_pipeline()` calls.
    pub pipeline_switches: u32,

    /// Number of bind group switches.
    ///
    /// In wgpu, this corresponds to `set_bind_group()` calls.
    pub bind_group_switches: u32,

    /// Number of texture binds (via bind groups).
    pub texture_binds: u32,

    /// Number of vertex buffer binds.
    pub vertex_buffer_binds: u32,

    /// Number of index buffer binds.
    pub index_buffer_binds: u32,

    /// Number of redundant pipeline binds skipped by state cache.
    pub skipped_pipeline_binds: u32,

    /// Number of redundant bind group binds skipped by state cache.
    pub skipped_bind_group_binds: u32,

    /// Number of redundant vertex buffer binds skipped by state cache.
    pub skipped_vertex_buffer_binds: u32,

    /// Which primitive types were rendered this frame.
    pub active_primitives: ActivePrimitives,

    /// Whether bloom effect was applied.
    pub bloom_applied: bool,

    /// Whether shadow effect was applied.
    pub shadow_applied: bool,

    /// Number of compute shader dispatches (for physics simulation).
    pub compute_dispatches: u32,

    /// Total entities processed by compute shaders.
    pub compute_entities: u32,

    /// Total bytes uploaded to GPU this frame.
    pub bytes_uploaded: u64,

    /// Total bytes downloaded from GPU this frame (rare, for readback).
    pub bytes_downloaded: u64,
}

impl FrameStats {
    /// Creates a new empty stats struct.
    #[inline]
    pub const fn new() -> Self {
        Self {
            draw_calls: 0,
            total_instances: 0,
            circle_instances: 0,
            ring_instances: 0,
            line_instances: 0,
            curve_instances: 0,
            quad_instances: 0,
            textured_quad_instances: 0,
            text_instances: 0,
            texture_array_instances: 0,
            pipeline_switches: 0,
            bind_group_switches: 0,
            texture_binds: 0,
            vertex_buffer_binds: 0,
            index_buffer_binds: 0,
            skipped_pipeline_binds: 0,
            skipped_bind_group_binds: 0,
            skipped_vertex_buffer_binds: 0,
            active_primitives: ActivePrimitives::none(),
            bloom_applied: false,
            shadow_applied: false,
            compute_dispatches: 0,
            compute_entities: 0,
            bytes_uploaded: 0,
            bytes_downloaded: 0,
        }
    }

    /// Resets all counters to zero for a new frame.
    #[inline]
    pub fn reset(&mut self) {
        *self = Self::new();
    }

    /// Returns the average instances per draw call.
    ///
    /// Higher is generally better, indicating effective batching.
    /// Returns 0.0 if no draw calls were made.
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
    /// `active_primitive_types / pipeline_switches`
    ///
    /// Perfect efficiency means `pipeline_switches` equals the number of active
    /// primitive types (no redundant switches).
    #[inline]
    pub fn batch_efficiency(&self) -> f32 {
        let active_count = self.active_primitives.count();
        if active_count == 0 || self.pipeline_switches == 0 {
            return 1.0; // No rendering = perfect efficiency
        }
        // Efficiency is optimal when pipeline_switches == active_count
        (active_count as f32 / self.pipeline_switches as f32).min(1.0)
    }

    /// Returns the number of redundant state changes avoided by caching.
    #[inline]
    pub const fn total_skipped_binds(&self) -> u32 {
        self.skipped_pipeline_binds
            + self.skipped_bind_group_binds
            + self.skipped_vertex_buffer_binds
    }

    /// Returns whether any post-processing effects were applied.
    #[inline]
    pub const fn has_post_processing(&self) -> bool {
        self.bloom_applied || self.shadow_applied
    }

    /// Returns whether any compute work was performed.
    #[inline]
    pub const fn has_compute(&self) -> bool {
        self.compute_dispatches > 0
    }

    /// Returns a human-readable summary string.
    ///
    /// Format: `Draws: N, Instances: N (N.N/draw), Pipelines: N, Compute: N`
    pub fn summary(&self) -> String {
        let mut s = format!(
            "Draws: {}, Instances: {} ({:.1}/draw), Pipelines: {}",
            self.draw_calls,
            self.total_instances,
            self.instances_per_draw_call(),
            self.pipeline_switches,
        );

        if self.compute_dispatches > 0 {
            use std::fmt::Write;
            let _ = write!(s, ", Compute: {}", self.compute_dispatches);
        }

        s
    }

    /// Returns a detailed summary string with all statistics.
    ///
    /// Includes all metrics separated by ` | ` for easy parsing.
    pub fn detailed_summary(&self) -> String {
        let mut parts = vec![
            format!("Draw calls: {}", self.draw_calls),
            format!("Total instances: {}", self.total_instances),
            format!("Instances/draw: {:.1}", self.instances_per_draw_call()),
            format!("Active primitives: {}", self.active_primitives.count()),
            format!("Pipeline switches: {}", self.pipeline_switches),
            format!("Bind group switches: {}", self.bind_group_switches),
            format!("Texture binds: {}", self.texture_binds),
            format!("Batch efficiency: {:.1}%", self.batch_efficiency() * 100.0),
            format!(
                "Skipped binds: {} (pipe: {}, bg: {}, vb: {})",
                self.total_skipped_binds(),
                self.skipped_pipeline_binds,
                self.skipped_bind_group_binds,
                self.skipped_vertex_buffer_binds
            ),
        ];

        if self.compute_dispatches > 0 {
            parts.push(format!(
                "Compute: {} dispatches, {} entities",
                self.compute_dispatches, self.compute_entities
            ));
        }

        if self.bytes_uploaded > 0 || self.bytes_downloaded > 0 {
            parts.push(format!(
                "Transfer: {} up, {} down",
                format_bytes(self.bytes_uploaded),
                format_bytes(self.bytes_downloaded)
            ));
        }

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

    /// Records a draw call with the given instance count.
    #[inline]
    pub fn record_draw(&mut self, instances: u32) {
        self.draw_calls += 1;
        self.total_instances += instances;
    }

    /// Records circle instances.
    #[inline]
    pub fn record_circles(&mut self, count: u32) {
        self.circle_instances += count;
        self.active_primitives.set(ActivePrimitives::CIRCLES);
    }

    /// Records ring instances.
    #[inline]
    pub fn record_rings(&mut self, count: u32) {
        self.ring_instances += count;
        self.active_primitives.set(ActivePrimitives::RINGS);
    }

    /// Records line instances.
    #[inline]
    pub fn record_lines(&mut self, count: u32) {
        self.line_instances += count;
        self.active_primitives.set(ActivePrimitives::LINES);
    }

    /// Records quad instances.
    #[inline]
    pub fn record_quads(&mut self, count: u32) {
        self.quad_instances += count;
        self.active_primitives.set(ActivePrimitives::QUADS);
    }

    /// Records textured quad instances.
    #[inline]
    pub fn record_textured_quads(&mut self, count: u32) {
        self.textured_quad_instances += count;
        self.active_primitives.set(ActivePrimitives::TEXTURED_QUADS);
    }

    /// Records text instances.
    #[inline]
    pub fn record_text(&mut self, count: u32) {
        self.text_instances += count;
        self.active_primitives.set(ActivePrimitives::TEXT);
    }

    /// Records texture array instances.
    #[inline]
    pub fn record_texture_arrays(&mut self, count: u32) {
        self.texture_array_instances += count;
        self.active_primitives.set(ActivePrimitives::TEXTURE_ARRAYS);
    }

    /// Records a compute dispatch.
    #[inline]
    pub fn record_compute(&mut self, entities: u32) {
        self.compute_dispatches += 1;
        self.compute_entities += entities;
    }

    /// Records bytes uploaded to GPU.
    #[inline]
    pub fn record_upload(&mut self, bytes: u64) {
        self.bytes_uploaded += bytes;
    }

    /// Records bytes downloaded from GPU.
    #[inline]
    pub fn record_download(&mut self, bytes: u64) {
        self.bytes_downloaded += bytes;
    }
}

/// Formats bytes in human-readable form (KB, MB, etc.).
fn format_bytes(bytes: u64) -> String {
    const KB: u64 = 1024;
    const MB: u64 = 1024 * KB;
    const GB: u64 = 1024 * MB;

    if bytes >= GB {
        format!("{:.2} GB", bytes as f64 / GB as f64)
    } else if bytes >= MB {
        format!("{:.2} MB", bytes as f64 / MB as f64)
    } else if bytes >= KB {
        format!("{:.2} KB", bytes as f64 / KB as f64)
    } else {
        format!("{bytes} B")
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
        assert!(!stats.bloom_applied);
        assert!(!stats.shadow_applied);
    }

    #[test]
    fn test_frame_stats_reset() {
        let mut stats = FrameStats {
            draw_calls: 10,
            total_instances: 1000,
            bloom_applied: true,
            ..Default::default()
        };

        stats.reset();

        assert_eq!(stats.draw_calls, 0);
        assert_eq!(stats.total_instances, 0);
        assert!(!stats.bloom_applied);
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
    fn test_instances_per_draw_call_zero_draws() {
        let stats = FrameStats::new();
        assert!((stats.instances_per_draw_call() - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_summary() {
        let stats = FrameStats {
            draw_calls: 6,
            total_instances: 1000,
            pipeline_switches: 6,
            ..Default::default()
        };

        let summary = stats.summary();
        assert!(summary.contains("Draws: 6"));
        assert!(summary.contains("Instances: 1000"));
        assert!(summary.contains("Pipelines: 6"));
    }

    #[test]
    fn test_summary_with_compute() {
        let stats = FrameStats {
            draw_calls: 6,
            total_instances: 1000,
            pipeline_switches: 6,
            compute_dispatches: 2,
            ..Default::default()
        };

        let summary = stats.summary();
        assert!(summary.contains("Compute: 2"));
    }

    #[test]
    fn test_active_primitives_none() {
        let active = ActivePrimitives::none();
        assert!(!active.any());
        assert!(active.is_empty());
        assert_eq!(active.count(), 0);
    }

    #[test]
    fn test_active_primitives_all() {
        let active = ActivePrimitives::all();
        assert!(active.any());
        assert!(!active.is_empty());
        assert_eq!(active.count(), 8);
    }

    #[test]
    fn test_active_primitives_set_and_is_set() {
        let mut active = ActivePrimitives::none();
        assert!(!active.is_set(ActivePrimitives::CIRCLES));

        active.set(ActivePrimitives::CIRCLES);
        assert!(active.is_set(ActivePrimitives::CIRCLES));
        assert!(!active.is_set(ActivePrimitives::LINES));
        assert_eq!(active.count(), 1);

        active.set(ActivePrimitives::LINES);
        active.set(ActivePrimitives::TEXT);
        assert_eq!(active.count(), 3);
    }

    #[test]
    fn test_active_primitives_clear() {
        let mut active = ActivePrimitives::all();
        assert_eq!(active.count(), 8);

        active.clear(ActivePrimitives::CIRCLES);
        assert!(!active.is_set(ActivePrimitives::CIRCLES));
        assert_eq!(active.count(), 7);
    }

    #[test]
    fn test_active_primitives_bits_roundtrip() {
        let mut active = ActivePrimitives::none();
        active.set(ActivePrimitives::CIRCLES);
        active.set(ActivePrimitives::TEXT);

        let bits = active.bits();
        let restored = ActivePrimitives::from_bits(bits);
        assert_eq!(active, restored);
    }

    #[test]
    fn test_batch_efficiency_no_rendering() {
        let stats = FrameStats::new();
        assert!((stats.batch_efficiency() - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_batch_efficiency_optimal() {
        let mut stats = FrameStats {
            pipeline_switches: 3,
            ..Default::default()
        };
        stats.active_primitives.set(ActivePrimitives::CIRCLES);
        stats.active_primitives.set(ActivePrimitives::LINES);
        stats.active_primitives.set(ActivePrimitives::TEXT);
        assert!((stats.batch_efficiency() - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_batch_efficiency_suboptimal() {
        let mut stats = FrameStats {
            pipeline_switches: 6,
            ..Default::default()
        };
        stats.active_primitives.set(ActivePrimitives::CIRCLES);
        stats.active_primitives.set(ActivePrimitives::LINES);
        stats.active_primitives.set(ActivePrimitives::TEXT);
        assert!((stats.batch_efficiency() - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_total_skipped_binds() {
        let stats = FrameStats {
            skipped_pipeline_binds: 10,
            skipped_bind_group_binds: 5,
            skipped_vertex_buffer_binds: 3,
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
    fn test_has_compute() {
        let mut stats = FrameStats::new();
        assert!(!stats.has_compute());

        stats.compute_dispatches = 1;
        assert!(stats.has_compute());
    }

    #[test]
    fn test_detailed_summary() {
        let mut stats = FrameStats {
            draw_calls: 6,
            total_instances: 1000,
            pipeline_switches: 6,
            bind_group_switches: 6,
            texture_binds: 2,
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

    #[test]
    fn test_detailed_summary_with_transfer() {
        let stats = FrameStats {
            bytes_uploaded: 1024 * 1024, // 1 MB
            bytes_downloaded: 512,
            ..Default::default()
        };

        let summary = stats.detailed_summary();
        assert!(summary.contains("Transfer:"));
        assert!(summary.contains("MB"));
    }

    #[test]
    fn test_record_draw() {
        let mut stats = FrameStats::new();
        stats.record_draw(100);
        stats.record_draw(50);

        assert_eq!(stats.draw_calls, 2);
        assert_eq!(stats.total_instances, 150);
    }

    #[test]
    fn test_record_primitives() {
        let mut stats = FrameStats::new();
        stats.record_circles(10);
        stats.record_rings(5);
        stats.record_lines(20);
        stats.record_quads(15);
        stats.record_textured_quads(8);
        stats.record_text(100);

        assert_eq!(stats.circle_instances, 10);
        assert_eq!(stats.ring_instances, 5);
        assert_eq!(stats.line_instances, 20);
        assert_eq!(stats.quad_instances, 15);
        assert_eq!(stats.textured_quad_instances, 8);
        assert_eq!(stats.text_instances, 100);
        assert_eq!(stats.active_primitives.count(), 6);
    }

    #[test]
    fn test_record_compute() {
        let mut stats = FrameStats::new();
        stats.record_compute(1000);
        stats.record_compute(500);

        assert_eq!(stats.compute_dispatches, 2);
        assert_eq!(stats.compute_entities, 1500);
    }

    #[test]
    fn test_record_upload_download() {
        let mut stats = FrameStats::new();
        stats.record_upload(1024);
        stats.record_upload(2048);
        stats.record_download(512);

        assert_eq!(stats.bytes_uploaded, 3072);
        assert_eq!(stats.bytes_downloaded, 512);
    }

    #[test]
    fn test_format_bytes() {
        assert_eq!(format_bytes(0), "0 B");
        assert_eq!(format_bytes(512), "512 B");
        assert_eq!(format_bytes(1024), "1.00 KB");
        assert_eq!(format_bytes(1536), "1.50 KB");
        assert_eq!(format_bytes(1024 * 1024), "1.00 MB");
        assert_eq!(format_bytes(1024 * 1024 * 1024), "1.00 GB");
    }

    #[test]
    fn test_frame_stats_default() {
        let stats = FrameStats::default();
        let new_stats = FrameStats::new();

        assert_eq!(stats.draw_calls, new_stats.draw_calls);
        assert_eq!(stats.total_instances, new_stats.total_instances);
        assert_eq!(
            stats.active_primitives.bits(),
            new_stats.active_primitives.bits()
        );
    }
}
