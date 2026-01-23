//! GPU visibility culling methods for the wgpu renderer.
//!
//! This module contains methods for GPU-based visibility culling.
//!
//! ## Current Status
//!
//! The GPU visibility culling infrastructure is **complete** but **not integrated**
//! into the rendering pipeline. This is intentional for the following reasons:
//!
//! 1. **CPU quadtree culling is efficient for typical use cases** - The scene graph's
//!    quadtree provides O(log n) visibility queries that work well for < 10,000 entities.
//!
//! 2. **Integration requires buffer layout changes** - The `InstanceBuffer` uses VERTEX
//!    usage while the culling pipeline outputs to STORAGE buffers. Integrating requires
//!    either buffer copying or creating output buffers with both VERTEX and STORAGE usage.
//!
//! 3. **Indirect draw adds complexity** - Using `draw_indirect()` instead of `draw()`
//!    requires careful synchronization between compute and render passes.
//!
//! ## When to Consider GPU Culling Integration
//!
//! GPU culling becomes beneficial when:
//! - Scene has 10,000+ instances
//! - View bounds change every frame (continuous panning/zooming)
//! - CPU is already saturated with other work
//! - GPU compute overhead is offset by reduced draw call preparation
//!
//! ## Integration Steps (Future Work)
//!
//! To integrate GPU culling into the render pipeline:
//!
//! 1. **Modify `StorageBuffer` in `culling.rs`**:
//!    - Add VERTEX usage flag to output buffers
//!    - Create output buffers with: `STORAGE | VERTEX | COPY_DST`
//!
//! 2. **Add culling dispatch to `flush()`**:
//!    ```ignore
//!    // Before render pass, dispatch culling compute
//!    if self.gpu_culling_enabled {
//!        self.dispatch_culling(encoder);
//!    }
//!    ```
//!
//! 3. **Modify flush passes to use indirect draw**:
//!    ```ignore
//!    if let Some(culling) = &self.culling_pipeline {
//!        // Use culling output buffer as vertex buffer
//!        render_pass.set_vertex_buffer(1, culling.output_buffer().slice(..));
//!        // Use indirect draw for GPU-determined instance count
//!        render_pass.draw_indirect(culling.indirect_buffer(), 0);
//!    } else {
//!        // Normal path
//!        render_pass.set_vertex_buffer(1, self.circle_instances.buffer().slice(..));
//!        render_pass.draw(0..4, 0..instance_count);
//!    }
//!    ```
//!
//! 4. **Add synchronization barrier** between compute and render passes
//!
//! 5. **Track visible instance count** for statistics (requires readback or query)

use super::{
    culling::{CullingStats, VisibilityCullingPipeline},
    WgpuRenderer,
};

impl WgpuRenderer {
    /// Enables or disables GPU visibility culling.
    ///
    /// When enabled, the renderer will use GPU compute shaders to cull instances
    /// based on the current cull bounds before rendering. This is beneficial for
    /// extreme-scale scenarios (10,000+ instances) where CPU culling becomes a
    /// bottleneck.
    ///
    /// For most use cases, the default CPU-side quadtree culling is more efficient.
    ///
    /// # Arguments
    ///
    /// * `enabled` - Whether to enable GPU culling
    pub fn set_gpu_culling_enabled(&mut self, enabled: bool) {
        self.gpu_culling_enabled = enabled;
        if enabled && self.culling_pipeline.is_none() {
            self.culling_pipeline = Some(VisibilityCullingPipeline::new(&self.device));
        }
    }

    /// Returns whether GPU visibility culling is enabled.
    #[inline]
    pub fn is_gpu_culling_enabled(&self) -> bool {
        self.gpu_culling_enabled
    }

    /// Sets the view bounds for GPU visibility culling.
    ///
    /// Instances outside these bounds will be culled by the GPU compute shader.
    /// These bounds should match the camera's visible area in world coordinates.
    ///
    /// # Arguments
    ///
    /// * `min_x` - Minimum X coordinate
    /// * `min_y` - Minimum Y coordinate
    /// * `max_x` - Maximum X coordinate
    /// * `max_y` - Maximum Y coordinate
    pub fn set_cull_bounds(&mut self, min_x: f32, min_y: f32, max_x: f32, max_y: f32) {
        self.cull_bounds = [min_x, min_y, max_x, max_y];
        if let Some(ref mut pipeline) = self.culling_pipeline {
            pipeline.set_view_bounds(min_x, min_y, max_x, max_y);
        }
    }

    /// Returns the current cull bounds.
    #[inline]
    pub fn cull_bounds(&self) -> [f32; 4] {
        self.cull_bounds
    }

    /// Warms up the GPU visibility culling pipeline.
    ///
    /// Call this during initialization to pre-compile compute shaders and avoid
    /// first-frame stuttering when GPU culling is first enabled.
    pub fn warmup_culling(&mut self) {
        if self.culling_pipeline.is_none() {
            self.culling_pipeline = Some(VisibilityCullingPipeline::new(&self.device));
        }
        if let Some(ref mut pipeline) = self.culling_pipeline {
            pipeline.warmup(&self.device, &self.queue);
        }
    }

    /// Returns statistics from the last GPU culling operation.
    pub fn culling_stats(&self) -> Option<&CullingStats> {
        self.culling_pipeline
            .as_ref()
            .map(VisibilityCullingPipeline::stats)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cull_primitive_types() {
        use super::super::culling::CullPrimitive;
        // Verify primitive types have correct instance sizes
        assert_eq!(CullPrimitive::Circles.floats_per_instance(), 7);
        assert_eq!(CullPrimitive::Lines.floats_per_instance(), 9);
        assert_eq!(CullPrimitive::Quads.floats_per_instance(), 8);
    }

    #[test]
    fn test_culling_stats() {
        let mut stats = CullingStats::default();
        assert_eq!(stats.total_instances, 0);
        assert_eq!(stats.visible_instances, 0);
        assert_eq!(stats.dispatch_count, 0);

        // Empty stats should have 1.0 cull ratio (100% visible)
        assert!((stats.cull_ratio() - 1.0).abs() < 0.001);

        // Test with actual values
        stats.total_instances = 100;
        stats.visible_instances = 25;
        assert!((stats.cull_ratio() - 0.25).abs() < 0.001);
        assert!((stats.culled_percentage() - 75.0).abs() < 0.001);
    }

    #[test]
    fn test_culling_stats_reset() {
        let mut stats = CullingStats {
            total_instances: 100,
            visible_instances: 50,
            dispatch_count: 5,
        };

        stats.reset();
        assert_eq!(stats.total_instances, 0);
        assert_eq!(stats.visible_instances, 0);
        assert_eq!(stats.dispatch_count, 0);
    }
}
