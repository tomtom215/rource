// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! GPU physics dispatch methods for the wgpu renderer.
//!
//! This module contains methods for running force-directed physics simulation on the GPU.
//!
//! ## Algorithm Selection
//!
//! By default, the renderer uses the O(N) spatial hash algorithm which provides
//! dramatically better performance for large entity counts:
//!
//! | Entities | O(N²) Comparisons | O(N) Comparisons | Speedup |
//! |----------|-------------------|------------------|---------|
//! | 1,000 | 1,000,000 | ~10,800 | ~93× |
//! | 5,000 | 25,000,000 | ~54,000 | ~463× |
//!
//! Use `set_use_spatial_hash(false)` to fall back to the O(N²) brute force algorithm.

use super::{
    compute::{ComputeEntity, ComputePipeline, ComputeStats, PhysicsConfig},
    spatial_hash::SpatialHashPipeline,
    WgpuRenderer,
};

#[cfg(not(target_arch = "wasm32"))]
use super::compute::ComputedBounds;

impl WgpuRenderer {
    /// Returns whether O(N) spatial hash physics is enabled.
    ///
    /// When true (default), uses the O(N) spatial hash algorithm.
    /// When false, uses O(N²) brute force for compatibility testing.
    #[must_use]
    pub fn use_spatial_hash(&self) -> bool {
        self.use_spatial_hash
    }

    /// Sets whether to use O(N) spatial hash physics.
    ///
    /// # Arguments
    ///
    /// * `enabled` - `true` for O(N) spatial hash (default), `false` for O(N²) brute force
    pub fn set_use_spatial_hash(&mut self, enabled: bool) {
        self.use_spatial_hash = enabled;
    }

    /// Returns a reference to the spatial hash pipeline, creating it if needed.
    pub fn spatial_hash_pipeline(&mut self) -> &mut SpatialHashPipeline {
        if self.spatial_hash_pipeline.is_none() {
            self.spatial_hash_pipeline = Some(SpatialHashPipeline::new(&self.device));
        }
        self.spatial_hash_pipeline.as_mut().unwrap()
    }

    /// Returns a reference to the compute pipeline (O(N²)), creating it if needed.
    pub fn compute_pipeline(&mut self) -> &mut ComputePipeline {
        if self.compute_pipeline.is_none() {
            self.compute_pipeline = Some(ComputePipeline::new(&self.device));
        }
        self.compute_pipeline.as_mut().unwrap()
    }

    /// Warms up the GPU physics compute pipeline.
    ///
    /// Call this during initialization to pre-compile compute shaders and avoid
    /// first-frame stuttering when physics is first dispatched.
    ///
    /// Warms up the O(N) spatial hash pipeline by default. Use `warmup_physics_legacy()`
    /// to warm up the O(N²) pipeline instead.
    pub fn warmup_physics(&mut self) {
        if self.use_spatial_hash {
            // Warm up O(N) spatial hash pipeline (default)
            if self.spatial_hash_pipeline.is_none() {
                self.spatial_hash_pipeline = Some(SpatialHashPipeline::new(&self.device));
            }
            if let Some(ref mut pipeline) = self.spatial_hash_pipeline {
                pipeline.warmup(&self.device, &self.queue);
            }
        } else {
            // Warm up O(N²) legacy pipeline
            self.warmup_physics_legacy();
        }
    }

    /// Warms up the O(N²) brute force physics pipeline.
    ///
    /// This is the legacy pipeline. Use `warmup_physics()` for the O(N) spatial hash.
    pub fn warmup_physics_legacy(&mut self) {
        if self.compute_pipeline.is_none() {
            self.compute_pipeline = Some(ComputePipeline::new(&self.device));
        }
        if let Some(ref mut pipeline) = self.compute_pipeline {
            pipeline.warmup(&self.device, &self.queue);
        }
    }

    /// Runs GPU physics simulation synchronously.
    ///
    /// This method performs a complete physics simulation step on the GPU:
    /// 1. Uploads entity data to GPU buffers
    /// 2. Dispatches compute shaders (spatial hash, forces, integration)
    /// 3. Downloads updated positions back to CPU
    ///
    /// # Arguments
    ///
    /// * `entities` - Slice of entities to simulate
    /// * `delta_time` - Time step in seconds
    ///
    /// # Returns
    ///
    /// Vector of updated entities with new positions and velocities.
    ///
    /// # Example
    ///
    /// ```ignore
    /// use rource_render::backend::wgpu::{WgpuRenderer, ComputeEntity};
    ///
    /// let mut renderer = WgpuRenderer::new_headless(800, 600)?;
    ///
    /// // Create entities from scene data
    /// let entities: Vec<ComputeEntity> = scene_nodes.iter()
    ///     .map(|node| ComputeEntity::new(node.x, node.y, node.radius))
    ///     .collect();
    ///
    /// // Run physics step
    /// let updated = renderer.dispatch_physics(&entities, 0.016);
    ///
    /// // Apply updated positions back to scene
    /// for (node, entity) in scene_nodes.iter_mut().zip(updated.iter()) {
    ///     node.set_position(entity.position[0], entity.position[1]);
    /// }
    /// ```
    #[cfg(not(target_arch = "wasm32"))]
    pub fn dispatch_physics(
        &mut self,
        entities: &[ComputeEntity],
        delta_time: f32,
    ) -> Vec<ComputeEntity> {
        if entities.is_empty() {
            return Vec::new();
        }

        if self.use_spatial_hash {
            // Use O(N) spatial hash pipeline (default)
            self.dispatch_physics_spatial_hash(entities, delta_time)
        } else {
            // Use O(N²) brute force pipeline (legacy)
            self.dispatch_physics_brute_force(entities, delta_time)
        }
    }

    /// Dispatches physics using O(N) spatial hash algorithm.
    #[cfg(not(target_arch = "wasm32"))]
    fn dispatch_physics_spatial_hash(
        &mut self,
        entities: &[ComputeEntity],
        delta_time: f32,
    ) -> Vec<ComputeEntity> {
        // Initialize spatial hash pipeline if needed
        if self.spatial_hash_pipeline.is_none() {
            self.spatial_hash_pipeline = Some(SpatialHashPipeline::new(&self.device));
        }

        let Some(ref mut pipeline) = self.spatial_hash_pipeline else {
            return entities.to_vec();
        };

        // Upload entities
        pipeline.upload_entities(&self.device, &self.queue, entities);

        // Create command encoder
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("Spatial Hash Physics Encoder"),
            });

        // Dispatch all 9 compute passes
        pipeline.dispatch(&mut encoder, &self.queue, delta_time);

        // Add copy command to the same encoder (batched submission)
        // This avoids a second command buffer submission for the copy.
        pipeline.prepare_readback(&self.device, &mut encoder);

        // Submit both compute and copy in one command buffer
        self.queue.submit(Some(encoder.finish()));

        // Download results (just map + poll, copy was already submitted)
        pipeline.download_entities_mapped(&self.device)
    }

    /// Dispatches physics using O(N²) brute force algorithm.
    #[cfg(not(target_arch = "wasm32"))]
    fn dispatch_physics_brute_force(
        &mut self,
        entities: &[ComputeEntity],
        delta_time: f32,
    ) -> Vec<ComputeEntity> {
        // Initialize compute pipeline if needed
        if self.compute_pipeline.is_none() {
            self.compute_pipeline = Some(ComputePipeline::new(&self.device));
        }

        let Some(ref mut pipeline) = self.compute_pipeline else {
            return entities.to_vec();
        };

        // Upload entities
        pipeline.upload_entities(&self.device, &self.queue, entities);

        // Create command encoder
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("Physics Compute Encoder"),
            });

        // Dispatch physics passes
        pipeline.dispatch(&mut encoder, &self.queue, delta_time);

        // Prepare readback
        pipeline.prepare_readback(&self.device, &mut encoder);

        // Submit and wait for completion
        self.queue.submit(Some(encoder.finish()));

        // Download results synchronously
        pipeline.download_entities(&self.device)
    }

    /// Runs GPU physics simulation and calculates bounds.
    ///
    /// Like `dispatch_physics`, but also calculates the bounding box of all entities
    /// after simulation. This is useful for camera fitting.
    ///
    /// # Arguments
    ///
    /// * `entities` - Slice of entities to simulate
    /// * `delta_time` - Time step in seconds
    ///
    /// # Returns
    ///
    /// Tuple of (updated entities, computed bounds).
    #[cfg(not(target_arch = "wasm32"))]
    pub fn dispatch_physics_with_bounds(
        &mut self,
        entities: &[ComputeEntity],
        delta_time: f32,
    ) -> (Vec<ComputeEntity>, ComputedBounds) {
        if entities.is_empty() {
            return (Vec::new(), ComputedBounds::default());
        }

        // Initialize compute pipeline if needed
        if self.compute_pipeline.is_none() {
            self.compute_pipeline = Some(ComputePipeline::new(&self.device));
        }

        let Some(ref mut pipeline) = self.compute_pipeline else {
            return (entities.to_vec(), ComputedBounds::default());
        };

        // Upload entities
        pipeline.upload_entities(&self.device, &self.queue, entities);

        // Create command encoder
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("Physics Compute Encoder"),
            });

        // Dispatch physics passes
        pipeline.dispatch(&mut encoder, &self.queue, delta_time);

        // Dispatch bounds calculation
        pipeline.dispatch_bounds(&mut encoder, &self.queue);

        // Prepare readback
        pipeline.prepare_readback(&self.device, &mut encoder);

        // Submit and wait for completion
        self.queue.submit(Some(encoder.finish()));

        // Download results synchronously
        let updated_entities = pipeline.download_entities(&self.device);

        // Get bounds from stats (bounds are calculated on GPU but we need to read them)
        // For now, calculate bounds from downloaded entities
        let bounds = if updated_entities.is_empty() {
            ComputedBounds::default()
        } else {
            let mut min_x = f32::MAX;
            let mut min_y = f32::MAX;
            let mut max_x = f32::MIN;
            let mut max_y = f32::MIN;

            for entity in &updated_entities {
                let (x, y) = entity.position();
                let r = entity.radius;
                min_x = min_x.min(x - r);
                min_y = min_y.min(y - r);
                max_x = max_x.max(x + r);
                max_y = max_y.max(y + r);
            }

            ComputedBounds {
                min: [min_x, min_y],
                max: [max_x, max_y],
            }
        };

        (updated_entities, bounds)
    }

    /// Runs GPU physics simulation asynchronously (WASM).
    ///
    /// This is the async version for WASM where GPU operations must be non-blocking.
    ///
    /// # Arguments
    ///
    /// * `entities` - Slice of entities to simulate
    /// * `delta_time` - Time step in seconds
    ///
    /// # Returns
    ///
    /// Vector of updated entities with new positions and velocities.
    #[cfg(target_arch = "wasm32")]
    pub async fn dispatch_physics_async(
        &mut self,
        entities: &[ComputeEntity],
        delta_time: f32,
    ) -> Vec<ComputeEntity> {
        if entities.is_empty() {
            return Vec::new();
        }

        // Initialize compute pipeline if needed
        if self.compute_pipeline.is_none() {
            self.compute_pipeline = Some(ComputePipeline::new(&self.device));
        }

        let Some(ref mut pipeline) = self.compute_pipeline else {
            return entities.to_vec();
        };

        // Upload entities
        pipeline.upload_entities(&self.device, &self.queue, entities);

        // Create command encoder
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("Physics Compute Encoder"),
            });

        // Dispatch physics passes
        pipeline.dispatch(&mut encoder, &self.queue, delta_time);

        // Prepare readback
        pipeline.prepare_readback(&self.device, &mut encoder);

        // Submit
        self.queue.submit(Some(encoder.finish()));

        // Download results asynchronously
        pipeline.download_entities_async(&self.device).await
    }

    /// Runs GPU physics simulation synchronously (WASM frame loop compatible).
    ///
    /// This is a synchronous version that uses device polling instead of async/await.
    /// Suitable for use in synchronous frame loops like `requestAnimationFrame` callbacks.
    ///
    /// # Arguments
    ///
    /// * `entities` - Slice of entities to simulate
    /// * `delta_time` - Time step in seconds
    ///
    /// # Returns
    ///
    /// Vector of updated entities with new positions and velocities.
    ///
    /// # Note
    ///
    /// This method blocks until the GPU completes. For most frame budgets (16ms @ 60fps),
    /// this is acceptable since GPU physics computation is typically fast (<1ms for 1000 entities).
    #[cfg(target_arch = "wasm32")]
    pub fn dispatch_physics_sync(
        &mut self,
        entities: &[ComputeEntity],
        delta_time: f32,
    ) -> Vec<ComputeEntity> {
        if entities.is_empty() {
            return Vec::new();
        }

        if self.use_spatial_hash {
            // Use O(N) spatial hash pipeline (default)
            self.dispatch_physics_sync_spatial_hash(entities, delta_time)
        } else {
            // Use O(N²) brute force pipeline (legacy)
            self.dispatch_physics_sync_brute_force(entities, delta_time)
        }
    }

    /// Dispatches physics synchronously using O(N) spatial hash algorithm (WASM).
    #[cfg(target_arch = "wasm32")]
    fn dispatch_physics_sync_spatial_hash(
        &mut self,
        entities: &[ComputeEntity],
        delta_time: f32,
    ) -> Vec<ComputeEntity> {
        // Initialize spatial hash pipeline if needed
        if self.spatial_hash_pipeline.is_none() {
            self.spatial_hash_pipeline = Some(SpatialHashPipeline::new(&self.device));
        }

        let Some(ref mut pipeline) = self.spatial_hash_pipeline else {
            return entities.to_vec();
        };

        // Upload entities
        pipeline.upload_entities(&self.device, &self.queue, entities);

        // Create command encoder
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("Spatial Hash Physics Encoder"),
            });

        // Dispatch all 9 compute passes
        pipeline.dispatch(&mut encoder, &self.queue, delta_time);

        // Add copy command to the same encoder (batched submission)
        // This avoids a second command buffer submission for the copy.
        pipeline.prepare_readback(&self.device, &mut encoder);

        // Submit both compute and copy in one command buffer
        self.queue.submit(Some(encoder.finish()));

        // Download results (just map + poll, copy was already submitted)
        pipeline.download_entities_mapped(&self.device)
    }

    /// Dispatches physics synchronously using O(N²) brute force algorithm (WASM).
    #[cfg(target_arch = "wasm32")]
    fn dispatch_physics_sync_brute_force(
        &mut self,
        entities: &[ComputeEntity],
        delta_time: f32,
    ) -> Vec<ComputeEntity> {
        // Initialize compute pipeline if needed
        if self.compute_pipeline.is_none() {
            self.compute_pipeline = Some(ComputePipeline::new(&self.device));
        }

        let Some(ref mut pipeline) = self.compute_pipeline else {
            return entities.to_vec();
        };

        // Upload entities
        pipeline.upload_entities(&self.device, &self.queue, entities);

        // Create command encoder
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("Physics Compute Encoder"),
            });

        // Dispatch physics passes
        pipeline.dispatch(&mut encoder, &self.queue, delta_time);

        // Prepare readback
        pipeline.prepare_readback(&self.device, &mut encoder);

        // Submit
        self.queue.submit(Some(encoder.finish()));

        // Download results synchronously using polling
        pipeline.download_entities_sync(&self.device)
    }

    /// Sets the GPU physics configuration.
    ///
    /// # Arguments
    ///
    /// * `config` - Physics configuration (repulsion, attraction, damping, etc.)
    ///
    /// Note: This sets the config on the currently active pipeline (spatial hash or brute force).
    pub fn set_physics_config(&mut self, config: PhysicsConfig) {
        if self.use_spatial_hash {
            // Set config on spatial hash pipeline
            if self.spatial_hash_pipeline.is_none() {
                self.spatial_hash_pipeline = Some(SpatialHashPipeline::new(&self.device));
            }
            if let Some(ref mut pipeline) = self.spatial_hash_pipeline {
                pipeline.set_config(config);
            }
        } else {
            // Set config on brute force pipeline
            if self.compute_pipeline.is_none() {
                self.compute_pipeline = Some(ComputePipeline::new(&self.device));
            }
            if let Some(ref mut pipeline) = self.compute_pipeline {
                pipeline.set_config(config);
            }
        }
    }

    /// Returns the current GPU physics configuration.
    ///
    /// Returns the config from the currently active pipeline.
    pub fn physics_config(&self) -> Option<&PhysicsConfig> {
        if self.use_spatial_hash {
            self.spatial_hash_pipeline
                .as_ref()
                .map(SpatialHashPipeline::config)
        } else {
            self.compute_pipeline.as_ref().map(ComputePipeline::config)
        }
    }

    /// Returns compute statistics from the last physics dispatch.
    ///
    /// Returns stats from the currently active pipeline.
    pub fn physics_stats(&self) -> Option<&ComputeStats> {
        if self.use_spatial_hash {
            self.spatial_hash_pipeline
                .as_ref()
                .map(SpatialHashPipeline::stats)
        } else {
            self.compute_pipeline.as_ref().map(ComputePipeline::stats)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_physics_config_presets() {
        let default = PhysicsConfig::default();
        let dense = PhysicsConfig::dense();
        let sparse = PhysicsConfig::sparse();

        assert!(dense.repulsion_strength > default.repulsion_strength);
        assert!(sparse.repulsion_strength < default.repulsion_strength);
    }

    #[test]
    fn test_compute_entity() {
        let entity = ComputeEntity::new(100.0, 200.0, 10.0);
        assert_eq!(entity.position(), (100.0, 200.0));
        assert_eq!(entity.radius, 10.0);

        let entity = entity.with_velocity(5.0, -3.0);
        assert_eq!(entity.velocity(), (5.0, -3.0));
    }
}
