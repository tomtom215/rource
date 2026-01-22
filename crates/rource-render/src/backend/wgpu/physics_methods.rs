//! GPU physics dispatch methods for the wgpu renderer.
//!
//! This module contains methods for running force-directed physics simulation on the GPU.

use super::{
    compute::{ComputeEntity, ComputePipeline, ComputeStats, ComputedBounds, PhysicsConfig},
    WgpuRenderer,
};

impl WgpuRenderer {
    /// Returns a reference to the compute pipeline, creating it if needed.
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
    pub fn warmup_physics(&mut self) {
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

    /// Sets the GPU physics configuration.
    ///
    /// # Arguments
    ///
    /// * `config` - Physics configuration (repulsion, attraction, damping, etc.)
    pub fn set_physics_config(&mut self, config: PhysicsConfig) {
        if self.compute_pipeline.is_none() {
            self.compute_pipeline = Some(ComputePipeline::new(&self.device));
        }
        if let Some(ref mut pipeline) = self.compute_pipeline {
            pipeline.set_config(config);
        }
    }

    /// Returns the current GPU physics configuration.
    pub fn physics_config(&self) -> Option<&PhysicsConfig> {
        self.compute_pipeline.as_ref().map(ComputePipeline::config)
    }

    /// Returns compute statistics from the last physics dispatch.
    pub fn physics_stats(&self) -> Option<&ComputeStats> {
        self.compute_pipeline.as_ref().map(ComputePipeline::stats)
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
