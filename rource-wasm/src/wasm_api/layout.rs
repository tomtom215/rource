//! Layout algorithm configuration.
//!
//! This module provides methods to configure the force-directed layout:
//! - Preset configurations for different repository sizes
//! - Fine-grained parameter control
//! - Automatic scaling based on repository statistics

use wasm_bindgen::prelude::*;

use rource_core::config::LayoutSettings;
use rource_core::scene::LayoutConfig;

use crate::Rource;

// ============================================================================
// Layout Configuration
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Configures the layout algorithm for a given repository size.
    ///
    /// This automatically computes optimal layout parameters based on
    /// repository statistics. Should be called after loading data or
    /// when repository characteristics are known.
    ///
    /// # Arguments
    /// * `file_count` - Total number of files
    /// * `max_depth` - Maximum directory depth (0 if unknown)
    /// * `dir_count` - Total number of directories (0 if unknown)
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.configureLayoutForRepo(50000, 12, 3000);
    /// ```
    #[wasm_bindgen(js_name = configureLayoutForRepo)]
    pub fn configure_layout_for_repo(
        &mut self,
        file_count: usize,
        max_depth: u32,
        dir_count: usize,
    ) {
        let settings = LayoutSettings::from_repo_stats(file_count, max_depth, dir_count);
        self.settings.layout = settings;

        // Also update the scene's layout config
        self.scene
            .configure_layout_for_repo(file_count, max_depth, dir_count);
    }

    /// Sets the layout preset for different repository sizes.
    ///
    /// # Presets
    /// * "small" - Repos < 1000 files (compact layout)
    /// * "medium" - Repos 1000-10000 files (default)
    /// * "large" - Repos 10000-50000 files (spread out)
    /// * "massive" - Repos 50000+ files (maximum spread)
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setLayoutPreset("massive");
    /// ```
    #[wasm_bindgen(js_name = setLayoutPreset)]
    pub fn set_layout_preset(&mut self, preset: &str) {
        let (layout_settings, layout_config) = match preset.to_lowercase().as_str() {
            "small" => (LayoutSettings::small_repo(), LayoutConfig::default()),
            "medium" => (LayoutSettings::medium_repo(), LayoutConfig::default()),
            "large" => (LayoutSettings::large_repo(), LayoutConfig::large_repo()),
            "massive" => (LayoutSettings::massive_repo(), LayoutConfig::massive_repo()),
            _ => return, // Unknown preset, ignore
        };

        self.settings.layout = layout_settings;
        self.scene.set_layout_config(layout_config);
    }

    /// Sets the radial distance scale for directory positioning.
    ///
    /// Higher values spread the tree outward more.
    /// Range: [40.0, 500.0], Default: 80.0
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setRadialDistanceScale(160.0);
    /// ```
    #[wasm_bindgen(js_name = setRadialDistanceScale)]
    pub fn set_radial_distance_scale(&mut self, scale: f32) {
        self.settings.layout.radial_distance_scale = scale.clamp(40.0, 500.0);
        let config = LayoutConfig::from_settings(&self.settings.layout);
        self.scene.set_layout_config(config);
    }

    /// Sets the depth distance exponent for non-linear depth scaling.
    ///
    /// Values > 1.0 add extra spacing at deeper levels.
    /// Range: [0.5, 2.0], Default: 1.0 (linear)
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setDepthDistanceExponent(1.3);
    /// ```
    #[wasm_bindgen(js_name = setDepthDistanceExponent)]
    pub fn set_depth_distance_exponent(&mut self, exponent: f32) {
        self.settings.layout.depth_distance_exponent = exponent.clamp(0.5, 2.0);
        let config = LayoutConfig::from_settings(&self.settings.layout);
        self.scene.set_layout_config(config);
    }

    /// Sets the branch depth fade rate.
    ///
    /// Higher values make deep branches fade faster.
    /// Range: [0.0, 1.0], Default: 0.3
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setBranchDepthFade(0.7);
    /// ```
    #[wasm_bindgen(js_name = setBranchDepthFade)]
    pub fn set_branch_depth_fade(&mut self, fade: f32) {
        self.settings.layout.branch_depth_fade = fade.clamp(0.0, 1.0);
    }

    /// Sets the maximum branch opacity.
    ///
    /// Controls visibility of directory-to-parent connections.
    /// Range: [0.0, 1.0], Default: 0.35
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// rource.setBranchOpacityMax(0.15);
    /// ```
    #[wasm_bindgen(js_name = setBranchOpacityMax)]
    pub fn set_branch_opacity_max(&mut self, opacity: f32) {
        self.settings.layout.branch_opacity_max = opacity.clamp(0.0, 1.0);
    }

    /// Gets the current layout configuration as a JSON string.
    ///
    /// Returns a JSON object with all layout parameters.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// const config = JSON.parse(rource.getLayoutConfig());
    /// console.log(config.radial_distance_scale);
    /// ```
    #[wasm_bindgen(js_name = getLayoutConfig)]
    pub fn get_layout_config(&self) -> String {
        let layout = &self.settings.layout;
        format!(
            r#"{{"radial_distance_scale":{},"min_angular_span":{},"depth_distance_exponent":{},"sibling_spacing_multiplier":{},"branch_depth_fade":{},"branch_opacity_max":{},"auto_scale":{},"large_repo_threshold":{}}}"#,
            layout.radial_distance_scale,
            layout.min_angular_span,
            layout.depth_distance_exponent,
            layout.sibling_spacing_multiplier,
            layout.branch_depth_fade,
            layout.branch_opacity_max,
            layout.auto_scale,
            layout.large_repo_threshold
        )
    }

    // ========================================================================
    // GPU Physics Configuration (wgpu only)
    // ========================================================================

    /// Enables or disables GPU physics simulation.
    ///
    /// When enabled and using the wgpu backend, the force-directed physics
    /// simulation runs on the GPU using compute shaders. This provides
    /// significant performance improvements for large repositories (500+
    /// directories) where CPU physics becomes the bottleneck.
    ///
    /// **Note**: GPU physics only works with the wgpu backend. When using
    /// WebGL2 or Software renderers, this setting is ignored and CPU physics
    /// is always used.
    ///
    /// # Arguments
    /// * `enabled` - Whether to enable GPU physics
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// if (rource.isWgpu()) {
    ///     rource.setUseGPUPhysics(true);
    ///     console.log('GPU physics enabled');
    /// }
    /// ```
    #[wasm_bindgen(js_name = setUseGPUPhysics)]
    pub fn set_use_gpu_physics(&mut self, enabled: bool) {
        self.use_gpu_physics = enabled;
    }

    /// Returns whether GPU physics is currently enabled.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// console.log('GPU physics:', rource.isGPUPhysicsEnabled());
    /// ```
    #[wasm_bindgen(js_name = isGPUPhysicsEnabled)]
    pub fn is_gpu_physics_enabled(&self) -> bool {
        self.use_gpu_physics
    }

    /// Returns whether GPU physics is currently active.
    ///
    /// This checks all conditions required for GPU physics:
    /// 1. GPU physics is enabled via `setUseGPUPhysics(true)`
    /// 2. wgpu backend is being used
    /// 3. Directory count exceeds threshold (if threshold > 0)
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// if (rource.isGPUPhysicsActive()) {
    ///     console.log('GPU physics is running');
    /// }
    /// ```
    #[wasm_bindgen(js_name = isGPUPhysicsActive)]
    pub fn is_gpu_physics_active(&self) -> bool {
        self.should_use_gpu_physics()
    }

    /// Sets the directory count threshold for enabling GPU physics.
    ///
    /// When the scene has more directories than this threshold, GPU physics
    /// will be used (if enabled and wgpu backend is active).
    ///
    /// Set to 0 to always use GPU physics when enabled (ignores directory count).
    ///
    /// Default: 500 directories
    ///
    /// # Arguments
    /// * `threshold` - Minimum directory count to trigger GPU physics
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// // Use GPU physics for repos with 1000+ directories
    /// rource.setGPUPhysicsThreshold(1000);
    ///
    /// // Always use GPU physics when enabled (no threshold)
    /// rource.setGPUPhysicsThreshold(0);
    /// ```
    #[wasm_bindgen(js_name = setGPUPhysicsThreshold)]
    pub fn set_gpu_physics_threshold(&mut self, threshold: usize) {
        self.gpu_physics_threshold = threshold;
    }

    /// Returns the current GPU physics threshold.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// console.log('GPU physics threshold:', rource.getGPUPhysicsThreshold());
    /// ```
    #[wasm_bindgen(js_name = getGPUPhysicsThreshold)]
    pub fn get_gpu_physics_threshold(&self) -> usize {
        self.gpu_physics_threshold
    }

    /// Warms up the GPU physics compute pipeline.
    ///
    /// Call this during initialization to pre-compile compute shaders
    /// and avoid first-frame stuttering when GPU physics is first used.
    ///
    /// **Note**: Only has an effect when using the wgpu backend.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// if (rource.isWgpu()) {
    ///     rource.warmupGPUPhysics();
    ///     rource.setUseGPUPhysics(true);
    /// }
    /// ```
    #[wasm_bindgen(js_name = warmupGPUPhysics)]
    pub fn warmup_gpu_physics(&mut self) {
        #[cfg(target_arch = "wasm32")]
        if let Some(wgpu_renderer) = self.backend.as_wgpu_mut() {
            wgpu_renderer.warmup_physics();
        }
    }

    // ========================================================================
    // GPU Visibility Culling Configuration (wgpu only)
    // ========================================================================

    /// Enables or disables GPU visibility culling.
    ///
    /// When enabled and using the wgpu backend, visibility culling runs on
    /// the GPU using compute shaders. This is beneficial for extreme-scale
    /// scenarios (10,000+ visible entities) where CPU culling becomes a
    /// bottleneck.
    ///
    /// **Note**: GPU culling only works with the wgpu backend. When using
    /// WebGL2 or Software renderers, this setting is ignored and CPU culling
    /// is always used.
    ///
    /// For most use cases, the default CPU-side quadtree culling is sufficient.
    ///
    /// # Arguments
    /// * `enabled` - Whether to enable GPU culling
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// if (rource.isWgpu()) {
    ///     rource.setUseGPUCulling(true);
    ///     console.log('GPU culling enabled');
    /// }
    /// ```
    #[wasm_bindgen(js_name = setUseGPUCulling)]
    pub fn set_use_gpu_culling(&mut self, enabled: bool) {
        self.use_gpu_culling = enabled;

        // Also enable in the wgpu renderer
        #[cfg(target_arch = "wasm32")]
        if let Some(wgpu_renderer) = self.backend.as_wgpu_mut() {
            wgpu_renderer.set_gpu_culling_enabled(enabled);
        }
    }

    /// Returns whether GPU visibility culling is currently enabled.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// console.log('GPU culling:', rource.isGPUCullingEnabled());
    /// ```
    #[wasm_bindgen(js_name = isGPUCullingEnabled)]
    pub fn is_gpu_culling_enabled(&self) -> bool {
        self.use_gpu_culling
    }

    /// Returns whether GPU visibility culling is currently active.
    ///
    /// This checks all conditions required for GPU culling:
    /// 1. GPU culling is enabled via `setUseGPUCulling(true)`
    /// 2. wgpu backend is being used
    /// 3. Total entity count exceeds threshold (if threshold > 0)
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// if (rource.isGPUCullingActive()) {
    ///     console.log('GPU culling is running');
    /// }
    /// ```
    #[wasm_bindgen(js_name = isGPUCullingActive)]
    pub fn is_gpu_culling_active(&self) -> bool {
        self.should_use_gpu_culling()
    }

    /// Sets the entity count threshold for enabling GPU culling.
    ///
    /// When the total visible entity count exceeds this threshold, GPU culling
    /// will be used (if enabled and wgpu backend is active).
    ///
    /// Set to 0 to always use GPU culling when enabled (ignores entity count).
    ///
    /// Default: 10000 entities
    ///
    /// # Arguments
    /// * `threshold` - Minimum entity count to trigger GPU culling
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// // Use GPU culling for scenes with 5000+ entities
    /// rource.setGPUCullingThreshold(5000);
    ///
    /// // Always use GPU culling when enabled (no threshold)
    /// rource.setGPUCullingThreshold(0);
    /// ```
    #[wasm_bindgen(js_name = setGPUCullingThreshold)]
    pub fn set_gpu_culling_threshold(&mut self, threshold: usize) {
        self.gpu_culling_threshold = threshold;
    }

    /// Returns the current GPU culling threshold.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// console.log('GPU culling threshold:', rource.getGPUCullingThreshold());
    /// ```
    #[wasm_bindgen(js_name = getGPUCullingThreshold)]
    pub fn get_gpu_culling_threshold(&self) -> usize {
        self.gpu_culling_threshold
    }

    /// Warms up the GPU visibility culling compute pipeline.
    ///
    /// Call this during initialization to pre-compile compute shaders
    /// and avoid first-frame stuttering when GPU culling is first used.
    ///
    /// **Note**: Only has an effect when using the wgpu backend.
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// if (rource.isWgpu()) {
    ///     rource.warmupGPUCulling();
    ///     rource.setUseGPUCulling(true);
    /// }
    /// ```
    #[wasm_bindgen(js_name = warmupGPUCulling)]
    pub fn warmup_gpu_culling(&mut self) {
        #[cfg(target_arch = "wasm32")]
        if let Some(wgpu_renderer) = self.backend.as_wgpu_mut() {
            wgpu_renderer.warmup_culling();
        }
    }

    /// Returns GPU culling statistics as a JSON string.
    ///
    /// Returns statistics from the last frame's culling operation, or null
    /// if GPU culling is not active or no culling has occurred yet.
    ///
    /// # Returns
    /// JSON string with fields:
    /// - `totalInstances`: Total instances submitted for culling
    /// - `visibleInstances`: Instances that passed culling
    /// - `dispatchCount`: Number of culling dispatches
    /// - `cullRatio`: Ratio of visible/total (0.0-1.0)
    /// - `culledPercentage`: Percentage culled (0.0-100.0)
    ///
    /// # Example (JavaScript)
    /// ```javascript
    /// const stats = rource.getGPUCullingStats();
    /// if (stats) {
    ///     const data = JSON.parse(stats);
    ///     console.log(`Culled ${data.culledPercentage.toFixed(1)}% of instances`);
    /// }
    /// ```
    #[wasm_bindgen(js_name = getGPUCullingStats)]
    pub fn get_gpu_culling_stats(&self) -> Option<String> {
        #[cfg(target_arch = "wasm32")]
        {
            // Need to get immutable reference for stats query
            // Since as_wgpu_mut isn't available, check renderer type
            if self.renderer_type != crate::backend::RendererType::Wgpu {
                return None;
            }

            // For now, return None since we can't easily get immutable access
            // The culling stats would need a different access pattern
            // This is a placeholder that will be filled when culling is wired in
            None
        }

        #[cfg(not(target_arch = "wasm32"))]
        None
    }
}
