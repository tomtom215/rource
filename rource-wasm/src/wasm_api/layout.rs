// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

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
// Helper Functions (testable without Rource instance)
// ============================================================================

#[allow(dead_code)]
#[allow(clippy::wildcard_imports)]
mod helpers {
    use super::*;

    /// Parses a layout preset name and returns whether it's valid.
    ///
    /// # Arguments
    /// * `preset` - The preset name (case-insensitive)
    ///
    /// # Returns
    /// `true` if the preset is recognized.
    #[inline]
    #[must_use]
    pub fn is_valid_preset(preset: &str) -> bool {
        matches!(
            preset.to_lowercase().as_str(),
            "small" | "medium" | "large" | "massive"
        )
    }

    /// Clamps a radial distance scale to valid range.
    ///
    /// # Arguments
    /// * `scale` - The scale value to clamp
    ///
    /// # Returns
    /// Clamped value in range [40.0, 500.0].
    #[inline]
    #[must_use]
    pub fn clamp_radial_distance_scale(scale: f32) -> f32 {
        scale.clamp(40.0, 500.0)
    }

    /// Clamps a depth distance exponent to valid range.
    ///
    /// # Arguments
    /// * `exponent` - The exponent value to clamp
    ///
    /// # Returns
    /// Clamped value in range [0.5, 2.0].
    #[inline]
    #[must_use]
    pub fn clamp_depth_distance_exponent(exponent: f32) -> f32 {
        exponent.clamp(0.5, 2.0)
    }

    /// Clamps a branch depth fade value to valid range.
    ///
    /// # Arguments
    /// * `fade` - The fade value to clamp
    ///
    /// # Returns
    /// Clamped value in range [0.0, 1.0].
    #[inline]
    #[must_use]
    pub fn clamp_branch_depth_fade(fade: f32) -> f32 {
        fade.clamp(0.0, 1.0)
    }

    /// Clamps a branch opacity max value to valid range.
    ///
    /// # Arguments
    /// * `opacity` - The opacity value to clamp
    ///
    /// # Returns
    /// Clamped value in range [0.0, 1.0].
    #[inline]
    #[must_use]
    pub fn clamp_branch_opacity_max(opacity: f32) -> f32 {
        opacity.clamp(0.0, 1.0)
    }

    /// Formats layout settings as a JSON string.
    ///
    /// # Arguments
    /// * `settings` - The layout settings to format
    ///
    /// # Returns
    /// JSON string representation.
    #[must_use]
    pub fn format_layout_config(settings: &LayoutSettings) -> String {
        format!(
            r#"{{"radial_distance_scale":{},"min_angular_span":{},"depth_distance_exponent":{},"sibling_spacing_multiplier":{},"branch_depth_fade":{},"branch_opacity_max":{},"auto_scale":{},"large_repo_threshold":{}}}"#,
            settings.radial_distance_scale,
            settings.min_angular_span,
            settings.depth_distance_exponent,
            settings.sibling_spacing_multiplier,
            settings.branch_depth_fade,
            settings.branch_opacity_max,
            settings.auto_scale,
            settings.large_repo_threshold
        )
    }
}

#[allow(unused_imports)]
pub use helpers::*;

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
        self.wake_renderer();
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
        self.wake_renderer();
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
        self.wake_renderer();
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
        self.wake_renderer();
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
        self.wake_renderer();
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
        self.wake_renderer();
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

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // Preset Validation Tests
    // ========================================================================

    #[test]
    fn test_is_valid_preset_known_presets() {
        assert!(is_valid_preset("small"));
        assert!(is_valid_preset("medium"));
        assert!(is_valid_preset("large"));
        assert!(is_valid_preset("massive"));
    }

    #[test]
    fn test_is_valid_preset_case_insensitive() {
        assert!(is_valid_preset("SMALL"));
        assert!(is_valid_preset("Medium"));
        assert!(is_valid_preset("LARGE"));
        assert!(is_valid_preset("MaSSiVe"));
    }

    #[test]
    fn test_is_valid_preset_unknown() {
        assert!(!is_valid_preset("tiny"));
        assert!(!is_valid_preset("huge"));
        assert!(!is_valid_preset("default"));
        assert!(!is_valid_preset(""));
        assert!(!is_valid_preset("extra-large"));
    }

    // ========================================================================
    // Radial Distance Scale Clamping Tests
    // ========================================================================

    #[test]
    fn test_clamp_radial_distance_scale_within_range() {
        assert!((clamp_radial_distance_scale(80.0) - 80.0).abs() < 0.001);
        assert!((clamp_radial_distance_scale(100.0) - 100.0).abs() < 0.001);
        assert!((clamp_radial_distance_scale(250.0) - 250.0).abs() < 0.001);
    }

    #[test]
    fn test_clamp_radial_distance_scale_minimum() {
        assert!((clamp_radial_distance_scale(40.0) - 40.0).abs() < 0.001);
        assert!((clamp_radial_distance_scale(20.0) - 40.0).abs() < 0.001);
        assert!((clamp_radial_distance_scale(0.0) - 40.0).abs() < 0.001);
        assert!((clamp_radial_distance_scale(-10.0) - 40.0).abs() < 0.001);
    }

    #[test]
    fn test_clamp_radial_distance_scale_maximum() {
        assert!((clamp_radial_distance_scale(500.0) - 500.0).abs() < 0.001);
        assert!((clamp_radial_distance_scale(600.0) - 500.0).abs() < 0.001);
        assert!((clamp_radial_distance_scale(1000.0) - 500.0).abs() < 0.001);
    }

    // ========================================================================
    // Depth Distance Exponent Clamping Tests
    // ========================================================================

    #[test]
    fn test_clamp_depth_distance_exponent_within_range() {
        assert!((clamp_depth_distance_exponent(1.0) - 1.0).abs() < 0.001);
        assert!((clamp_depth_distance_exponent(1.5) - 1.5).abs() < 0.001);
        assert!((clamp_depth_distance_exponent(0.7) - 0.7).abs() < 0.001);
    }

    #[test]
    fn test_clamp_depth_distance_exponent_minimum() {
        assert!((clamp_depth_distance_exponent(0.5) - 0.5).abs() < 0.001);
        assert!((clamp_depth_distance_exponent(0.3) - 0.5).abs() < 0.001);
        assert!((clamp_depth_distance_exponent(0.0) - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_clamp_depth_distance_exponent_maximum() {
        assert!((clamp_depth_distance_exponent(2.0) - 2.0).abs() < 0.001);
        assert!((clamp_depth_distance_exponent(2.5) - 2.0).abs() < 0.001);
        assert!((clamp_depth_distance_exponent(5.0) - 2.0).abs() < 0.001);
    }

    // ========================================================================
    // Branch Depth Fade Clamping Tests
    // ========================================================================

    #[test]
    fn test_clamp_branch_depth_fade_within_range() {
        assert!((clamp_branch_depth_fade(0.3) - 0.3).abs() < 0.001);
        assert!((clamp_branch_depth_fade(0.5) - 0.5).abs() < 0.001);
        assert!((clamp_branch_depth_fade(0.0) - 0.0).abs() < 0.001);
        assert!((clamp_branch_depth_fade(1.0) - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_clamp_branch_depth_fade_minimum() {
        assert!((clamp_branch_depth_fade(-0.1) - 0.0).abs() < 0.001);
        assert!((clamp_branch_depth_fade(-1.0) - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_clamp_branch_depth_fade_maximum() {
        assert!((clamp_branch_depth_fade(1.1) - 1.0).abs() < 0.001);
        assert!((clamp_branch_depth_fade(2.0) - 1.0).abs() < 0.001);
    }

    // ========================================================================
    // Branch Opacity Clamping Tests
    // ========================================================================

    #[test]
    fn test_clamp_branch_opacity_max_within_range() {
        assert!((clamp_branch_opacity_max(0.35) - 0.35).abs() < 0.001);
        assert!((clamp_branch_opacity_max(0.5) - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_clamp_branch_opacity_max_bounds() {
        assert!((clamp_branch_opacity_max(-0.5) - 0.0).abs() < 0.001);
        assert!((clamp_branch_opacity_max(1.5) - 1.0).abs() < 0.001);
    }

    // ========================================================================
    // Layout Config Formatting Tests
    // ========================================================================

    #[test]
    fn test_format_layout_config_default() {
        let settings = LayoutSettings::default();
        let json = format_layout_config(&settings);
        assert!(json.starts_with('{'));
        assert!(json.ends_with('}'));
        assert!(json.contains("radial_distance_scale"));
        assert!(json.contains("min_angular_span"));
        assert!(json.contains("depth_distance_exponent"));
        assert!(json.contains("sibling_spacing_multiplier"));
        assert!(json.contains("branch_depth_fade"));
        assert!(json.contains("branch_opacity_max"));
        assert!(json.contains("auto_scale"));
        assert!(json.contains("large_repo_threshold"));
    }

    #[test]
    fn test_format_layout_config_presets() {
        let small = format_layout_config(&LayoutSettings::small_repo());
        let large = format_layout_config(&LayoutSettings::large_repo());
        let massive = format_layout_config(&LayoutSettings::massive_repo());

        // All should be valid JSON objects
        assert!(small.starts_with('{'));
        assert!(large.starts_with('{'));
        assert!(massive.starts_with('{'));

        // Different presets should have different values
        assert_ne!(small, large);
        assert_ne!(large, massive);
    }
}
