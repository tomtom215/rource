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
}
