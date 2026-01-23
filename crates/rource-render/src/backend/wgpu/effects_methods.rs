// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Post-processing effect and display configuration methods for the wgpu renderer.
//!
//! This module contains methods for configuring:
//! - Bloom post-processing effects
//! - Shadow post-processing effects
//! - Present mode (vsync control)

use super::{
    bloom::{BloomConfig, BloomPipeline},
    shadow::{ShadowConfig, ShadowPipeline},
    WgpuRenderer,
};

/// Present mode for controlling vsync and frame pacing.
///
/// This maps to `wgpu::PresentMode` but provides a simpler API for configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum VsyncMode {
    /// Vsync enabled (default) - frames are synchronized to display refresh.
    /// Prevents tearing but limits max FPS to display refresh rate.
    #[default]
    Enabled,
    /// Vsync disabled - frames are presented as fast as possible.
    /// May cause tearing but allows uncapped frame rates.
    Disabled,
}

impl WgpuRenderer {
    /// Enables or disables bloom post-processing.
    pub fn set_bloom_enabled(&mut self, enabled: bool) {
        self.bloom_enabled = enabled;
        if enabled {
            // Initialize bloom pipeline if needed
            if self.bloom_pipeline.is_none() {
                let format = self
                    .surface_config
                    .as_ref()
                    .map(|c| c.format)
                    .unwrap_or(wgpu::TextureFormat::Bgra8UnormSrgb);
                self.bloom_pipeline = Some(BloomPipeline::new(&self.device, format));
            }
            // Pre-allocate scene texture to avoid first-frame stutter
            // Bloom manages its own scene target, but ensure the bloom pipeline is sized
            if let Some(ref mut bloom) = self.bloom_pipeline {
                bloom.ensure_size(&self.device, self.width, self.height);
            }
        }
    }

    /// Returns whether bloom is enabled.
    #[inline]
    pub fn is_bloom_enabled(&self) -> bool {
        self.bloom_enabled
    }

    /// Sets bloom configuration.
    pub fn set_bloom_config(&mut self, config: BloomConfig) {
        let format = self
            .surface_config
            .as_ref()
            .map(|c| c.format)
            .unwrap_or(wgpu::TextureFormat::Bgra8UnormSrgb);

        if let Some(ref mut bloom) = self.bloom_pipeline {
            bloom.config = config;
        } else {
            let mut bloom = BloomPipeline::new(&self.device, format);
            bloom.config = config;
            self.bloom_pipeline = Some(bloom);
        }
    }

    /// Returns the current bloom configuration.
    pub fn bloom_config(&self) -> Option<&BloomConfig> {
        self.bloom_pipeline.as_ref().map(|b| &b.config)
    }

    /// Enables or disables shadow post-processing.
    pub fn set_shadow_enabled(&mut self, enabled: bool) {
        self.shadow_enabled = enabled;
        if enabled {
            // Initialize shadow pipeline if needed
            if self.shadow_pipeline.is_none() {
                let format = self
                    .surface_config
                    .as_ref()
                    .map(|c| c.format)
                    .unwrap_or(wgpu::TextureFormat::Bgra8UnormSrgb);
                self.shadow_pipeline = Some(ShadowPipeline::new(&self.device, format));
            }
            // Pre-allocate scene texture to avoid first-frame stutter
            self.ensure_scene_texture();
            // Also ensure the shadow pipeline's internal textures are sized
            if let Some(ref mut shadow) = self.shadow_pipeline {
                shadow.ensure_size(&self.device, self.width, self.height);
            }
        }
    }

    /// Returns whether shadow is enabled.
    #[inline]
    pub fn is_shadow_enabled(&self) -> bool {
        self.shadow_enabled
    }

    /// Sets shadow configuration.
    pub fn set_shadow_config(&mut self, config: ShadowConfig) {
        let format = self
            .surface_config
            .as_ref()
            .map(|c| c.format)
            .unwrap_or(wgpu::TextureFormat::Bgra8UnormSrgb);

        if let Some(ref mut shadow) = self.shadow_pipeline {
            shadow.config = config;
        } else {
            let mut shadow = ShadowPipeline::new(&self.device, format);
            shadow.config = config;
            self.shadow_pipeline = Some(shadow);
        }
    }

    /// Returns the current shadow configuration.
    pub fn shadow_config(&self) -> Option<&ShadowConfig> {
        self.shadow_pipeline.as_ref().map(|s| &s.config)
    }

    // ========================================================================
    // Vsync / Present Mode Configuration
    // ========================================================================

    /// Sets the vsync mode for the renderer.
    ///
    /// - `VsyncMode::Enabled` (default): Frames are synchronized to the display
    ///   refresh rate. This prevents tearing but limits max FPS.
    /// - `VsyncMode::Disabled`: Frames are presented immediately without waiting
    ///   for vsync. This allows uncapped frame rates but may cause tearing.
    ///
    /// # Performance Impact
    ///
    /// Disabling vsync can significantly increase frame rates (from ~60 to 300+ FPS)
    /// but also increases GPU utilization and power consumption. Use with caution
    /// on battery-powered devices.
    ///
    /// # Note
    ///
    /// This method reconfigures the swap chain, which may cause a brief stutter.
    /// It's best to call this during initialization or when the user explicitly
    /// changes the setting, not during active rendering.
    pub fn set_vsync_mode(&mut self, mode: VsyncMode) {
        if let (Some(ref surface), Some(ref mut config)) = (&self.surface, &mut self.surface_config)
        {
            let new_present_mode = match mode {
                VsyncMode::Enabled => wgpu::PresentMode::Fifo,
                VsyncMode::Disabled => {
                    // Try Mailbox first (best for tearing-free uncapped), fall back to Immediate
                    // Note: The surface capabilities should be checked, but for simplicity
                    // we use AutoNoVsync which the driver will handle appropriately
                    wgpu::PresentMode::AutoNoVsync
                }
            };

            // Only reconfigure if the mode actually changed
            if config.present_mode != new_present_mode {
                config.present_mode = new_present_mode;
                surface.configure(&self.device, config);
            }
        }
    }

    /// Returns the current vsync mode.
    pub fn vsync_mode(&self) -> VsyncMode {
        self.surface_config
            .as_ref()
            .map(|config| match config.present_mode {
                wgpu::PresentMode::Fifo | wgpu::PresentMode::FifoRelaxed => VsyncMode::Enabled,
                _ => VsyncMode::Disabled,
            })
            .unwrap_or(VsyncMode::Enabled)
    }

    /// Returns whether vsync is currently enabled.
    #[inline]
    pub fn is_vsync_enabled(&self) -> bool {
        self.vsync_mode() == VsyncMode::Enabled
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bloom_config() {
        let config = BloomConfig::default();
        assert!(config.threshold > 0.0);
        assert!(config.intensity > 0.0);

        let subtle = BloomConfig::subtle();
        let intense = BloomConfig::intense();
        assert!(intense.intensity > subtle.intensity);
    }

    #[test]
    fn test_shadow_config() {
        let config = ShadowConfig::default();
        assert!(config.opacity > 0.0);
        assert!(config.offset_x != 0.0 || config.offset_y != 0.0);

        let subtle = ShadowConfig::subtle();
        let strong = ShadowConfig::strong();
        assert!(strong.opacity > subtle.opacity);
    }
}
