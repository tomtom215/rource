// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! File icon methods for the wgpu renderer.
//!
//! This module contains methods for managing file extension icons using
//! the texture array infrastructure.

use super::{textures::TextureArray, WgpuRenderer};
use crate::backend::icons::{common_extensions, generate_default_icon, generate_icon, ICON_SIZE};
use rource_math::Color;

/// Configuration for file icon rendering.
#[derive(Debug, Clone)]
#[allow(dead_code)] // Future API for configurable file icons
pub struct FileIconConfig {
    /// Whether file icons are enabled.
    pub enabled: bool,
    /// Maximum number of unique file types to track.
    pub max_types: u32,
}

impl Default for FileIconConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            max_types: 64,
        }
    }
}

impl WgpuRenderer {
    /// Initializes the file icon texture array.
    ///
    /// This pre-registers icons for common file extensions. Call this once
    /// during initialization if you want to use file icon rendering.
    ///
    /// # Returns
    ///
    /// `true` if initialization succeeded, `false` otherwise.
    pub fn init_file_icons(&mut self) -> bool {
        // Create texture array layout if it doesn't exist
        let layout = self
            .device
            .create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("file_icon_texture_array_layout"),
                entries: &[
                    wgpu::BindGroupLayoutEntry {
                        binding: 0,
                        visibility: wgpu::ShaderStages::FRAGMENT,
                        ty: wgpu::BindingType::Texture {
                            sample_type: wgpu::TextureSampleType::Float { filterable: true },
                            view_dimension: wgpu::TextureViewDimension::D2Array,
                            multisampled: false,
                        },
                        count: None,
                    },
                    wgpu::BindGroupLayoutEntry {
                        binding: 1,
                        visibility: wgpu::ShaderStages::FRAGMENT,
                        ty: wgpu::BindingType::Sampler(wgpu::SamplerBindingType::Filtering),
                        count: None,
                    },
                ],
            });

        // Create texture array
        let Some(mut array) = TextureArray::new(
            &self.device,
            &layout,
            ICON_SIZE as u32,
            ICON_SIZE as u32,
            64, // Max 64 file types
        ) else {
            return false;
        };

        // Register common file extensions
        for (ext, color) in common_extensions() {
            let icon_data = generate_icon(color);
            array.register_extension(&self.queue, ext, &icon_data);
        }

        // Register default icon for unknown extensions
        let default_icon = generate_default_icon();
        array.register_extension(&self.queue, "_default", &default_icon);

        self.file_icon_array = Some(array);
        true
    }

    /// Returns the icon layer index for a file extension.
    ///
    /// If the extension is not registered, returns the default icon layer.
    /// If file icons are not initialized, returns `None`.
    ///
    /// # Arguments
    ///
    /// * `extension` - File extension (e.g., "rs", "js", "py")
    pub fn get_file_icon_layer(&self, extension: &str) -> Option<u32> {
        let array = self.file_icon_array.as_ref()?;

        // Try to find the extension
        if let Some(layer) = array.get_layer(extension) {
            return Some(layer);
        }

        // Fall back to default
        array.get_layer("_default")
    }

    /// Registers a custom icon for a file extension.
    ///
    /// If the extension is already registered, this does nothing.
    /// If file icons are not initialized, returns `false`.
    ///
    /// # Arguments
    ///
    /// * `extension` - File extension (e.g., "custom")
    /// * `color` - Color for the icon
    ///
    /// # Returns
    ///
    /// `true` if the icon was registered, `false` otherwise.
    pub fn register_file_icon(&mut self, extension: &str, color: Color) -> bool {
        let Some(array) = self.file_icon_array.as_mut() else {
            return false;
        };

        // Check if already registered
        if array.has_extension(extension) {
            return true;
        }

        // Generate and register icon
        let icon_data = generate_icon(color);
        array
            .register_extension(&self.queue, extension, &icon_data)
            .is_some()
    }

    /// Returns whether file icons are initialized.
    #[inline]
    pub fn has_file_icons(&self) -> bool {
        self.file_icon_array.is_some()
    }

    /// Returns the number of registered file icon types.
    pub fn file_icon_count(&self) -> u32 {
        self.file_icon_array
            .as_ref()
            .map_or(0, TextureArray::layer_count)
    }

    /// Returns the file icon texture array bind group.
    ///
    /// Returns `None` if file icons are not initialized.
    pub fn file_icon_bind_group(&self) -> Option<&wgpu::BindGroup> {
        self.file_icon_array.as_ref().map(TextureArray::bind_group)
    }

    /// Draws a file icon at the specified screen position.
    ///
    /// This method queues a textured quad for rendering using the texture array
    /// pipeline. Icons are batched and rendered in a single draw call at flush time.
    ///
    /// # Arguments
    ///
    /// * `x` - Screen X coordinate (center of icon)
    /// * `y` - Screen Y coordinate (center of icon)
    /// * `size` - Icon size in pixels (width and height)
    /// * `extension` - File extension to determine which icon layer to use
    /// * `tint` - Optional color tint (multiplied with icon color)
    ///
    /// # Returns
    ///
    /// `true` if the icon was queued, `false` if file icons are not initialized.
    #[inline]
    pub fn draw_file_icon(
        &mut self,
        x: f32,
        y: f32,
        size: f32,
        extension: &str,
        tint: Option<Color>,
    ) -> bool {
        // Get layer index for this extension
        let Some(layer) = self.get_file_icon_layer(extension) else {
            return false;
        };

        let half = size * 0.5;
        let color = tint.unwrap_or(Color::WHITE);

        // Calculate bounds (min_x, min_y, max_x, max_y)
        let bounds = [x - half, y - half, x + half, y + half];

        // UV bounds for the entire icon (0 to 1)
        let uv_bounds = [0.0f32, 0.0, 1.0, 1.0];

        // Push instance data:
        // bounds (4 floats) + uv_bounds (4 floats) + color (4 floats) + layer (1 u32)
        self.file_icon_instances.push_raw(&bounds);
        self.file_icon_instances.push_raw(&uv_bounds);
        self.file_icon_instances
            .push_raw(&[color.r, color.g, color.b, color.a]);
        // Push layer as bits of f32 (will be reinterpreted as u32 in shader)
        self.file_icon_instances.push_raw(&[f32::from_bits(layer)]);

        true
    }

    /// Draws a file icon with explicit layer index.
    ///
    /// This is a lower-level variant that skips extension lookup.
    ///
    /// # Arguments
    ///
    /// * `x` - Screen X coordinate (center of icon)
    /// * `y` - Screen Y coordinate (center of icon)
    /// * `size` - Icon size in pixels
    /// * `layer` - Texture array layer index
    /// * `tint` - Color tint (multiplied with icon color)
    #[inline]
    pub fn draw_file_icon_with_layer(
        &mut self,
        x: f32,
        y: f32,
        size: f32,
        layer: u32,
        tint: Color,
    ) {
        let half = size * 0.5;

        // Calculate bounds (min_x, min_y, max_x, max_y)
        let bounds = [x - half, y - half, x + half, y + half];

        // UV bounds for the entire icon (0 to 1)
        let uv_bounds = [0.0f32, 0.0, 1.0, 1.0];

        // Push instance data
        self.file_icon_instances.push_raw(&bounds);
        self.file_icon_instances.push_raw(&uv_bounds);
        self.file_icon_instances
            .push_raw(&[tint.r, tint.g, tint.b, tint.a]);
        // Push layer as bits of f32 (will be reinterpreted as u32 in shader)
        self.file_icon_instances.push_raw(&[f32::from_bits(layer)]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_file_icon_config_default() {
        let config = FileIconConfig::default();
        assert!(!config.enabled);
        assert_eq!(config.max_types, 64);
    }
}
