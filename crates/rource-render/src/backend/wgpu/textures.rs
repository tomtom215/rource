// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Texture management for wgpu renderer.
//!
//! This module provides texture atlas management for font glyphs and
//! general texture handling for user images.
//!
//! ## Font Atlas
//!
//! The font atlas uses row-based packing to efficiently store glyphs:
//!
//! ```text
//! ┌───────────────────────────────────────┐
//! │ A B C D E F G H I J K L M N O P Q R S │ Row 0 (height 16)
//! ├───────────────────────────────────────┤
//! │ a b c d e f g h i j k l m n o p q r s │ Row 1 (height 14)
//! ├───────────────────────────────────────┤
//! │ 0 1 2 3 4 5 6 7 8 9 ! @ # $ % ^ & * ( │ Row 2 (height 12)
//! ├───────────────────────────────────────┤
//! │                                       │ (unused)
//! └───────────────────────────────────────┘
//! ```
//!
//! ## Performance
//!
//! - Glyphs are cached by (character, size) key
//! - Atlas grows dynamically from 512px to 2048px max
//! - Defragmentation reclaims wasted space when needed

use std::collections::HashMap;

/// Initial font atlas size in pixels.
const INITIAL_ATLAS_SIZE: u32 = 512;

/// Maximum font atlas size in pixels.
const MAX_ATLAS_SIZE: u32 = 2048;

/// Padding between glyphs in the atlas.
const GLYPH_PADDING: u32 = 2;

/// Fragmentation threshold for defragmentation (50%).
const DEFRAG_THRESHOLD: f32 = 0.5;

/// Key for looking up cached glyphs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GlyphKey {
    /// The character.
    pub ch: char,
    /// Font size in tenths of a point (e.g., 120 = 12.0pt).
    pub size_tenths: u32,
}

impl GlyphKey {
    /// Creates a new glyph key.
    #[inline]
    pub fn new(ch: char, size: f32) -> Self {
        Self {
            ch,
            size_tenths: (size * 10.0).round() as u32,
        }
    }

    /// Returns the font size in points.
    #[inline]
    pub fn size(&self) -> f32 {
        self.size_tenths as f32 / 10.0
    }
}

/// Region in the texture atlas.
#[derive(Debug, Clone, Copy)]
pub struct AtlasRegion {
    /// X position in the atlas.
    pub x: u32,
    /// Y position in the atlas.
    pub y: u32,
    /// Width of the region.
    pub width: u32,
    /// Height of the region.
    pub height: u32,
}

impl AtlasRegion {
    /// Returns the UV coordinates for this region.
    ///
    /// # Arguments
    ///
    /// * `atlas_size` - Total atlas size for normalization
    ///
    /// # Returns
    ///
    /// `(u_min, v_min, u_max, v_max)` in [0, 1] range.
    #[inline]
    pub fn uv_bounds(&self, atlas_size: u32) -> (f32, f32, f32, f32) {
        let inv_size = 1.0 / atlas_size as f32;
        (
            self.x as f32 * inv_size,
            self.y as f32 * inv_size,
            (self.x + self.width) as f32 * inv_size,
            (self.y + self.height) as f32 * inv_size,
        )
    }
}

/// Row in the atlas packer.
#[derive(Debug)]
struct AtlasRow {
    /// Y position of this row.
    y: u32,
    /// Height of this row.
    height: u32,
    /// Current X position (next free slot).
    x: u32,
}

/// Row-based atlas packer.
#[derive(Debug)]
struct RowPacker {
    /// All rows in the atlas.
    rows: Vec<AtlasRow>,
    /// Atlas width and height.
    size: u32,
    /// Current Y position for new rows.
    next_row_y: u32,
}

impl RowPacker {
    /// Creates a new row packer.
    fn new(size: u32) -> Self {
        Self {
            rows: Vec::new(),
            size,
            next_row_y: 0,
        }
    }

    /// Attempts to allocate a region.
    ///
    /// # Returns
    ///
    /// `Some(AtlasRegion)` if allocation succeeded, `None` if atlas is full.
    fn allocate(&mut self, width: u32, height: u32) -> Option<AtlasRegion> {
        // Try to fit in an existing row
        for row in &mut self.rows {
            if row.height >= height && row.x + width + GLYPH_PADDING <= self.size {
                let region = AtlasRegion {
                    x: row.x,
                    y: row.y,
                    width,
                    height,
                };
                row.x += width + GLYPH_PADDING;
                return Some(region);
            }
        }

        // Need a new row
        if self.next_row_y + height + GLYPH_PADDING > self.size {
            return None; // Atlas is full
        }

        let region = AtlasRegion {
            x: 0,
            y: self.next_row_y,
            width,
            height,
        };

        self.rows.push(AtlasRow {
            y: self.next_row_y,
            height: height + GLYPH_PADDING,
            x: width + GLYPH_PADDING,
        });

        self.next_row_y += height + GLYPH_PADDING;
        Some(region)
    }

    /// Resets the packer, clearing all allocations.
    fn reset(&mut self) {
        self.rows.clear();
        self.next_row_y = 0;
    }

    /// Resizes the packer to a new size.
    fn resize(&mut self, new_size: u32) {
        self.size = new_size;
        // Don't reset - existing allocations might still be valid
    }
}

/// Cached glyph data for defragmentation.
#[derive(Debug)]
struct CachedGlyph {
    /// The glyph key.
    key: GlyphKey,
    /// Glyph width.
    width: u32,
    /// Glyph height.
    height: u32,
    /// Glyph bitmap data (R8 format).
    data: Vec<u8>,
}

/// Font texture atlas.
///
/// Stores rasterized glyphs in a single GPU texture for efficient text rendering.
#[derive(Debug)]
pub struct FontAtlas {
    /// The GPU texture.
    texture: wgpu::Texture,
    /// Texture view for sampling.
    view: wgpu::TextureView,
    /// Sampler for texture filtering.
    sampler: wgpu::Sampler,
    /// Bind group for shader access.
    bind_group: wgpu::BindGroup,
    /// Cached glyph regions.
    regions: HashMap<GlyphKey, AtlasRegion>,
    /// Row-based packer.
    packer: RowPacker,
    /// Current atlas size.
    size: u32,
    /// CPU-side texture data for defragmentation.
    data: Vec<u8>,
    /// Cached glyphs for defragmentation.
    cached_glyphs: Vec<CachedGlyph>,
    /// Whether the atlas needs to be uploaded.
    dirty: bool,
}

impl FontAtlas {
    /// Creates a new font atlas.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device for resource creation
    /// * `texture_layout` - Bind group layout for texture access
    pub fn new(device: &wgpu::Device, texture_layout: &wgpu::BindGroupLayout) -> Self {
        let size = INITIAL_ATLAS_SIZE;
        let data = vec![0u8; (size * size) as usize];

        let texture = device.create_texture(&wgpu::TextureDescriptor {
            label: Some("font_atlas"),
            size: wgpu::Extent3d {
                width: size,
                height: size,
                depth_or_array_layers: 1,
            },
            mip_level_count: 1,
            sample_count: 1,
            dimension: wgpu::TextureDimension::D2,
            format: wgpu::TextureFormat::R8Unorm,
            usage: wgpu::TextureUsages::TEXTURE_BINDING | wgpu::TextureUsages::COPY_DST,
            view_formats: &[],
        });

        let view = texture.create_view(&wgpu::TextureViewDescriptor::default());

        let sampler = device.create_sampler(&wgpu::SamplerDescriptor {
            label: Some("font_atlas_sampler"),
            address_mode_u: wgpu::AddressMode::ClampToEdge,
            address_mode_v: wgpu::AddressMode::ClampToEdge,
            address_mode_w: wgpu::AddressMode::ClampToEdge,
            mag_filter: wgpu::FilterMode::Linear,
            min_filter: wgpu::FilterMode::Linear,
            mipmap_filter: wgpu::FilterMode::Nearest,
            ..Default::default()
        });

        let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("font_atlas_bind_group"),
            layout: texture_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: wgpu::BindingResource::TextureView(&view),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: wgpu::BindingResource::Sampler(&sampler),
                },
            ],
        });

        Self {
            texture,
            view,
            sampler,
            bind_group,
            regions: HashMap::new(),
            packer: RowPacker::new(size),
            size,
            data,
            cached_glyphs: Vec::new(),
            dirty: false,
        }
    }

    /// Returns the current atlas size.
    #[inline]
    pub fn size(&self) -> u32 {
        self.size
    }

    /// Returns the bind group for shader access.
    #[inline]
    pub fn bind_group(&self) -> &wgpu::BindGroup {
        &self.bind_group
    }

    /// Returns the texture view.
    #[inline]
    pub fn view(&self) -> &wgpu::TextureView {
        &self.view
    }

    /// Looks up a cached glyph region.
    #[inline]
    pub fn get(&self, key: &GlyphKey) -> Option<&AtlasRegion> {
        self.regions.get(key)
    }

    /// Inserts a new glyph into the atlas.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device (needed if atlas must grow)
    /// * `texture_layout` - Bind group layout (needed if atlas must grow)
    /// * `key` - Glyph key
    /// * `width` - Glyph bitmap width
    /// * `height` - Glyph bitmap height
    /// * `bitmap` - Glyph bitmap data (R8 format, row-major)
    ///
    /// # Returns
    ///
    /// The allocated region, or `None` if the atlas is full and cannot grow.
    pub fn insert(
        &mut self,
        device: &wgpu::Device,
        texture_layout: &wgpu::BindGroupLayout,
        key: GlyphKey,
        width: u32,
        height: u32,
        bitmap: &[u8],
    ) -> Option<AtlasRegion> {
        // Check if already cached
        if let Some(region) = self.regions.get(&key) {
            return Some(*region);
        }

        // Try to allocate
        let region = match self.packer.allocate(width, height) {
            Some(region) => region,
            None => {
                // Try defragmentation first
                if self.should_defragment() {
                    self.defragment(device, texture_layout);
                    if let Some(region) = self.packer.allocate(width, height) {
                        // Defrag succeeded, continue with this region
                        region
                    } else {
                        // Still can't fit, try growing
                        if !self.grow(device, texture_layout) {
                            return None;
                        }
                        self.packer.allocate(width, height)?
                    }
                } else if !self.grow(device, texture_layout) {
                    return None;
                } else {
                    self.packer.allocate(width, height)?
                }
            }
        };

        // Copy bitmap to CPU data
        for row in 0..height {
            let src_offset = (row * width) as usize;
            let dst_offset = ((region.y + row) * self.size + region.x) as usize;
            let src_end = src_offset + width as usize;
            let dst_end = dst_offset + width as usize;

            if src_end <= bitmap.len() && dst_end <= self.data.len() {
                self.data[dst_offset..dst_end].copy_from_slice(&bitmap[src_offset..src_end]);
            }
        }

        // Cache for potential defragmentation
        self.cached_glyphs.push(CachedGlyph {
            key,
            width,
            height,
            data: bitmap.to_vec(),
        });

        self.regions.insert(key, region);
        self.dirty = true;

        Some(region)
    }

    /// Uploads the atlas to GPU if dirty.
    pub fn upload(&mut self, queue: &wgpu::Queue) {
        if !self.dirty {
            return;
        }

        queue.write_texture(
            wgpu::TexelCopyTextureInfo {
                texture: &self.texture,
                mip_level: 0,
                origin: wgpu::Origin3d::ZERO,
                aspect: wgpu::TextureAspect::All,
            },
            &self.data,
            wgpu::TexelCopyBufferLayout {
                offset: 0,
                bytes_per_row: Some(self.size),
                rows_per_image: Some(self.size),
            },
            wgpu::Extent3d {
                width: self.size,
                height: self.size,
                depth_or_array_layers: 1,
            },
        );

        self.dirty = false;
    }

    /// Returns whether defragmentation might help.
    fn should_defragment(&self) -> bool {
        if self.cached_glyphs.is_empty() {
            return false;
        }

        let used_pixels: u64 = self
            .cached_glyphs
            .iter()
            .map(|g| u64::from(g.width) * u64::from(g.height))
            .sum();

        let total_pixels = u64::from(self.size) * u64::from(self.size);
        let fragmentation = 1.0 - (used_pixels as f64 / total_pixels as f64);

        fragmentation > f64::from(DEFRAG_THRESHOLD)
    }

    /// Defragments the atlas by repacking all glyphs.
    fn defragment(&mut self, device: &wgpu::Device, texture_layout: &wgpu::BindGroupLayout) {
        // Sort glyphs by height (tallest first) for better packing
        self.cached_glyphs.sort_by(|a, b| b.height.cmp(&a.height));

        // Reset packer and data
        self.packer.reset();
        self.data.fill(0);
        self.regions.clear();

        // Reinsert all glyphs
        let glyphs = std::mem::take(&mut self.cached_glyphs);
        for glyph in glyphs {
            if let Some(region) = self.packer.allocate(glyph.width, glyph.height) {
                // Copy bitmap
                for row in 0..glyph.height {
                    let src_offset = (row * glyph.width) as usize;
                    let dst_offset = ((region.y + row) * self.size + region.x) as usize;
                    let src_end = src_offset + glyph.width as usize;
                    let dst_end = dst_offset + glyph.width as usize;

                    if src_end <= glyph.data.len() && dst_end <= self.data.len() {
                        self.data[dst_offset..dst_end]
                            .copy_from_slice(&glyph.data[src_offset..src_end]);
                    }
                }

                self.regions.insert(glyph.key, region);
                self.cached_glyphs.push(glyph);
            }
        }

        self.dirty = true;

        // Recreate bind group (texture didn't change, but upload will happen)
        self.bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("font_atlas_bind_group"),
            layout: texture_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: wgpu::BindingResource::TextureView(&self.view),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: wgpu::BindingResource::Sampler(&self.sampler),
                },
            ],
        });
    }

    /// Grows the atlas to double its current size.
    ///
    /// # Returns
    ///
    /// `true` if growth succeeded, `false` if already at maximum size.
    fn grow(&mut self, device: &wgpu::Device, texture_layout: &wgpu::BindGroupLayout) -> bool {
        let new_size = self.size * 2;
        if new_size > MAX_ATLAS_SIZE {
            return false;
        }

        // Create new texture
        let texture = device.create_texture(&wgpu::TextureDescriptor {
            label: Some("font_atlas"),
            size: wgpu::Extent3d {
                width: new_size,
                height: new_size,
                depth_or_array_layers: 1,
            },
            mip_level_count: 1,
            sample_count: 1,
            dimension: wgpu::TextureDimension::D2,
            format: wgpu::TextureFormat::R8Unorm,
            usage: wgpu::TextureUsages::TEXTURE_BINDING | wgpu::TextureUsages::COPY_DST,
            view_formats: &[],
        });

        let view = texture.create_view(&wgpu::TextureViewDescriptor::default());

        // Create new data buffer and copy old data
        let mut new_data = vec![0u8; (new_size * new_size) as usize];
        for row in 0..self.size {
            let src_offset = (row * self.size) as usize;
            let dst_offset = (row * new_size) as usize;
            let row_len = self.size as usize;
            new_data[dst_offset..dst_offset + row_len]
                .copy_from_slice(&self.data[src_offset..src_offset + row_len]);
        }

        // Update state
        self.texture = texture;
        self.view = view;
        self.data = new_data;
        self.size = new_size;
        self.packer.resize(new_size);
        self.dirty = true;

        // Recreate bind group with new view
        self.bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("font_atlas_bind_group"),
            layout: texture_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: wgpu::BindingResource::TextureView(&self.view),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: wgpu::BindingResource::Sampler(&self.sampler),
                },
            ],
        });

        true
    }

    /// Returns atlas statistics.
    pub fn stats(&self) -> AtlasStats {
        let glyph_count = self.regions.len();
        let used_pixels: u64 = self
            .cached_glyphs
            .iter()
            .map(|g| u64::from(g.width) * u64::from(g.height))
            .sum();
        let total_pixels = u64::from(self.size) * u64::from(self.size);

        AtlasStats {
            glyph_count,
            used_pixels,
            total_pixels,
            size: self.size,
        }
    }
}

/// Atlas statistics.
#[derive(Debug, Clone, Copy)]
pub struct AtlasStats {
    /// Number of cached glyphs.
    pub glyph_count: usize,
    /// Pixels used by glyphs.
    pub used_pixels: u64,
    /// Total atlas pixels.
    pub total_pixels: u64,
    /// Atlas size in pixels.
    pub size: u32,
}

impl AtlasStats {
    /// Returns the utilization ratio (0.0 - 1.0).
    #[inline]
    pub fn utilization(&self) -> f64 {
        if self.total_pixels == 0 {
            0.0
        } else {
            self.used_pixels as f64 / self.total_pixels as f64
        }
    }

    /// Returns the fragmentation ratio (0.0 - 1.0).
    #[inline]
    pub fn fragmentation(&self) -> f64 {
        1.0 - self.utilization()
    }
}

/// Managed texture for user images.
#[derive(Debug)]
pub struct ManagedTexture {
    /// The GPU texture.
    pub texture: wgpu::Texture,
    /// Texture view.
    pub view: wgpu::TextureView,
    /// Bind group for shader access.
    pub bind_group: wgpu::BindGroup,
    /// Texture width.
    pub width: u32,
    /// Texture height.
    pub height: u32,
}

impl ManagedTexture {
    /// Creates a new managed texture from RGBA data.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device
    /// * `queue` - wgpu queue for upload
    /// * `texture_layout` - Bind group layout
    /// * `width` - Texture width
    /// * `height` - Texture height
    /// * `data` - RGBA pixel data
    /// * `label` - Debug label
    pub fn new(
        device: &wgpu::Device,
        queue: &wgpu::Queue,
        texture_layout: &wgpu::BindGroupLayout,
        width: u32,
        height: u32,
        data: &[u8],
        label: &str,
    ) -> Self {
        let texture = device.create_texture(&wgpu::TextureDescriptor {
            label: Some(label),
            size: wgpu::Extent3d {
                width,
                height,
                depth_or_array_layers: 1,
            },
            mip_level_count: 1,
            sample_count: 1,
            dimension: wgpu::TextureDimension::D2,
            format: wgpu::TextureFormat::Rgba8UnormSrgb,
            usage: wgpu::TextureUsages::TEXTURE_BINDING | wgpu::TextureUsages::COPY_DST,
            view_formats: &[],
        });

        queue.write_texture(
            wgpu::TexelCopyTextureInfo {
                texture: &texture,
                mip_level: 0,
                origin: wgpu::Origin3d::ZERO,
                aspect: wgpu::TextureAspect::All,
            },
            data,
            wgpu::TexelCopyBufferLayout {
                offset: 0,
                bytes_per_row: Some(width * 4),
                rows_per_image: Some(height),
            },
            wgpu::Extent3d {
                width,
                height,
                depth_or_array_layers: 1,
            },
        );

        let view = texture.create_view(&wgpu::TextureViewDescriptor::default());

        let sampler = device.create_sampler(&wgpu::SamplerDescriptor {
            label: Some(&format!("{label}_sampler")),
            address_mode_u: wgpu::AddressMode::ClampToEdge,
            address_mode_v: wgpu::AddressMode::ClampToEdge,
            address_mode_w: wgpu::AddressMode::ClampToEdge,
            mag_filter: wgpu::FilterMode::Linear,
            min_filter: wgpu::FilterMode::Linear,
            mipmap_filter: wgpu::FilterMode::Nearest,
            ..Default::default()
        });

        let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some(&format!("{label}_bind_group")),
            layout: texture_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: wgpu::BindingResource::TextureView(&view),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: wgpu::BindingResource::Sampler(&sampler),
                },
            ],
        });

        Self {
            texture,
            view,
            bind_group,
            width,
            height,
        }
    }
}

// ============================================================================
// Texture Array for File Icons
// ============================================================================

/// Maximum number of layers in a texture array.
///
/// This limits the number of unique file types that can be rendered with a
/// single draw call. 256 layers is sufficient for most use cases (~200 common
/// file extensions).
pub const MAX_TEXTURE_ARRAY_LAYERS: u32 = 256;

/// Default layer size for file icons.
pub const DEFAULT_ICON_SIZE: u32 = 32;

/// Texture array for efficient file icon rendering.
///
/// Stores multiple textures as layers in a single GPU texture array,
/// enabling all icons to be rendered in a single draw call.
///
/// ## Architecture
///
/// ```text
/// ┌─────────────────────────────────────────────┐
/// │ Layer 0: .rs icon                            │
/// ├─────────────────────────────────────────────┤
/// │ Layer 1: .py icon                            │
/// ├─────────────────────────────────────────────┤
/// │ Layer 2: .js icon                            │
/// ├─────────────────────────────────────────────┤
/// │ ...                                          │
/// ├─────────────────────────────────────────────┤
/// │ Layer N: last registered icon               │
/// └─────────────────────────────────────────────┘
/// ```
///
/// ## Usage
///
/// ```ignore
/// // Create array with 32x32 icons
/// let array = TextureArray::new(&device, &queue, 32, 32, 64)?;
///
/// // Register icons (returns layer index)
/// let rs_layer = array.add_layer(&queue, &rs_icon_data)?;
/// let py_layer = array.add_layer(&queue, &py_icon_data)?;
///
/// // Use layer index in shader to sample correct icon
/// ```
#[derive(Debug)]
pub struct TextureArray {
    /// The GPU texture array.
    texture: wgpu::Texture,
    /// Texture view for sampling all layers.
    view: wgpu::TextureView,
    /// Sampler for texture filtering.
    sampler: wgpu::Sampler,
    /// Bind group for shader access.
    bind_group: wgpu::BindGroup,
    /// Width of each layer.
    width: u32,
    /// Height of each layer.
    height: u32,
    /// Maximum number of layers.
    max_layers: u32,
    /// Number of layers currently allocated.
    layer_count: u32,
    /// Extension to layer index mapping.
    extension_map: HashMap<String, u32>,
}

impl TextureArray {
    /// Creates a new texture array.
    ///
    /// # Arguments
    ///
    /// * `device` - wgpu device for resource creation
    /// * `texture_array_layout` - Bind group layout for texture array access
    /// * `width` - Width of each layer in pixels
    /// * `height` - Height of each layer in pixels
    /// * `max_layers` - Maximum number of layers (up to 256)
    ///
    /// # Returns
    ///
    /// A new texture array, or `None` if `max_layers` exceeds the limit.
    pub fn new(
        device: &wgpu::Device,
        texture_array_layout: &wgpu::BindGroupLayout,
        width: u32,
        height: u32,
        max_layers: u32,
    ) -> Option<Self> {
        if max_layers == 0 || max_layers > MAX_TEXTURE_ARRAY_LAYERS {
            return None;
        }

        let texture = device.create_texture(&wgpu::TextureDescriptor {
            label: Some("texture_array"),
            size: wgpu::Extent3d {
                width,
                height,
                depth_or_array_layers: max_layers,
            },
            mip_level_count: 1,
            sample_count: 1,
            dimension: wgpu::TextureDimension::D2,
            format: wgpu::TextureFormat::Rgba8UnormSrgb,
            usage: wgpu::TextureUsages::TEXTURE_BINDING | wgpu::TextureUsages::COPY_DST,
            view_formats: &[],
        });

        let view = texture.create_view(&wgpu::TextureViewDescriptor {
            label: Some("texture_array_view"),
            dimension: Some(wgpu::TextureViewDimension::D2Array),
            ..Default::default()
        });

        let sampler = device.create_sampler(&wgpu::SamplerDescriptor {
            label: Some("texture_array_sampler"),
            address_mode_u: wgpu::AddressMode::ClampToEdge,
            address_mode_v: wgpu::AddressMode::ClampToEdge,
            address_mode_w: wgpu::AddressMode::ClampToEdge,
            mag_filter: wgpu::FilterMode::Linear,
            min_filter: wgpu::FilterMode::Linear,
            mipmap_filter: wgpu::FilterMode::Nearest,
            ..Default::default()
        });

        let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("texture_array_bind_group"),
            layout: texture_array_layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: wgpu::BindingResource::TextureView(&view),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: wgpu::BindingResource::Sampler(&sampler),
                },
            ],
        });

        Some(Self {
            texture,
            view,
            sampler,
            bind_group,
            width,
            height,
            max_layers,
            layer_count: 0,
            extension_map: HashMap::new(),
        })
    }

    /// Creates a texture array with default icon size (32x32).
    pub fn with_default_size(
        device: &wgpu::Device,
        texture_array_layout: &wgpu::BindGroupLayout,
        max_layers: u32,
    ) -> Option<Self> {
        Self::new(
            device,
            texture_array_layout,
            DEFAULT_ICON_SIZE,
            DEFAULT_ICON_SIZE,
            max_layers,
        )
    }

    /// Returns the layer width in pixels.
    #[inline]
    pub fn width(&self) -> u32 {
        self.width
    }

    /// Returns the layer height in pixels.
    #[inline]
    pub fn height(&self) -> u32 {
        self.height
    }

    /// Returns the maximum number of layers.
    #[inline]
    pub fn max_layers(&self) -> u32 {
        self.max_layers
    }

    /// Returns the current number of allocated layers.
    #[inline]
    pub fn layer_count(&self) -> u32 {
        self.layer_count
    }

    /// Returns the bind group for shader access.
    #[inline]
    pub fn bind_group(&self) -> &wgpu::BindGroup {
        &self.bind_group
    }

    /// Returns the texture view.
    #[inline]
    pub fn view(&self) -> &wgpu::TextureView {
        &self.view
    }

    /// Returns the sampler.
    #[inline]
    #[allow(dead_code)]
    pub fn sampler(&self) -> &wgpu::Sampler {
        &self.sampler
    }

    /// Adds a new layer with the given RGBA data.
    ///
    /// # Arguments
    ///
    /// * `queue` - wgpu queue for upload
    /// * `data` - RGBA pixel data (must be `width * height * 4` bytes)
    ///
    /// # Returns
    ///
    /// The layer index, or `None` if the array is full or data is wrong size.
    pub fn add_layer(&mut self, queue: &wgpu::Queue, data: &[u8]) -> Option<u32> {
        let expected_size = (self.width * self.height * 4) as usize;
        if data.len() != expected_size {
            return None;
        }

        if self.layer_count >= self.max_layers {
            return None;
        }

        let layer = self.layer_count;
        self.layer_count += 1;

        queue.write_texture(
            wgpu::TexelCopyTextureInfo {
                texture: &self.texture,
                mip_level: 0,
                origin: wgpu::Origin3d {
                    x: 0,
                    y: 0,
                    z: layer,
                },
                aspect: wgpu::TextureAspect::All,
            },
            data,
            wgpu::TexelCopyBufferLayout {
                offset: 0,
                bytes_per_row: Some(self.width * 4),
                rows_per_image: Some(self.height),
            },
            wgpu::Extent3d {
                width: self.width,
                height: self.height,
                depth_or_array_layers: 1,
            },
        );

        Some(layer)
    }

    /// Registers a file extension and assigns it a layer.
    ///
    /// If the extension is already registered, returns the existing layer index.
    /// If a new layer needs to be added, `icon_data` is uploaded.
    ///
    /// # Arguments
    ///
    /// * `queue` - wgpu queue for upload
    /// * `extension` - File extension (e.g., "rs", "py", "js")
    /// * `icon_data` - RGBA icon data (only used if extension is new)
    ///
    /// # Returns
    ///
    /// The layer index, or `None` if the array is full.
    pub fn register_extension(
        &mut self,
        queue: &wgpu::Queue,
        extension: &str,
        icon_data: &[u8],
    ) -> Option<u32> {
        // Check if already registered
        if let Some(&layer) = self.extension_map.get(extension) {
            return Some(layer);
        }

        // Add new layer
        let layer = self.add_layer(queue, icon_data)?;
        self.extension_map.insert(extension.to_lowercase(), layer);

        Some(layer)
    }

    /// Looks up the layer index for a file extension.
    ///
    /// # Returns
    ///
    /// The layer index, or `None` if the extension is not registered.
    #[inline]
    pub fn get_layer(&self, extension: &str) -> Option<u32> {
        self.extension_map.get(&extension.to_lowercase()).copied()
    }

    /// Checks if an extension is registered.
    #[inline]
    pub fn has_extension(&self, extension: &str) -> bool {
        self.extension_map.contains_key(&extension.to_lowercase())
    }

    /// Returns statistics about the texture array.
    pub fn stats(&self) -> TextureArrayStats {
        TextureArrayStats {
            width: self.width,
            height: self.height,
            layer_count: self.layer_count,
            max_layers: self.max_layers,
            extension_count: self.extension_map.len(),
            bytes_per_layer: self.width * self.height * 4,
            total_bytes: self.width * self.height * 4 * self.layer_count,
        }
    }
}

/// Statistics for a texture array.
#[derive(Debug, Clone, Copy)]
pub struct TextureArrayStats {
    /// Width of each layer.
    pub width: u32,
    /// Height of each layer.
    pub height: u32,
    /// Number of layers currently used.
    pub layer_count: u32,
    /// Maximum number of layers.
    pub max_layers: u32,
    /// Number of registered extensions.
    pub extension_count: usize,
    /// Bytes per layer.
    pub bytes_per_layer: u32,
    /// Total bytes used.
    pub total_bytes: u32,
}

impl TextureArrayStats {
    /// Returns the utilization ratio (0.0 - 1.0).
    #[inline]
    pub fn utilization(&self) -> f32 {
        if self.max_layers == 0 {
            0.0
        } else {
            self.layer_count as f32 / self.max_layers as f32
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_glyph_key_new() {
        let key = GlyphKey::new('A', 12.5);
        assert_eq!(key.ch, 'A');
        assert_eq!(key.size_tenths, 125);
    }

    #[test]
    fn test_glyph_key_size() {
        let key = GlyphKey::new('B', 16.0);
        assert!((key.size() - 16.0).abs() < 0.1);
    }

    #[test]
    fn test_glyph_key_equality() {
        let key1 = GlyphKey::new('A', 12.0);
        let key2 = GlyphKey::new('A', 12.0);
        let key3 = GlyphKey::new('A', 14.0);
        let key4 = GlyphKey::new('B', 12.0);

        assert_eq!(key1, key2);
        assert_ne!(key1, key3);
        assert_ne!(key1, key4);
    }

    #[test]
    fn test_atlas_region_uv_bounds() {
        let region = AtlasRegion {
            x: 0,
            y: 0,
            width: 256,
            height: 256,
        };

        let (u_min, v_min, u_max, v_max) = region.uv_bounds(512);
        assert!((u_min - 0.0).abs() < 0.001);
        assert!((v_min - 0.0).abs() < 0.001);
        assert!((u_max - 0.5).abs() < 0.001);
        assert!((v_max - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_atlas_region_uv_bounds_offset() {
        let region = AtlasRegion {
            x: 256,
            y: 128,
            width: 64,
            height: 32,
        };

        let (u_min, v_min, u_max, v_max) = region.uv_bounds(512);
        assert!((u_min - 0.5).abs() < 0.001);
        assert!((v_min - 0.25).abs() < 0.001);
        assert!((u_max - 0.625).abs() < 0.001);
        assert!((v_max - 0.3125).abs() < 0.001);
    }

    #[test]
    fn test_row_packer_new() {
        let packer = RowPacker::new(512);
        assert_eq!(packer.size, 512);
        assert_eq!(packer.next_row_y, 0);
        assert!(packer.rows.is_empty());
    }

    #[test]
    fn test_row_packer_allocate() {
        let mut packer = RowPacker::new(512);

        let region1 = packer.allocate(100, 50).unwrap();
        assert_eq!(region1.x, 0);
        assert_eq!(region1.y, 0);
        assert_eq!(region1.width, 100);
        assert_eq!(region1.height, 50);

        let region2 = packer.allocate(80, 40).unwrap();
        // Should fit in same row since height <= existing row height
        assert_eq!(region2.x, 100 + GLYPH_PADDING);
        assert_eq!(region2.y, 0);
    }

    #[test]
    fn test_row_packer_new_row() {
        let mut packer = RowPacker::new(512);

        let region1 = packer.allocate(400, 50).unwrap();
        assert_eq!(region1.y, 0);

        // This should start a new row (too wide for existing)
        let region2 = packer.allocate(400, 30).unwrap();
        assert_eq!(region2.x, 0);
        assert_eq!(region2.y, 50 + GLYPH_PADDING);
    }

    #[test]
    fn test_row_packer_full() {
        let mut packer = RowPacker::new(100);

        // Fill the atlas
        let _ = packer.allocate(100, 50);
        let _ = packer.allocate(100, 50);

        // Should fail - no more room
        assert!(packer.allocate(100, 50).is_none());
    }

    #[test]
    fn test_row_packer_reset() {
        let mut packer = RowPacker::new(512);
        let _ = packer.allocate(100, 50);
        let _ = packer.allocate(100, 50);

        packer.reset();

        assert!(packer.rows.is_empty());
        assert_eq!(packer.next_row_y, 0);
    }

    #[test]
    fn test_atlas_stats_utilization() {
        let stats = AtlasStats {
            glyph_count: 10,
            used_pixels: 25_000,
            total_pixels: 100_000,
            size: 316, // sqrt(100_000) ≈ 316
        };

        assert!((stats.utilization() - 0.25).abs() < 0.001);
        assert!((stats.fragmentation() - 0.75).abs() < 0.001);
    }

    #[test]
    fn test_atlas_stats_empty() {
        let stats = AtlasStats {
            glyph_count: 0,
            used_pixels: 0,
            total_pixels: 0,
            size: 0,
        };

        assert!((stats.utilization() - 0.0).abs() < 0.001);
    }

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn test_constants() {
        // Validate compile-time constant relationships
        assert!(INITIAL_ATLAS_SIZE > 0);
        assert!(MAX_ATLAS_SIZE >= INITIAL_ATLAS_SIZE);
        assert!(GLYPH_PADDING >= 1);
        assert!(DEFRAG_THRESHOLD > 0.0 && DEFRAG_THRESHOLD < 1.0);
    }

    // ========================================================================
    // TextureArray tests
    // ========================================================================

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn test_texture_array_constants() {
        assert!(MAX_TEXTURE_ARRAY_LAYERS > 0);
        assert!(MAX_TEXTURE_ARRAY_LAYERS <= 256);
        assert!(DEFAULT_ICON_SIZE > 0);
        assert!(DEFAULT_ICON_SIZE <= 128);
    }

    #[test]
    fn test_texture_array_stats_utilization() {
        let stats = TextureArrayStats {
            width: 32,
            height: 32,
            layer_count: 64,
            max_layers: 256,
            extension_count: 50,
            bytes_per_layer: 32 * 32 * 4,
            total_bytes: 32 * 32 * 4 * 64,
        };

        assert!((stats.utilization() - 0.25).abs() < 0.001);
    }

    #[test]
    fn test_texture_array_stats_empty() {
        let stats = TextureArrayStats {
            width: 32,
            height: 32,
            layer_count: 0,
            max_layers: 256,
            extension_count: 0,
            bytes_per_layer: 32 * 32 * 4,
            total_bytes: 0,
        };

        assert!((stats.utilization() - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_texture_array_stats_full() {
        let stats = TextureArrayStats {
            width: 32,
            height: 32,
            layer_count: 256,
            max_layers: 256,
            extension_count: 200,
            bytes_per_layer: 32 * 32 * 4,
            total_bytes: 32 * 32 * 4 * 256,
        };

        assert!((stats.utilization() - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_texture_array_stats_zero_max() {
        let stats = TextureArrayStats {
            width: 32,
            height: 32,
            layer_count: 0,
            max_layers: 0,
            extension_count: 0,
            bytes_per_layer: 32 * 32 * 4,
            total_bytes: 0,
        };

        assert!((stats.utilization() - 0.0).abs() < 0.001);
    }
}
