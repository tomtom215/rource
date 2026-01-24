// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! GPU state caching for wgpu renderer.
//!
//! This module provides state tracking to minimize redundant GPU API calls.
//! By caching the current state of pipelines, bind groups, and buffers,
//! we can skip unnecessary binds that wouldn't change any state.
//!
//! ## Performance Impact
//!
//! While wgpu's validation layer would catch redundant binds anyway,
//! avoiding them at the application level provides several benefits:
//!
//! - Reduces CPU overhead from parameter validation
//! - Allows tracking statistics about cache hit rates
//! - Makes render pass logic cleaner by separating state management
//!
//! ## Usage
//!
//! ```ignore
//! let mut state = RenderState::new();
//! state.begin_frame(1920, 1080);
//!
//! // Only binds if pipeline changed
//! if state.set_pipeline(PipelineId::Circle) {
//!     render_pass.set_pipeline(&circle_pipeline);
//! }
//! ```

use super::stats::FrameStats;

/// Unique identifier for render pipelines.
///
/// Each primitive type has a dedicated pipeline with its own shaders
/// and vertex layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum PipelineId {
    /// Filled circle rendering pipeline.
    Circle = 0,
    /// Circle outline (ring) rendering pipeline.
    Ring = 1,
    /// Anti-aliased line rendering pipeline.
    Line = 2,
    /// Solid colored quad rendering pipeline.
    Quad = 3,
    /// Textured quad rendering pipeline.
    TexturedQuad = 4,
    /// Text glyph rendering pipeline.
    Text = 5,
    /// Bloom bright pass extraction pipeline.
    BloomBright = 6,
    /// Bloom blur pass pipeline (horizontal/vertical).
    BloomBlur = 7,
    /// Bloom composite pass pipeline.
    BloomComposite = 8,
    /// Shadow silhouette extraction pipeline.
    ShadowSilhouette = 9,
    /// Shadow blur pass pipeline.
    ShadowBlur = 10,
    /// Shadow composite pass pipeline.
    ShadowComposite = 11,
    /// Catmull-Rom curve rendering pipeline.
    Curve = 12,
    /// Texture array rendering pipeline (for file icons).
    TextureArray = 13,
}

impl PipelineId {
    /// Returns all primitive pipeline IDs (excluding post-processing and special pipelines).
    ///
    /// Note: `TextureArray` is excluded because it requires special creation with a
    /// texture array bind group layout. It should be created through dedicated methods.
    pub const fn primitives() -> [Self; 7] {
        [
            Self::Circle,
            Self::Ring,
            Self::Line,
            Self::Quad,
            Self::TexturedQuad,
            Self::Text,
            Self::Curve,
        ]
    }

    /// Returns all bloom pipeline IDs.
    pub const fn bloom_pipelines() -> [Self; 3] {
        [Self::BloomBright, Self::BloomBlur, Self::BloomComposite]
    }

    /// Returns all shadow pipeline IDs.
    pub const fn shadow_pipelines() -> [Self; 3] {
        [
            Self::ShadowSilhouette,
            Self::ShadowBlur,
            Self::ShadowComposite,
        ]
    }

    /// Returns the total number of pipeline types.
    pub const fn count() -> usize {
        14
    }
}

/// Unique identifier for bind groups.
///
/// Bind groups contain uniform buffers, textures, and samplers that
/// are bound together for efficient GPU access.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum BindGroupId {
    /// Common uniforms (resolution, time, etc.) at group 0.
    Uniforms = 0,
    /// Font atlas texture and sampler at group 1.
    FontAtlas = 1,
    /// User texture at group 1 (mutually exclusive with `FontAtlas`).
    UserTexture = 2,
    /// Bloom scene texture for bright pass.
    BloomScene = 3,
    /// Bloom intermediate texture A.
    BloomTextureA = 4,
    /// Bloom intermediate texture B.
    BloomTextureB = 5,
    /// Shadow scene texture.
    ShadowScene = 6,
    /// Shadow intermediate texture.
    ShadowTexture = 7,
    /// File icon texture array at group 1.
    FileIconArray = 8,
}

impl BindGroupId {
    /// Returns the bind group slot (0-3) for this ID.
    ///
    /// Most bind groups use slot 0 for uniforms and slot 1 for textures.
    pub const fn slot(&self) -> u32 {
        match self {
            Self::Uniforms => 0,
            Self::FontAtlas
            | Self::UserTexture
            | Self::BloomScene
            | Self::BloomTextureA
            | Self::BloomTextureB
            | Self::ShadowScene
            | Self::ShadowTexture
            | Self::FileIconArray => 1,
        }
    }
}

/// Maximum number of bind group slots (wgpu limit is typically 4).
const MAX_BIND_GROUP_SLOTS: usize = 4;

/// Cached GPU render state.
///
/// Tracks the currently bound pipeline, bind groups, and buffers to avoid
/// redundant API calls. State is invalidated at the start of each frame
/// or when explicitly reset.
#[derive(Debug)]
pub struct RenderState {
    /// Currently bound render pipeline.
    current_pipeline: Option<PipelineId>,

    /// Currently bound bind groups per slot.
    current_bind_groups: [Option<BindGroupId>; MAX_BIND_GROUP_SLOTS],

    /// Cached viewport dimensions.
    viewport: (u32, u32),

    /// Whether state has been invalidated and needs full rebind.
    invalidated: bool,
}

impl RenderState {
    /// Creates a new render state with no bindings.
    pub const fn new() -> Self {
        Self {
            current_pipeline: None,
            current_bind_groups: [None; MAX_BIND_GROUP_SLOTS],
            viewport: (0, 0),
            invalidated: true,
        }
    }

    /// Prepares state tracking for a new frame.
    ///
    /// This invalidates all cached state since render passes start fresh.
    /// The viewport dimensions are stored for uniform buffer updates.
    pub fn begin_frame(&mut self, width: u32, height: u32) {
        self.current_pipeline = None;
        self.current_bind_groups = [None; MAX_BIND_GROUP_SLOTS];
        self.viewport = (width, height);
        self.invalidated = false;
    }

    /// Returns the cached viewport dimensions.
    #[inline]
    pub const fn viewport(&self) -> (u32, u32) {
        self.viewport
    }

    /// Returns whether state tracking is invalidated.
    #[inline]
    pub const fn is_invalidated(&self) -> bool {
        self.invalidated
    }

    /// Marks all state as invalidated.
    ///
    /// Call this when GPU state may have changed externally
    /// (e.g., after post-processing passes).
    pub fn invalidate(&mut self) {
        self.current_pipeline = None;
        self.current_bind_groups = [None; MAX_BIND_GROUP_SLOTS];
        self.invalidated = true;
    }

    /// Attempts to set the current pipeline.
    ///
    /// Returns `true` if the pipeline needs to be bound (changed),
    /// `false` if it's already bound (cached). Also updates frame stats.
    ///
    /// # Arguments
    ///
    /// * `id` - The pipeline to bind
    /// * `stats` - Frame statistics to update
    ///
    /// # Returns
    ///
    /// `true` if caller should actually bind the pipeline, `false` if skipped.
    #[inline]
    pub fn set_pipeline(&mut self, id: PipelineId, stats: &mut FrameStats) -> bool {
        if self.current_pipeline == Some(id) {
            stats.skipped_pipeline_binds += 1;
            false
        } else {
            self.current_pipeline = Some(id);
            stats.pipeline_switches += 1;
            true
        }
    }

    /// Attempts to set a bind group at the given slot.
    ///
    /// Returns `true` if the bind group needs to be bound (changed),
    /// `false` if it's already bound (cached). Also updates frame stats.
    ///
    /// # Arguments
    ///
    /// * `slot` - The bind group slot (0-3)
    /// * `id` - The bind group to bind
    /// * `stats` - Frame statistics to update
    ///
    /// # Returns
    ///
    /// `true` if caller should actually bind the group, `false` if skipped.
    ///
    /// # Panics
    ///
    /// Panics if slot >= 4 in debug builds.
    #[inline]
    pub fn set_bind_group(&mut self, slot: usize, id: BindGroupId, stats: &mut FrameStats) -> bool {
        debug_assert!(slot < MAX_BIND_GROUP_SLOTS, "Bind group slot out of range");

        if self.current_bind_groups[slot] == Some(id) {
            stats.skipped_bind_group_binds += 1;
            false
        } else {
            self.current_bind_groups[slot] = Some(id);
            stats.bind_group_switches += 1;
            true
        }
    }

    /// Returns the currently bound pipeline, if any.
    #[inline]
    pub const fn current_pipeline(&self) -> Option<PipelineId> {
        self.current_pipeline
    }

    /// Returns the currently bound bind group at the given slot, if any.
    #[inline]
    pub const fn current_bind_group(&self, slot: usize) -> Option<BindGroupId> {
        if slot < MAX_BIND_GROUP_SLOTS {
            self.current_bind_groups[slot]
        } else {
            None
        }
    }

    /// Clears all bind group state.
    ///
    /// Useful when starting a new render pass or switching between
    /// render and compute passes.
    pub fn clear_bind_groups(&mut self) {
        self.current_bind_groups = [None; MAX_BIND_GROUP_SLOTS];
    }

    /// Clears only the bind group at the given slot.
    #[inline]
    pub fn clear_bind_group(&mut self, slot: usize) {
        if slot < MAX_BIND_GROUP_SLOTS {
            self.current_bind_groups[slot] = None;
        }
    }
}

impl Default for RenderState {
    fn default() -> Self {
        Self::new()
    }
}

/// Compute pipeline state cache.
///
/// Separate from render state since compute passes have different
/// binding semantics.
#[derive(Debug)]
pub struct ComputeState {
    /// Currently bound compute pipeline.
    current_pipeline: Option<ComputePipelineId>,

    /// Currently bound bind groups per slot.
    current_bind_groups: [Option<ComputeBindGroupId>; MAX_BIND_GROUP_SLOTS],
}

/// Unique identifier for compute pipelines.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ComputePipelineId {
    /// Force calculation pass.
    ForceCalculation = 0,
    /// Position integration pass.
    PositionIntegration = 1,
    /// Bounds calculation pass.
    BoundsCalculation = 2,
}

/// Unique identifier for compute bind groups.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ComputeBindGroupId {
    /// Physics simulation parameters.
    PhysicsParams = 0,
    /// Entity position buffer.
    Positions = 1,
    /// Entity velocity buffer.
    Velocities = 2,
    /// Force accumulator buffer.
    Forces = 3,
    /// Spatial hash grid buffer.
    SpatialHash = 4,
}

impl ComputeState {
    /// Creates a new compute state with no bindings.
    pub const fn new() -> Self {
        Self {
            current_pipeline: None,
            current_bind_groups: [None; MAX_BIND_GROUP_SLOTS],
        }
    }

    /// Prepares state tracking for a new frame.
    pub fn begin_frame(&mut self) {
        self.current_pipeline = None;
        self.current_bind_groups = [None; MAX_BIND_GROUP_SLOTS];
    }

    /// Attempts to set the current compute pipeline.
    #[inline]
    pub fn set_pipeline(&mut self, id: ComputePipelineId, stats: &mut FrameStats) -> bool {
        if self.current_pipeline == Some(id) {
            stats.skipped_pipeline_binds += 1;
            false
        } else {
            self.current_pipeline = Some(id);
            stats.pipeline_switches += 1;
            true
        }
    }

    /// Attempts to set a compute bind group at the given slot.
    #[inline]
    pub fn set_bind_group(
        &mut self,
        slot: usize,
        id: ComputeBindGroupId,
        stats: &mut FrameStats,
    ) -> bool {
        debug_assert!(slot < MAX_BIND_GROUP_SLOTS, "Bind group slot out of range");

        if self.current_bind_groups[slot] == Some(id) {
            stats.skipped_bind_group_binds += 1;
            false
        } else {
            self.current_bind_groups[slot] = Some(id);
            stats.bind_group_switches += 1;
            true
        }
    }

    /// Invalidates all compute state.
    pub fn invalidate(&mut self) {
        self.current_pipeline = None;
        self.current_bind_groups = [None; MAX_BIND_GROUP_SLOTS];
    }
}

impl Default for ComputeState {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_render_state_new() {
        let state = RenderState::new();
        assert!(state.current_pipeline.is_none());
        assert!(state.is_invalidated());
        assert_eq!(state.viewport(), (0, 0));
    }

    #[test]
    fn test_render_state_begin_frame() {
        let mut state = RenderState::new();
        state.begin_frame(1920, 1080);

        assert!(!state.is_invalidated());
        assert_eq!(state.viewport(), (1920, 1080));
        assert!(state.current_pipeline.is_none());
    }

    #[test]
    fn test_render_state_set_pipeline_changed() {
        let mut state = RenderState::new();
        let mut stats = FrameStats::new();
        state.begin_frame(800, 600);

        let changed = state.set_pipeline(PipelineId::Circle, &mut stats);

        assert!(changed);
        assert_eq!(stats.pipeline_switches, 1);
        assert_eq!(stats.skipped_pipeline_binds, 0);
        assert_eq!(state.current_pipeline(), Some(PipelineId::Circle));
    }

    #[test]
    fn test_render_state_set_pipeline_cached() {
        let mut state = RenderState::new();
        let mut stats = FrameStats::new();
        state.begin_frame(800, 600);

        state.set_pipeline(PipelineId::Circle, &mut stats);
        let changed = state.set_pipeline(PipelineId::Circle, &mut stats);

        assert!(!changed);
        assert_eq!(stats.pipeline_switches, 1);
        assert_eq!(stats.skipped_pipeline_binds, 1);
    }

    #[test]
    fn test_render_state_set_pipeline_different() {
        let mut state = RenderState::new();
        let mut stats = FrameStats::new();
        state.begin_frame(800, 600);

        state.set_pipeline(PipelineId::Circle, &mut stats);
        let changed = state.set_pipeline(PipelineId::Line, &mut stats);

        assert!(changed);
        assert_eq!(stats.pipeline_switches, 2);
        assert_eq!(state.current_pipeline(), Some(PipelineId::Line));
    }

    #[test]
    fn test_render_state_set_bind_group_changed() {
        let mut state = RenderState::new();
        let mut stats = FrameStats::new();
        state.begin_frame(800, 600);

        let changed = state.set_bind_group(0, BindGroupId::Uniforms, &mut stats);

        assert!(changed);
        assert_eq!(stats.bind_group_switches, 1);
        assert_eq!(stats.skipped_bind_group_binds, 0);
        assert_eq!(state.current_bind_group(0), Some(BindGroupId::Uniforms));
    }

    #[test]
    fn test_render_state_set_bind_group_cached() {
        let mut state = RenderState::new();
        let mut stats = FrameStats::new();
        state.begin_frame(800, 600);

        state.set_bind_group(0, BindGroupId::Uniforms, &mut stats);
        let changed = state.set_bind_group(0, BindGroupId::Uniforms, &mut stats);

        assert!(!changed);
        assert_eq!(stats.bind_group_switches, 1);
        assert_eq!(stats.skipped_bind_group_binds, 1);
    }

    #[test]
    fn test_render_state_invalidate() {
        let mut state = RenderState::new();
        let mut stats = FrameStats::new();
        state.begin_frame(800, 600);
        state.set_pipeline(PipelineId::Circle, &mut stats);
        state.set_bind_group(0, BindGroupId::Uniforms, &mut stats);

        state.invalidate();

        assert!(state.is_invalidated());
        assert!(state.current_pipeline.is_none());
        assert!(state.current_bind_group(0).is_none());
    }

    #[test]
    fn test_render_state_clear_bind_groups() {
        let mut state = RenderState::new();
        let mut stats = FrameStats::new();
        state.begin_frame(800, 600);
        state.set_bind_group(0, BindGroupId::Uniforms, &mut stats);
        state.set_bind_group(1, BindGroupId::FontAtlas, &mut stats);

        state.clear_bind_groups();

        assert!(state.current_bind_group(0).is_none());
        assert!(state.current_bind_group(1).is_none());
    }

    #[test]
    fn test_render_state_clear_bind_group_single() {
        let mut state = RenderState::new();
        let mut stats = FrameStats::new();
        state.begin_frame(800, 600);
        state.set_bind_group(0, BindGroupId::Uniforms, &mut stats);
        state.set_bind_group(1, BindGroupId::FontAtlas, &mut stats);

        state.clear_bind_group(0);

        assert!(state.current_bind_group(0).is_none());
        assert_eq!(state.current_bind_group(1), Some(BindGroupId::FontAtlas));
    }

    #[test]
    fn test_pipeline_id_primitives() {
        let primitives = PipelineId::primitives();
        // TextureArray is excluded because it requires special creation
        assert_eq!(primitives.len(), 7);
        assert_eq!(primitives[0], PipelineId::Circle);
        assert_eq!(primitives[5], PipelineId::Text);
        assert_eq!(primitives[6], PipelineId::Curve);
    }

    #[test]
    fn test_pipeline_id_bloom() {
        let bloom = PipelineId::bloom_pipelines();
        assert_eq!(bloom.len(), 3);
    }

    #[test]
    fn test_pipeline_id_shadow() {
        let shadow = PipelineId::shadow_pipelines();
        assert_eq!(shadow.len(), 3);
    }

    #[test]
    fn test_pipeline_id_count() {
        assert_eq!(PipelineId::count(), 14);
    }

    #[test]
    fn test_bind_group_id_slot() {
        assert_eq!(BindGroupId::Uniforms.slot(), 0);
        assert_eq!(BindGroupId::FontAtlas.slot(), 1);
        assert_eq!(BindGroupId::UserTexture.slot(), 1);
    }

    #[test]
    fn test_compute_state_new() {
        let state = ComputeState::new();
        assert!(state.current_pipeline.is_none());
    }

    #[test]
    fn test_compute_state_set_pipeline() {
        let mut state = ComputeState::new();
        let mut stats = FrameStats::new();
        state.begin_frame();

        let changed = state.set_pipeline(ComputePipelineId::ForceCalculation, &mut stats);

        assert!(changed);
        assert_eq!(stats.pipeline_switches, 1);
    }

    #[test]
    fn test_compute_state_set_bind_group() {
        let mut state = ComputeState::new();
        let mut stats = FrameStats::new();
        state.begin_frame();

        let changed = state.set_bind_group(0, ComputeBindGroupId::PhysicsParams, &mut stats);

        assert!(changed);
        assert_eq!(stats.bind_group_switches, 1);
    }

    #[test]
    fn test_compute_state_invalidate() {
        let mut state = ComputeState::new();
        let mut stats = FrameStats::new();
        state.begin_frame();
        state.set_pipeline(ComputePipelineId::ForceCalculation, &mut stats);

        state.invalidate();

        assert!(state.current_pipeline.is_none());
    }

    #[test]
    fn test_render_state_default() {
        let state = RenderState::default();
        assert!(state.current_pipeline.is_none());
    }

    #[test]
    fn test_compute_state_default() {
        let state = ComputeState::default();
        assert!(state.current_pipeline.is_none());
    }
}
