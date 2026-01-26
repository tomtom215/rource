// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Flush pass methods for the wgpu renderer.
//!
//! This module contains methods for flushing batched draw calls to the GPU.

use crate::TextureId;

use super::{
    buffers::{self, InstanceBuffer, Uniforms},
    state::{BindGroupId, PipelineId},
    stats::ActivePrimitives,
    WgpuRenderer,
};

impl WgpuRenderer {
    /// Flushes all batched draw calls to the current render pass.
    pub(super) fn flush(
        &mut self,
        encoder: &mut wgpu::CommandEncoder,
        target_view: &wgpu::TextureView,
    ) {
        // Update uniforms
        let uniforms = Uniforms {
            resolution: [self.width as f32, self.height as f32],
            time: 0.0,
            padding: 0.0,
        };
        self.uniform_buffer.update(&self.queue, &uniforms);

        let format = self
            .surface_config
            .as_ref()
            .map(|c| c.format)
            .unwrap_or(wgpu::TextureFormat::Bgra8UnormSrgb);

        // Dispatch GPU culling if enabled (before uploading to avoid duplicate uploads)
        if self.gpu_culling_enabled {
            self.dispatch_culling(encoder);
        }

        // Upload all instance data first (needed for non-culled primitives and fallback)
        self.circle_instances
            .upload(&self.device, &self.queue, &mut self.frame_stats);
        self.ring_instances
            .upload(&self.device, &self.queue, &mut self.frame_stats);
        self.line_instances
            .upload(&self.device, &self.queue, &mut self.frame_stats);
        self.curve_instances
            .upload(&self.device, &self.queue, &mut self.frame_stats);
        self.quad_instances
            .upload(&self.device, &self.queue, &mut self.frame_stats);
        self.text_instances
            .upload(&self.device, &self.queue, &mut self.frame_stats);
        self.file_icon_instances
            .upload(&self.device, &self.queue, &mut self.frame_stats);
        self.avatar_quad_instances
            .upload(&self.device, &self.queue, &mut self.frame_stats);
        self.upload_textured_quads();

        // Upload font atlas texture to GPU (critical for text rendering!)
        self.font_atlas.upload(&self.queue);

        // Create render pass
        {
            let mut render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                label: Some("Main Render Pass"),
                color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                    view: target_view,
                    resolve_target: None,
                    ops: wgpu::Operations {
                        load: wgpu::LoadOp::Load,
                        store: wgpu::StoreOp::Store,
                    },
                    depth_slice: None,
                })],
                depth_stencil_attachment: None,
                timestamp_writes: None,
                occlusion_query_set: None,
                multiview_mask: None,
            });

            // Apply scissor rect if clipping is active
            if let Some(scissor) = self.current_scissor {
                render_pass.set_scissor_rect(scissor.x, scissor.y, scissor.width, scissor.height);
            }

            // Flush each primitive type
            self.flush_circles_pass(&mut render_pass, format);
            self.flush_rings_pass(&mut render_pass, format);
            self.flush_lines_pass(&mut render_pass, format);
            self.flush_curves_pass(&mut render_pass, format);
            self.flush_quads_pass(&mut render_pass, format);
            self.flush_textured_quads_pass(&mut render_pass, format);
            self.flush_avatar_quads_pass(&mut render_pass, format);
            self.flush_texture_array_pass(&mut render_pass, format);
            self.flush_text_pass(&mut render_pass, format);
        }

        // Clear all instance buffers
        self.circle_instances.clear();
        self.ring_instances.clear();
        self.line_instances.clear();
        self.curve_instances.clear();
        self.quad_instances.clear();
        self.text_instances.clear();
        self.file_icon_instances.clear();
        self.avatar_quad_instances.clear();
        self.clear_textured_quads();
    }

    /// Flushes circle draw calls within a render pass.
    ///
    /// When GPU culling is enabled and circles were culled, uses indirect draw
    /// with the culled output buffer. Otherwise, uses the standard instance buffer.
    pub(super) fn flush_circles_pass(
        &mut self,
        render_pass: &mut wgpu::RenderPass<'_>,
        _format: wgpu::TextureFormat,
    ) {
        // Check if we have culled buffers available
        let use_culling = self.culled_circles().is_some();

        // If not using culling, check if we have instances
        if !use_culling && self.circle_instances.is_empty() {
            return;
        }

        let Some(ref mut pipeline_manager) = self.pipeline_manager else {
            return;
        };

        // Get or create pipeline
        let pipeline = pipeline_manager.get_pipeline(&self.device, PipelineId::Circle);

        // Set pipeline
        if self
            .render_state
            .set_pipeline(PipelineId::Circle, &mut self.frame_stats)
        {
            render_pass.set_pipeline(pipeline);
        }

        // Set bind groups (with state caching)
        if self
            .render_state
            .set_bind_group(0, BindGroupId::Uniforms, &mut self.frame_stats)
        {
            render_pass.set_bind_group(0, &self.uniform_bind_group, &[]);
        }

        // Set vertex buffer (unit quad)
        render_pass.set_vertex_buffer(0, self.vertex_buffers.circle_quad.slice(..));

        // Use culled buffer or standard buffer
        if let Some(culled) = self.culled_circles() {
            // Use GPU-culled output buffer and indirect draw
            render_pass.set_vertex_buffer(1, culled.output_slice());
            render_pass.draw_indirect(culled.indirect(), 0);

            // Track statistics (instance count is determined by GPU, use input count)
            let input_count = self.circle_instances.instance_count() as u32;
            self.frame_stats.draw_calls += 1;
            self.frame_stats.circle_instances += input_count;
            self.frame_stats.total_instances += input_count;
        } else {
            // Standard path: use instance buffer directly
            render_pass.set_vertex_buffer(1, self.circle_instances.buffer().slice(..));
            let instance_count = self.circle_instances.instance_count() as u32;
            render_pass.draw(0..4, 0..instance_count);

            // Track statistics
            self.frame_stats.draw_calls += 1;
            self.frame_stats.circle_instances += instance_count;
            self.frame_stats.total_instances += instance_count;
        }

        self.frame_stats
            .active_primitives
            .set(ActivePrimitives::CIRCLES);
    }

    /// Flushes ring draw calls within a render pass.
    pub(super) fn flush_rings_pass(
        &mut self,
        render_pass: &mut wgpu::RenderPass<'_>,
        _format: wgpu::TextureFormat,
    ) {
        if self.ring_instances.is_empty() {
            return;
        }

        let Some(ref mut pipeline_manager) = self.pipeline_manager else {
            return;
        };

        let pipeline = pipeline_manager.get_pipeline(&self.device, PipelineId::Ring);

        if self
            .render_state
            .set_pipeline(PipelineId::Ring, &mut self.frame_stats)
        {
            render_pass.set_pipeline(pipeline);
        }

        if self
            .render_state
            .set_bind_group(0, BindGroupId::Uniforms, &mut self.frame_stats)
        {
            render_pass.set_bind_group(0, &self.uniform_bind_group, &[]);
        }
        render_pass.set_vertex_buffer(0, self.vertex_buffers.circle_quad.slice(..));
        render_pass.set_vertex_buffer(1, self.ring_instances.buffer().slice(..));

        let instance_count = self.ring_instances.instance_count() as u32;
        render_pass.draw(0..4, 0..instance_count);

        self.frame_stats.draw_calls += 1;
        self.frame_stats.ring_instances += instance_count;
        self.frame_stats.total_instances += instance_count;
        self.frame_stats
            .active_primitives
            .set(ActivePrimitives::RINGS);
    }

    /// Flushes line draw calls within a render pass.
    ///
    /// When GPU culling is enabled and lines were culled, uses indirect draw
    /// with the culled output buffer. Otherwise, uses the standard instance buffer.
    pub(super) fn flush_lines_pass(
        &mut self,
        render_pass: &mut wgpu::RenderPass<'_>,
        _format: wgpu::TextureFormat,
    ) {
        // Check if we have culled buffers available
        let use_culling = self.culled_lines().is_some();

        // If not using culling, check if we have instances
        if !use_culling && self.line_instances.is_empty() {
            return;
        }

        let Some(ref mut pipeline_manager) = self.pipeline_manager else {
            return;
        };

        let pipeline = pipeline_manager.get_pipeline(&self.device, PipelineId::Line);

        if self
            .render_state
            .set_pipeline(PipelineId::Line, &mut self.frame_stats)
        {
            render_pass.set_pipeline(pipeline);
        }

        if self
            .render_state
            .set_bind_group(0, BindGroupId::Uniforms, &mut self.frame_stats)
        {
            render_pass.set_bind_group(0, &self.uniform_bind_group, &[]);
        }
        render_pass.set_vertex_buffer(0, self.vertex_buffers.line_quad.slice(..));

        // Use culled buffer or standard buffer
        if let Some(culled) = self.culled_lines() {
            // Use GPU-culled output buffer and indirect draw
            render_pass.set_vertex_buffer(1, culled.output_slice());
            render_pass.draw_indirect(culled.indirect(), 0);

            // Track statistics
            let input_count = self.line_instances.instance_count() as u32;
            self.frame_stats.draw_calls += 1;
            self.frame_stats.line_instances += input_count;
            self.frame_stats.total_instances += input_count;
        } else {
            // Standard path
            render_pass.set_vertex_buffer(1, self.line_instances.buffer().slice(..));
            let instance_count = self.line_instances.instance_count() as u32;
            render_pass.draw(0..4, 0..instance_count);

            self.frame_stats.draw_calls += 1;
            self.frame_stats.line_instances += instance_count;
            self.frame_stats.total_instances += instance_count;
        }

        self.frame_stats
            .active_primitives
            .set(ActivePrimitives::LINES);
    }

    /// Flushes curve draw calls within a render pass.
    pub(super) fn flush_curves_pass(
        &mut self,
        render_pass: &mut wgpu::RenderPass<'_>,
        _format: wgpu::TextureFormat,
    ) {
        if self.curve_instances.is_empty() {
            return;
        }

        let Some(ref mut pipeline_manager) = self.pipeline_manager else {
            return;
        };

        let pipeline = pipeline_manager.get_pipeline(&self.device, PipelineId::Curve);

        if self
            .render_state
            .set_pipeline(PipelineId::Curve, &mut self.frame_stats)
        {
            render_pass.set_pipeline(pipeline);
        }

        if self
            .render_state
            .set_bind_group(0, BindGroupId::Uniforms, &mut self.frame_stats)
        {
            render_pass.set_bind_group(0, &self.uniform_bind_group, &[]);
        }
        render_pass.set_vertex_buffer(0, self.vertex_buffers.curve_strip.slice(..));
        render_pass.set_vertex_buffer(1, self.curve_instances.buffer().slice(..));

        let instance_count = self.curve_instances.instance_count() as u32;
        render_pass.draw(0..buffers::CURVE_STRIP_VERTEX_COUNT, 0..instance_count);

        self.frame_stats.draw_calls += 1;
        self.frame_stats.curve_instances += instance_count;
        self.frame_stats.total_instances += instance_count;
        self.frame_stats
            .active_primitives
            .set(ActivePrimitives::CURVES);
    }

    /// Flushes solid quad draw calls within a render pass.
    ///
    /// When GPU culling is enabled and quads were culled, uses indirect draw
    /// with the culled output buffer. Otherwise, uses the standard instance buffer.
    pub(super) fn flush_quads_pass(
        &mut self,
        render_pass: &mut wgpu::RenderPass<'_>,
        _format: wgpu::TextureFormat,
    ) {
        // Check if we have culled buffers available
        let use_culling = self.culled_quads().is_some();

        // If not using culling, check if we have instances
        if !use_culling && self.quad_instances.is_empty() {
            return;
        }

        let Some(ref mut pipeline_manager) = self.pipeline_manager else {
            return;
        };

        let pipeline = pipeline_manager.get_pipeline(&self.device, PipelineId::Quad);

        if self
            .render_state
            .set_pipeline(PipelineId::Quad, &mut self.frame_stats)
        {
            render_pass.set_pipeline(pipeline);
        }

        if self
            .render_state
            .set_bind_group(0, BindGroupId::Uniforms, &mut self.frame_stats)
        {
            render_pass.set_bind_group(0, &self.uniform_bind_group, &[]);
        }
        render_pass.set_vertex_buffer(0, self.vertex_buffers.standard_quad.slice(..));

        // Use culled buffer or standard buffer
        if let Some(culled) = self.culled_quads() {
            // Use GPU-culled output buffer and indirect draw
            render_pass.set_vertex_buffer(1, culled.output_slice());
            render_pass.draw_indirect(culled.indirect(), 0);

            // Track statistics
            let input_count = self.quad_instances.instance_count() as u32;
            self.frame_stats.draw_calls += 1;
            self.frame_stats.quad_instances += input_count;
            self.frame_stats.total_instances += input_count;
        } else {
            // Standard path
            render_pass.set_vertex_buffer(1, self.quad_instances.buffer().slice(..));
            let instance_count = self.quad_instances.instance_count() as u32;
            render_pass.draw(0..4, 0..instance_count);

            self.frame_stats.draw_calls += 1;
            self.frame_stats.quad_instances += instance_count;
            self.frame_stats.total_instances += instance_count;
        }

        self.frame_stats
            .active_primitives
            .set(ActivePrimitives::QUADS);
    }

    /// Uploads all textured quad instance buffers.
    ///
    /// Uses a cached texture ID buffer to avoid per-frame allocation.
    pub(super) fn upload_textured_quads(&mut self) {
        // Reuse cached buffer - avoids allocation after first frame
        self.cached_texture_ids.clear();
        self.cached_texture_ids
            .extend(self.textured_quad_instances.keys().copied());

        for &tex_id in &self.cached_texture_ids {
            if let Some(instances) = self.textured_quad_instances.get_mut(&tex_id) {
                if !instances.is_empty() {
                    instances.upload(&self.device, &self.queue, &mut self.frame_stats);
                }
            }
        }
    }

    /// Flushes textured quad draw calls within a render pass.
    ///
    /// Reuses `cached_texture_ids` populated by `upload_textured_quads()` to avoid
    /// per-frame Vec allocation.
    pub(super) fn flush_textured_quads_pass(
        &mut self,
        render_pass: &mut wgpu::RenderPass<'_>,
        _format: wgpu::TextureFormat,
    ) {
        let Some(ref mut pipeline_manager) = self.pipeline_manager else {
            return;
        };

        // Check if any textured quads to render (quick scan of cached IDs)
        let has_instances = self.cached_texture_ids.iter().any(|tex_id| {
            self.textured_quad_instances
                .get(tex_id)
                .is_some_and(|b| !b.is_empty())
        });

        if !has_instances {
            return;
        }

        // Get or create pipeline
        let pipeline = pipeline_manager.get_pipeline(&self.device, PipelineId::TexturedQuad);

        // Set pipeline once for all textured quads
        if self
            .render_state
            .set_pipeline(PipelineId::TexturedQuad, &mut self.frame_stats)
        {
            render_pass.set_pipeline(pipeline);
        }

        if self
            .render_state
            .set_bind_group(0, BindGroupId::Uniforms, &mut self.frame_stats)
        {
            render_pass.set_bind_group(0, &self.uniform_bind_group, &[]);
        }

        // Render each texture group using cached IDs (avoids per-frame allocation)
        for i in 0..self.cached_texture_ids.len() {
            let tex_id = self.cached_texture_ids[i];
            let Some(instances) = self.textured_quad_instances.get(&tex_id) else {
                continue;
            };

            // Skip empty buffers (filter during iteration, not pre-filtering)
            if instances.is_empty() {
                continue;
            }

            // Set texture bind group
            if let Some(texture) = self.textures.get(&tex_id) {
                render_pass.set_bind_group(1, &texture.bind_group, &[]);
            }

            render_pass.set_vertex_buffer(0, self.vertex_buffers.standard_quad.slice(..));
            render_pass.set_vertex_buffer(1, instances.buffer().slice(..));

            let instance_count = instances.instance_count() as u32;
            render_pass.draw(0..4, 0..instance_count);

            self.frame_stats.draw_calls += 1;
            self.frame_stats.textured_quad_instances += instance_count;
            self.frame_stats.total_instances += instance_count;
            self.frame_stats
                .active_primitives
                .set(ActivePrimitives::TEXTURED_QUADS);
        }
    }

    /// Clears all textured quad instance buffers.
    pub(super) fn clear_textured_quads(&mut self) {
        for instances in self.textured_quad_instances.values_mut() {
            instances.clear();
        }
    }

    /// Flushes text draw calls within a render pass.
    pub(super) fn flush_text_pass(
        &mut self,
        render_pass: &mut wgpu::RenderPass<'_>,
        _format: wgpu::TextureFormat,
    ) {
        if self.text_instances.is_empty() {
            return;
        }

        let Some(ref mut pipeline_manager) = self.pipeline_manager else {
            return;
        };

        // Get or create pipeline
        let pipeline = pipeline_manager.get_pipeline(&self.device, PipelineId::Text);

        if self
            .render_state
            .set_pipeline(PipelineId::Text, &mut self.frame_stats)
        {
            render_pass.set_pipeline(pipeline);
        }

        if self
            .render_state
            .set_bind_group(0, BindGroupId::Uniforms, &mut self.frame_stats)
        {
            render_pass.set_bind_group(0, &self.uniform_bind_group, &[]);
        }
        if self
            .render_state
            .set_bind_group(1, BindGroupId::FontAtlas, &mut self.frame_stats)
        {
            render_pass.set_bind_group(1, self.font_atlas.bind_group(), &[]);
        }
        render_pass.set_vertex_buffer(0, self.vertex_buffers.standard_quad.slice(..));
        render_pass.set_vertex_buffer(1, self.text_instances.buffer().slice(..));

        let instance_count = self.text_instances.instance_count() as u32;
        render_pass.draw(0..4, 0..instance_count);

        self.frame_stats.draw_calls += 1;
        self.frame_stats.text_instances += instance_count;
        self.frame_stats.total_instances += instance_count;
        self.frame_stats
            .active_primitives
            .set(ActivePrimitives::TEXT);
    }

    /// Gets or creates an instance buffer for a specific texture.
    pub(super) fn get_or_create_textured_quad_buffer(
        &mut self,
        tex_id: TextureId,
    ) -> &mut InstanceBuffer {
        self.textured_quad_instances
            .entry(tex_id)
            .or_insert_with(|| {
                InstanceBuffer::new(&self.device, 12, 100, "textured_quad_instances")
                // 12 floats = 48 bytes
            })
    }

    /// Flushes avatar texture array draw calls within a render pass.
    ///
    /// This method renders all queued avatar quads in a single instanced draw call,
    /// using the avatar texture array to batch all user avatars together.
    /// This is the key optimization that reduces draw calls from N (one per avatar)
    /// to 1 (single batched draw call).
    pub(super) fn flush_avatar_quads_pass(
        &mut self,
        render_pass: &mut wgpu::RenderPass<'_>,
        _format: wgpu::TextureFormat,
    ) {
        if self.avatar_quad_instances.is_empty() {
            return;
        }

        // Need avatar texture array to be initialized
        let Some(ref avatar_array) = self.avatar_texture_array else {
            return;
        };

        let Some(ref mut pipeline_manager) = self.pipeline_manager else {
            return;
        };

        // Get or create pipeline (reuse TextureArray pipeline since format is identical)
        let pipeline = pipeline_manager.get_pipeline(&self.device, PipelineId::TextureArray);

        if self
            .render_state
            .set_pipeline(PipelineId::TextureArray, &mut self.frame_stats)
        {
            render_pass.set_pipeline(pipeline);
        }

        // Set bind groups (with state caching)
        if self
            .render_state
            .set_bind_group(0, BindGroupId::Uniforms, &mut self.frame_stats)
        {
            render_pass.set_bind_group(0, &self.uniform_bind_group, &[]);
        }
        if self
            .render_state
            .set_bind_group(1, BindGroupId::AvatarArray, &mut self.frame_stats)
        {
            render_pass.set_bind_group(1, avatar_array.bind_group(), &[]);
        }

        // Set vertex and instance buffers
        render_pass.set_vertex_buffer(0, self.vertex_buffers.standard_quad.slice(..));
        render_pass.set_vertex_buffer(1, self.avatar_quad_instances.buffer().slice(..));

        // Draw all avatars in one instanced call
        let instance_count = self.avatar_quad_instances.instance_count() as u32;
        render_pass.draw(0..4, 0..instance_count);

        // Track statistics
        self.frame_stats.draw_calls += 1;
        self.frame_stats.texture_array_instances += instance_count;
        self.frame_stats.total_instances += instance_count;
        self.frame_stats
            .active_primitives
            .set(ActivePrimitives::TEXTURE_ARRAYS);
    }

    /// Flushes texture array (file icon) draw calls within a render pass.
    ///
    /// This method renders all queued file icons in a single instanced draw call,
    /// using the texture array to batch different file types together.
    pub(super) fn flush_texture_array_pass(
        &mut self,
        render_pass: &mut wgpu::RenderPass<'_>,
        _format: wgpu::TextureFormat,
    ) {
        if self.file_icon_instances.is_empty() {
            return;
        }

        // Need file icon array to be initialized
        let Some(ref file_icon_array) = self.file_icon_array else {
            return;
        };

        let Some(ref mut pipeline_manager) = self.pipeline_manager else {
            return;
        };

        // Get or create pipeline
        let pipeline = pipeline_manager.get_pipeline(&self.device, PipelineId::TextureArray);

        if self
            .render_state
            .set_pipeline(PipelineId::TextureArray, &mut self.frame_stats)
        {
            render_pass.set_pipeline(pipeline);
        }

        // Set bind groups (with state caching)
        if self
            .render_state
            .set_bind_group(0, BindGroupId::Uniforms, &mut self.frame_stats)
        {
            render_pass.set_bind_group(0, &self.uniform_bind_group, &[]);
        }
        if self
            .render_state
            .set_bind_group(1, BindGroupId::FileIconArray, &mut self.frame_stats)
        {
            render_pass.set_bind_group(1, file_icon_array.bind_group(), &[]);
        }

        // Set vertex and instance buffers
        render_pass.set_vertex_buffer(0, self.vertex_buffers.standard_quad.slice(..));
        render_pass.set_vertex_buffer(1, self.file_icon_instances.buffer().slice(..));

        // Draw all file icons in one instanced call
        let instance_count = self.file_icon_instances.instance_count() as u32;
        render_pass.draw(0..4, 0..instance_count);

        // Track statistics
        self.frame_stats.draw_calls += 1;
        self.frame_stats.texture_array_instances += instance_count;
        self.frame_stats.total_instances += instance_count;
        self.frame_stats
            .active_primitives
            .set(ActivePrimitives::TEXTURE_ARRAYS);
    }
}
