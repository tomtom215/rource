//! Flush pass methods for the WebGL2 renderer.
//!
//! This module contains methods for flushing batched draw calls to the GPU.

use web_sys::WebGl2RenderingContext;

use super::{stats::ActivePrimitives, WebGl2Renderer};

impl WebGl2Renderer {
    /// Flushes all batched draw calls.
    pub(super) fn flush(&mut self) {
        self.flush_circles();
        self.flush_rings();
        self.flush_lines();
        self.flush_quads();
        self.flush_textured_quads();
        self.flush_text();
    }

    /// Flushes circle draw calls.
    pub(super) fn flush_circles(&mut self) {
        if self.circle_instances.instance_count() == 0 {
            return;
        }

        let Some(program) = &self.circle_program else {
            return;
        };

        let gl = &self.gl;

        // Upload instance data
        self.circle_instances.upload(gl);

        // Setup VAO if needed
        if self.vao_manager.circle_vao.is_none() {
            self.vao_manager
                .setup_circle_vao(gl, &self.circle_instances);
        }

        // Use program (state cache avoids redundant bind)
        let program_changed = self.state_cache.use_program(gl, &program.program);
        if program_changed {
            self.frame_stats.program_switches += 1;
        } else {
            self.frame_stats.skipped_program_binds += 1;
        }

        // Bind VAO (state cache avoids redundant bind)
        let vao_changed = self
            .state_cache
            .bind_vao(gl, self.vao_manager.circle_vao.as_ref());
        if vao_changed {
            self.frame_stats.vao_switches += 1;
        } else {
            self.frame_stats.skipped_vao_binds += 1;
        }

        // Set uniforms only if program changed (legacy mode only)
        if program_changed {
            if let Some(loc) = &program.resolution_loc {
                let (w, h) = self.state_cache.resolution();
                gl.uniform2f(Some(loc), w, h);
                self.frame_stats.uniform_calls += 1;
            }
        }

        // Draw instanced
        let instance_count = self.circle_instances.instance_count();
        gl.draw_arrays_instanced(
            WebGl2RenderingContext::TRIANGLE_STRIP,
            0,
            4,
            instance_count as i32,
        );

        // Track statistics
        self.frame_stats.draw_calls += 1;
        self.frame_stats.circle_instances += instance_count as u32;
        self.frame_stats.total_instances += instance_count as u32;
        self.frame_stats
            .active_primitives
            .set(ActivePrimitives::CIRCLES);

        self.circle_instances.clear();
    }

    /// Flushes ring (circle outline) draw calls.
    pub(super) fn flush_rings(&mut self) {
        if self.ring_instances.instance_count() == 0 {
            return;
        }

        let Some(program) = &self.ring_program else {
            return;
        };

        let gl = &self.gl;

        self.ring_instances.upload(gl);

        if self.vao_manager.ring_vao.is_none() {
            self.vao_manager.setup_ring_vao(gl, &self.ring_instances);
        }

        // Use program (state cache avoids redundant bind)
        let program_changed = self.state_cache.use_program(gl, &program.program);
        if program_changed {
            self.frame_stats.program_switches += 1;
        } else {
            self.frame_stats.skipped_program_binds += 1;
        }

        // Bind VAO (state cache avoids redundant bind)
        let vao_changed = self
            .state_cache
            .bind_vao(gl, self.vao_manager.ring_vao.as_ref());
        if vao_changed {
            self.frame_stats.vao_switches += 1;
        } else {
            self.frame_stats.skipped_vao_binds += 1;
        }

        // Set uniforms only if program changed (legacy mode only)
        if program_changed {
            if let Some(loc) = &program.resolution_loc {
                let (w, h) = self.state_cache.resolution();
                gl.uniform2f(Some(loc), w, h);
                self.frame_stats.uniform_calls += 1;
            }
        }

        let instance_count = self.ring_instances.instance_count();
        gl.draw_arrays_instanced(
            WebGl2RenderingContext::TRIANGLE_STRIP,
            0,
            4,
            instance_count as i32,
        );

        // Track statistics
        self.frame_stats.draw_calls += 1;
        self.frame_stats.ring_instances += instance_count as u32;
        self.frame_stats.total_instances += instance_count as u32;
        self.frame_stats
            .active_primitives
            .set(ActivePrimitives::RINGS);

        self.ring_instances.clear();
    }

    /// Flushes line draw calls.
    pub(super) fn flush_lines(&mut self) {
        if self.line_instances.instance_count() == 0 {
            return;
        }

        let Some(program) = &self.line_program else {
            return;
        };

        let gl = &self.gl;

        self.line_instances.upload(gl);

        if self.vao_manager.line_vao.is_none() {
            self.vao_manager.setup_line_vao(gl, &self.line_instances);
        }

        // Use program (state cache avoids redundant bind)
        let program_changed = self.state_cache.use_program(gl, &program.program);
        if program_changed {
            self.frame_stats.program_switches += 1;
        } else {
            self.frame_stats.skipped_program_binds += 1;
        }

        // Bind VAO (state cache avoids redundant bind)
        let vao_changed = self
            .state_cache
            .bind_vao(gl, self.vao_manager.line_vao.as_ref());
        if vao_changed {
            self.frame_stats.vao_switches += 1;
        } else {
            self.frame_stats.skipped_vao_binds += 1;
        }

        // Set uniforms only if program changed (legacy mode only)
        if program_changed {
            if let Some(loc) = &program.resolution_loc {
                let (w, h) = self.state_cache.resolution();
                gl.uniform2f(Some(loc), w, h);
                self.frame_stats.uniform_calls += 1;
            }
        }

        let instance_count = self.line_instances.instance_count();
        gl.draw_arrays_instanced(
            WebGl2RenderingContext::TRIANGLE_STRIP,
            0,
            4,
            instance_count as i32,
        );

        // Track statistics
        self.frame_stats.draw_calls += 1;
        self.frame_stats.line_instances += instance_count as u32;
        self.frame_stats.total_instances += instance_count as u32;
        self.frame_stats
            .active_primitives
            .set(ActivePrimitives::LINES);

        self.line_instances.clear();
    }

    /// Flushes solid quad draw calls.
    pub(super) fn flush_quads(&mut self) {
        if self.quad_instances.instance_count() == 0 {
            return;
        }

        let Some(program) = &self.quad_program else {
            return;
        };

        let gl = &self.gl;

        self.quad_instances.upload(gl);

        if self.vao_manager.quad_vao.is_none() {
            self.vao_manager.setup_quad_vao(gl, &self.quad_instances);
        }

        // Use program (state cache avoids redundant bind)
        let program_changed = self.state_cache.use_program(gl, &program.program);
        if program_changed {
            self.frame_stats.program_switches += 1;
        } else {
            self.frame_stats.skipped_program_binds += 1;
        }

        // Bind VAO (state cache avoids redundant bind)
        let vao_changed = self
            .state_cache
            .bind_vao(gl, self.vao_manager.quad_vao.as_ref());
        if vao_changed {
            self.frame_stats.vao_switches += 1;
        } else {
            self.frame_stats.skipped_vao_binds += 1;
        }

        // Set uniforms only if program changed (legacy mode only)
        if program_changed {
            if let Some(loc) = &program.resolution_loc {
                let (w, h) = self.state_cache.resolution();
                gl.uniform2f(Some(loc), w, h);
                self.frame_stats.uniform_calls += 1;
            }
        }

        let instance_count = self.quad_instances.instance_count();
        gl.draw_arrays_instanced(
            WebGl2RenderingContext::TRIANGLE_STRIP,
            0,
            4,
            instance_count as i32,
        );

        // Track statistics
        self.frame_stats.draw_calls += 1;
        self.frame_stats.quad_instances += instance_count as u32;
        self.frame_stats.total_instances += instance_count as u32;
        self.frame_stats
            .active_primitives
            .set(ActivePrimitives::QUADS);

        self.quad_instances.clear();
    }

    /// Flushes textured quad draw calls.
    pub(super) fn flush_textured_quads(&mut self) {
        if self.textured_quad_instances.is_empty() {
            return;
        }

        let Some(program) = &self.textured_quad_program else {
            return;
        };

        let gl = &self.gl;

        // Use program (state cache avoids redundant bind)
        let program_changed = self.state_cache.use_program(gl, &program.program);
        if program_changed {
            self.frame_stats.program_switches += 1;
        } else {
            self.frame_stats.skipped_program_binds += 1;
        }

        // Set uniforms only if program changed (legacy mode only)
        if program_changed {
            if let Some(loc) = &program.resolution_loc {
                let (w, h) = self.state_cache.resolution();
                gl.uniform2f(Some(loc), w, h);
                self.frame_stats.uniform_calls += 1;
            }

            if let Some(loc) = &program.texture_loc {
                gl.uniform1i(Some(loc), 0); // Texture unit 0
            }
        }

        // Track whether any textured quads were rendered
        let mut rendered_any = false;

        // Reuse cached buffer - avoids allocation after first frame
        self.cached_texture_ids.clear();
        self.cached_texture_ids
            .extend(self.textured_quad_instances.keys().copied());

        for &tex_id in &self.cached_texture_ids {
            if let Some(instances) = self.textured_quad_instances.get_mut(&tex_id) {
                if instances.instance_count() == 0 {
                    continue;
                }

                rendered_any = true;
                instances.upload(gl);

                // Bind texture (state cache tracks bound textures)
                self.texture_manager.bind(gl, tex_id, 0);
                self.frame_stats.texture_binds += 1;

                // Setup VAO if needed
                if self.vao_manager.textured_quad_vao.is_none() {
                    self.vao_manager.setup_textured_vao(gl, instances);
                }

                // Bind VAO (state cache avoids redundant bind)
                let vao_changed = self
                    .state_cache
                    .bind_vao(gl, self.vao_manager.textured_quad_vao.as_ref());
                if vao_changed {
                    self.frame_stats.vao_switches += 1;
                } else {
                    self.frame_stats.skipped_vao_binds += 1;
                }

                let instance_count = instances.instance_count();
                gl.draw_arrays_instanced(
                    WebGl2RenderingContext::TRIANGLE_STRIP,
                    0,
                    4,
                    instance_count as i32,
                );

                // Track statistics
                self.frame_stats.draw_calls += 1;
                self.frame_stats.textured_quad_instances += instance_count as u32;
                self.frame_stats.total_instances += instance_count as u32;

                instances.clear();
            }
        }

        if rendered_any {
            self.frame_stats
                .active_primitives
                .set(ActivePrimitives::TEXTURED_QUADS);
        }
    }

    /// Flushes text draw calls.
    pub(super) fn flush_text(&mut self) {
        if self.text_instances.instance_count() == 0 {
            return;
        }

        let Some(program) = &self.text_program else {
            return;
        };

        let gl = &self.gl;

        // Upload font atlas
        self.font_atlas.upload(gl);
        self.text_instances.upload(gl);

        // Setup VAO if needed (reusing textured quad VAO layout)
        if self.vao_manager.text_vao.is_none() {
            // Text uses same layout as textured quads
            self.vao_manager
                .setup_textured_vao(gl, &self.text_instances);
            self.vao_manager.text_vao = self.vao_manager.textured_quad_vao.take();
        }

        // Use program (state cache avoids redundant bind)
        let program_changed = self.state_cache.use_program(gl, &program.program);
        if program_changed {
            self.frame_stats.program_switches += 1;
        } else {
            self.frame_stats.skipped_program_binds += 1;
        }

        // Bind VAO (state cache avoids redundant bind)
        let vao_changed = self
            .state_cache
            .bind_vao(gl, self.vao_manager.text_vao.as_ref());
        if vao_changed {
            self.frame_stats.vao_switches += 1;
        } else {
            self.frame_stats.skipped_vao_binds += 1;
        }

        // Set uniforms only if program changed (legacy mode only)
        if program_changed {
            if let Some(loc) = &program.resolution_loc {
                let (w, h) = self.state_cache.resolution();
                gl.uniform2f(Some(loc), w, h);
                self.frame_stats.uniform_calls += 1;
            }

            if let Some(loc) = &program.texture_loc {
                gl.uniform1i(Some(loc), 0);
            }
        }

        // Bind font atlas
        self.font_atlas.bind(gl, 0);
        self.frame_stats.texture_binds += 1;

        let instance_count = self.text_instances.instance_count();
        gl.draw_arrays_instanced(
            WebGl2RenderingContext::TRIANGLE_STRIP,
            0,
            4,
            instance_count as i32,
        );

        // Track statistics
        self.frame_stats.draw_calls += 1;
        self.frame_stats.text_instances += instance_count as u32;
        self.frame_stats.total_instances += instance_count as u32;
        self.frame_stats
            .active_primitives
            .set(ActivePrimitives::TEXT);

        self.text_instances.clear();
    }
}
