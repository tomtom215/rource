// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Texture batching benchmarks for Phase 61 avatar texture array optimization.
//!
//! These benchmarks measure the CPU-side overhead difference between:
//! - **Per-texture path**: HashMap<TextureId, InstanceBuffer> with separate draw calls
//! - **Texture array path**: Single InstanceBuffer with layer indices
//!
//! ## Benchmark Categories
//!
//! - **Instance population**: Adding instances to buffers
//! - **Flush preparation**: Preparing data for GPU submission
//! - **Draw dispatch simulation**: Simulating draw call overhead
//!
//! ## Usage
//!
//! ```bash
//! cargo bench --bench texture_batching -p rource-render
//! ```

#![allow(missing_docs)]

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rustc_hash::FxHashMap as HashMap;
use std::collections::hash_map::Entry;

/// Simulated texture ID (matches TextureId in rource-render).
type TextureId = u32;

/// Instance data for per-texture path (simplified).
/// In production: bounds[4] + uv_bounds[4] + color[4] = 12 floats.
#[derive(Clone, Copy)]
#[repr(C)]
struct PerTextureInstance {
    bounds: [f32; 4],
    uv_bounds: [f32; 4],
    color: [f32; 4],
}

/// Instance data for texture array path.
/// In production: bounds[4] + uv_bounds[4] + color[4] + layer[1] = 13 floats.
#[derive(Clone, Copy)]
#[repr(C)]
struct TextureArrayInstance {
    bounds: [f32; 4],
    uv_bounds: [f32; 4],
    color: [f32; 4],
    layer: u32,
}

/// Simulates per-texture instance buffer management.
/// Each texture gets its own Vec (simulating separate GPU buffers).
struct PerTextureBuffers {
    buffers: HashMap<TextureId, Vec<PerTextureInstance>>,
}

impl PerTextureBuffers {
    fn new() -> Self {
        Self {
            buffers: HashMap::default(),
        }
    }

    #[inline]
    fn add_instance(&mut self, texture_id: TextureId, instance: PerTextureInstance) {
        match self.buffers.entry(texture_id) {
            Entry::Occupied(mut e) => {
                e.get_mut().push(instance);
            }
            Entry::Vacant(e) => {
                let mut vec = Vec::with_capacity(16);
                vec.push(instance);
                e.insert(vec);
            }
        }
    }

    fn clear(&mut self) {
        for buffer in self.buffers.values_mut() {
            buffer.clear();
        }
    }

    /// Returns number of draw calls needed (one per texture).
    fn draw_call_count(&self) -> usize {
        self.buffers.iter().filter(|(_, v)| !v.is_empty()).count()
    }

    /// Simulates iterating all buffers for draw dispatch.
    fn simulate_flush(&self) -> usize {
        let mut total_instances = 0;
        for (texture_id, instances) in &self.buffers {
            if instances.is_empty() {
                continue;
            }
            // Simulate bind group switch (in production: set_bind_group)
            black_box(*texture_id);

            // Simulate buffer upload (in production: queue.write_buffer)
            for instance in instances {
                black_box(instance);
                total_instances += 1;
            }

            // Simulate draw call (in production: render_pass.draw)
            black_box(instances.len());
        }
        total_instances
    }
}

/// Simulates texture array instance buffer management.
/// Single buffer for all textures with layer indices.
struct TextureArrayBuffer {
    instances: Vec<TextureArrayInstance>,
    texture_to_layer: HashMap<TextureId, u32>,
    next_layer: u32,
}

impl TextureArrayBuffer {
    fn new() -> Self {
        Self {
            instances: Vec::with_capacity(1024),
            texture_to_layer: HashMap::default(),
            next_layer: 0,
        }
    }

    /// Registers a texture and returns its layer index.
    fn register_texture(&mut self, texture_id: TextureId) -> u32 {
        *self.texture_to_layer.entry(texture_id).or_insert_with(|| {
            let layer = self.next_layer;
            self.next_layer += 1;
            layer
        })
    }

    #[inline]
    fn add_instance(&mut self, texture_id: TextureId, base: PerTextureInstance) {
        let layer = self.texture_to_layer.get(&texture_id).copied().unwrap_or(0);
        self.instances.push(TextureArrayInstance {
            bounds: base.bounds,
            uv_bounds: base.uv_bounds,
            color: base.color,
            layer,
        });
    }

    fn clear(&mut self) {
        self.instances.clear();
    }

    /// Returns number of draw calls needed (always 1 if non-empty).
    fn draw_call_count(&self) -> usize {
        if self.instances.is_empty() {
            0
        } else {
            1
        }
    }

    /// Simulates single buffer flush for draw dispatch.
    fn simulate_flush(&self) -> usize {
        if self.instances.is_empty() {
            return 0;
        }

        // Simulate single bind group switch
        black_box(0u32);

        // Simulate single buffer upload
        for instance in &self.instances {
            black_box(instance);
        }

        // Simulate single draw call
        black_box(self.instances.len());

        self.instances.len()
    }
}

// ============================================================================
// Benchmark Data Generation
// ============================================================================

/// Generates test data simulating visible avatars.
fn generate_avatar_instances(
    avatar_count: usize,
    unique_textures: usize,
) -> Vec<(TextureId, PerTextureInstance)> {
    (0..avatar_count)
        .map(|i| {
            let texture_id = (i % unique_textures) as u32;
            let instance = PerTextureInstance {
                bounds: [i as f32, i as f32, 32.0, 32.0],
                uv_bounds: [0.0, 0.0, 1.0, 1.0],
                color: [1.0, 1.0, 1.0, 1.0],
            };
            (texture_id, instance)
        })
        .collect()
}

// ============================================================================
// Instance Population Benchmarks
// ============================================================================

fn benchmark_instance_population(c: &mut Criterion) {
    let mut group = c.benchmark_group("texture_batching/instance_population");

    // Test various avatar counts with realistic texture distribution
    // Scenario: Each user has unique avatar texture
    for avatar_count in [50, 100, 200, 300, 500] {
        let unique_textures = avatar_count; // Worst case: all unique
        let data = generate_avatar_instances(avatar_count, unique_textures);

        group.throughput(Throughput::Elements(avatar_count as u64));

        // Per-texture path (baseline)
        group.bench_with_input(
            BenchmarkId::new("per_texture", avatar_count),
            &data,
            |b, data| {
                let mut buffers = PerTextureBuffers::new();
                b.iter(|| {
                    buffers.clear();
                    for (texture_id, instance) in data {
                        buffers.add_instance(black_box(*texture_id), black_box(*instance));
                    }
                    black_box(buffers.draw_call_count())
                });
            },
        );

        // Texture array path (optimized)
        group.bench_with_input(
            BenchmarkId::new("texture_array", avatar_count),
            &data,
            |b, data| {
                let mut buffer = TextureArrayBuffer::new();
                // Pre-register textures (done once at load time)
                for i in 0..unique_textures {
                    buffer.register_texture(i as u32);
                }
                b.iter(|| {
                    buffer.clear();
                    for (texture_id, instance) in data {
                        buffer.add_instance(black_box(*texture_id), black_box(*instance));
                    }
                    black_box(buffer.draw_call_count())
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Flush/Draw Dispatch Benchmarks
// ============================================================================

fn benchmark_flush_overhead(c: &mut Criterion) {
    let mut group = c.benchmark_group("texture_batching/flush_overhead");

    for avatar_count in [50, 100, 200, 300, 500] {
        let unique_textures = avatar_count;
        let data = generate_avatar_instances(avatar_count, unique_textures);

        group.throughput(Throughput::Elements(avatar_count as u64));

        // Per-texture path: populate then flush
        group.bench_with_input(
            BenchmarkId::new("per_texture", avatar_count),
            &data,
            |b, data| {
                let mut buffers = PerTextureBuffers::new();
                for (texture_id, instance) in data {
                    buffers.add_instance(*texture_id, *instance);
                }
                b.iter(|| black_box(buffers.simulate_flush()));
            },
        );

        // Texture array path: populate then flush
        group.bench_with_input(
            BenchmarkId::new("texture_array", avatar_count),
            &data,
            |b, data| {
                let mut buffer = TextureArrayBuffer::new();
                for i in 0..unique_textures {
                    buffer.register_texture(i as u32);
                }
                for (texture_id, instance) in data {
                    buffer.add_instance(*texture_id, *instance);
                }
                b.iter(|| black_box(buffer.simulate_flush()));
            },
        );
    }

    group.finish();
}

// ============================================================================
// Draw Call Count Verification
// ============================================================================

fn benchmark_draw_call_reduction(c: &mut Criterion) {
    let mut group = c.benchmark_group("texture_batching/draw_call_reduction");

    for avatar_count in [50, 100, 200, 300, 500] {
        let unique_textures = avatar_count;
        let data = generate_avatar_instances(avatar_count, unique_textures);

        // Per-texture path
        let mut per_texture = PerTextureBuffers::new();
        for (texture_id, instance) in &data {
            per_texture.add_instance(*texture_id, *instance);
        }
        let per_texture_draws = per_texture.draw_call_count();

        // Texture array path
        let mut array_buffer = TextureArrayBuffer::new();
        for i in 0..unique_textures {
            array_buffer.register_texture(i as u32);
        }
        for (texture_id, instance) in &data {
            array_buffer.add_instance(*texture_id, *instance);
        }
        let array_draws = array_buffer.draw_call_count();

        // Report draw call counts
        group.bench_function(BenchmarkId::new("verify_per_texture", avatar_count), |b| {
            b.iter(|| black_box(per_texture_draws))
        });
        group.bench_function(
            BenchmarkId::new("verify_texture_array", avatar_count),
            |b| b.iter(|| black_box(array_draws)),
        );

        // Calculate reduction percentage
        let reduction = if per_texture_draws > 0 {
            100.0 * (1.0 - array_draws as f64 / per_texture_draws as f64)
        } else {
            0.0
        };
        eprintln!(
            "Avatar count {}: per_texture={} draws, texture_array={} draws ({:.1}% reduction)",
            avatar_count, per_texture_draws, array_draws, reduction
        );
    }

    group.finish();
}

// ============================================================================
// Combined Full-Frame Simulation
// ============================================================================

fn benchmark_full_frame(c: &mut Criterion) {
    let mut group = c.benchmark_group("texture_batching/full_frame");

    // Simulate realistic frame with mixed content
    // 300 avatars is typical for medium-sized visualization
    for avatar_count in [100, 300, 500] {
        let unique_textures = avatar_count;
        let data = generate_avatar_instances(avatar_count, unique_textures);

        group.throughput(Throughput::Elements(avatar_count as u64));

        // Per-texture path: full frame cycle
        group.bench_with_input(
            BenchmarkId::new("per_texture", avatar_count),
            &data,
            |b, data| {
                let mut buffers = PerTextureBuffers::new();
                b.iter(|| {
                    // Clear from previous frame
                    buffers.clear();

                    // Populate (during render traversal)
                    for (texture_id, instance) in data {
                        buffers.add_instance(black_box(*texture_id), black_box(*instance));
                    }

                    // Flush (GPU submission)
                    black_box(buffers.simulate_flush())
                });
            },
        );

        // Texture array path: full frame cycle
        group.bench_with_input(
            BenchmarkId::new("texture_array", avatar_count),
            &data,
            |b, data| {
                let mut buffer = TextureArrayBuffer::new();
                for i in 0..unique_textures {
                    buffer.register_texture(i as u32);
                }
                b.iter(|| {
                    // Clear from previous frame
                    buffer.clear();

                    // Populate (during render traversal)
                    for (texture_id, instance) in data {
                        buffer.add_instance(black_box(*texture_id), black_box(*instance));
                    }

                    // Flush (GPU submission)
                    black_box(buffer.simulate_flush())
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Mathematical Analysis
// ============================================================================

/// Benchmark to verify mathematical claims about draw call reduction.
fn benchmark_mathematical_analysis(c: &mut Criterion) {
    let mut group = c.benchmark_group("texture_batching/mathematical_analysis");

    // The key mathematical claim:
    // Per-texture: O(n) draw calls where n = unique textures
    // Texture array: O(1) draw calls

    // Test scaling behavior
    for n in [10, 50, 100, 250, 500] {
        let data = generate_avatar_instances(n, n);

        // Measure per-texture path scaling
        group.bench_with_input(BenchmarkId::new("per_texture_O_n", n), &data, |b, data| {
            let mut buffers = PerTextureBuffers::new();
            for (texture_id, instance) in data {
                buffers.add_instance(*texture_id, *instance);
            }
            b.iter(|| {
                let count = buffers.draw_call_count();
                // Verify O(n): draw_call_count == n
                assert_eq!(count, n);
                black_box(count)
            });
        });

        // Measure texture array path (constant)
        group.bench_with_input(
            BenchmarkId::new("texture_array_O_1", n),
            &data,
            |b, data| {
                let mut buffer = TextureArrayBuffer::new();
                for i in 0..n {
                    buffer.register_texture(i as u32);
                }
                for (texture_id, instance) in data {
                    buffer.add_instance(*texture_id, *instance);
                }
                b.iter(|| {
                    let count = buffer.draw_call_count();
                    // Verify O(1): draw_call_count == 1
                    assert_eq!(count, 1);
                    black_box(count)
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    benchmark_instance_population,
    benchmark_flush_overhead,
    benchmark_draw_call_reduction,
    benchmark_full_frame,
    benchmark_mathematical_analysis,
);

criterion_main!(benches);
