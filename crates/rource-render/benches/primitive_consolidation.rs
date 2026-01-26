// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Primitive consolidation benchmarks for Phase 63 circle + ring unification.
//!
//! These benchmarks measure the CPU-side overhead difference between:
//! - **Separate pipelines**: Circle and Ring use separate instance buffers and draw calls
//! - **Unified disc pipeline**: Single instance buffer with `inner_radius` field
//!
//! ## Benchmark Categories
//!
//! - **Instance population**: Adding instances to buffers
//! - **Flush simulation**: Simulating GPU state changes and draw calls
//! - **Pipeline switch overhead**: Cost of changing render pipelines
//!
//! ## Usage
//!
//! ```bash
//! cargo bench --bench primitive_consolidation -p rource-render
//! ```

#![allow(missing_docs)]

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::hint::black_box;

// ============================================================================
// Instance Data Structures
// ============================================================================

/// Circle instance data for separate pipeline approach.
/// Layout: center(2) + radius(1) + color(4) = 7 floats = 28 bytes.
#[derive(Clone, Copy)]
#[repr(C)]
struct CircleInstance {
    center: [f32; 2],
    radius: f32,
    color: [f32; 4],
}

/// Ring instance data for separate pipeline approach.
/// Layout: center(2) + radius(1) + width(1) + color(4) = 8 floats = 32 bytes.
#[derive(Clone, Copy)]
#[repr(C)]
struct RingInstance {
    center: [f32; 2],
    radius: f32,
    width: f32,
    color: [f32; 4],
}

/// Unified disc instance data for consolidated pipeline approach.
/// Layout: `center(2)` + `outer_radius(1)` + `inner_radius(1)` + `color(4)` = 8 floats = 32 bytes.
/// When `inner_radius` = 0, renders as solid disc. When `inner_radius` > 0, renders as ring.
#[derive(Clone, Copy)]
#[repr(C)]
struct DiscInstance {
    center: [f32; 2],
    outer_radius: f32,
    inner_radius: f32, // 0 = solid disc, >0 = ring
    color: [f32; 4],
}

// ============================================================================
// Separate Pipeline Buffers
// ============================================================================

/// Simulates current separate pipeline approach with two instance buffers.
struct SeparatePipelineBuffers {
    circles: Vec<CircleInstance>,
    rings: Vec<RingInstance>,
}

impl SeparatePipelineBuffers {
    fn new(capacity: usize) -> Self {
        Self {
            circles: Vec::with_capacity(capacity),
            rings: Vec::with_capacity(capacity),
        }
    }

    #[inline]
    fn add_circle(&mut self, center: [f32; 2], radius: f32, color: [f32; 4]) {
        self.circles.push(CircleInstance {
            center,
            radius,
            color,
        });
    }

    #[inline]
    fn add_ring(&mut self, center: [f32; 2], radius: f32, width: f32, color: [f32; 4]) {
        self.rings.push(RingInstance {
            center,
            radius,
            width,
            color,
        });
    }

    fn clear(&mut self) {
        self.circles.clear();
        self.rings.clear();
    }

    /// Returns number of draw calls needed (0-2).
    fn draw_call_count(&self) -> usize {
        usize::from(!self.circles.is_empty()) + usize::from(!self.rings.is_empty())
    }

    /// Returns number of pipeline switches needed (0-1).
    fn pipeline_switch_count(&self) -> usize {
        // Need to switch from Circle pipeline to Ring pipeline when both present
        usize::from(!self.circles.is_empty() && !self.rings.is_empty())
    }

    /// Simulates flush operation with pipeline switches and draw calls.
    fn simulate_flush(&self) -> usize {
        let mut total_instances = 0;

        // Flush circles (Pipeline 1)
        if !self.circles.is_empty() {
            // Simulate pipeline bind
            black_box(1u32); // Pipeline ID: Circle

            // Simulate buffer upload
            for instance in &self.circles {
                black_box(instance);
                total_instances += 1;
            }

            // Simulate draw call
            black_box(self.circles.len());
        }

        // Flush rings (Pipeline 2) - requires pipeline switch
        if !self.rings.is_empty() {
            // Simulate pipeline switch (expensive GPU state change)
            black_box(2u32); // Pipeline ID: Ring

            // Simulate buffer upload
            for instance in &self.rings {
                black_box(instance);
                total_instances += 1;
            }

            // Simulate draw call
            black_box(self.rings.len());
        }

        total_instances
    }
}

// ============================================================================
// Unified Disc Pipeline Buffer
// ============================================================================

/// Simulates consolidated disc pipeline with single instance buffer.
struct UnifiedDiscBuffer {
    instances: Vec<DiscInstance>,
}

impl UnifiedDiscBuffer {
    fn new(capacity: usize) -> Self {
        Self {
            instances: Vec::with_capacity(capacity),
        }
    }

    #[inline]
    fn add_solid_disc(&mut self, center: [f32; 2], radius: f32, color: [f32; 4]) {
        self.instances.push(DiscInstance {
            center,
            outer_radius: radius,
            inner_radius: 0.0, // Solid disc
            color,
        });
    }

    #[inline]
    fn add_ring(&mut self, center: [f32; 2], radius: f32, width: f32, color: [f32; 4]) {
        self.instances.push(DiscInstance {
            center,
            outer_radius: radius + width * 0.5,
            inner_radius: radius - width * 0.5,
            color,
        });
    }

    fn clear(&mut self) {
        self.instances.clear();
    }

    /// Returns number of draw calls needed (always 0 or 1).
    fn draw_call_count(&self) -> usize {
        usize::from(!self.instances.is_empty())
    }

    /// Returns number of pipeline switches needed (always 0).
    #[allow(clippy::unused_self)]
    fn pipeline_switch_count(&self) -> usize {
        // Single pipeline, no switching needed
        0
    }

    /// Simulates flush operation with single draw call.
    fn simulate_flush(&self) -> usize {
        if self.instances.is_empty() {
            return 0;
        }

        // Simulate single pipeline bind
        black_box(3u32); // Pipeline ID: Disc (unified)

        // Simulate buffer upload (single contiguous buffer)
        for instance in &self.instances {
            black_box(instance);
        }

        // Simulate single draw call
        black_box(self.instances.len());

        self.instances.len()
    }
}

// ============================================================================
// Test Data Generation
// ============================================================================

/// Generates test data for file nodes.
/// Each file has a disc (body) and optionally a ring (glow when modified).
fn generate_file_primitives(
    file_count: usize,
    glow_ratio: f32,
) -> Vec<(bool, [f32; 2], f32, [f32; 4])> {
    let glow_count = (file_count as f32 * glow_ratio) as usize;

    let mut primitives = Vec::with_capacity(file_count + glow_count);

    // File body discs
    for i in 0..file_count {
        let x = (i % 100) as f32 * 10.0;
        let y = (i / 100) as f32 * 10.0;
        primitives.push((
            true, // is_disc
            [x, y],
            4.0, // radius
            [1.0, 1.0, 1.0, 1.0],
        ));
    }

    // File glow rings (for recently modified files)
    for i in 0..glow_count {
        let x = (i % 100) as f32 * 10.0;
        let y = (i / 100) as f32 * 10.0;
        primitives.push((
            false, // is_ring
            [x, y],
            6.0, // radius (larger than body)
            [1.0, 0.8, 0.2, 0.5],
        ));
    }

    primitives
}

/// Generates test data for user nodes.
/// Each user has multiple concentric discs and rings for glow effects.
fn generate_user_primitives(user_count: usize) -> Vec<(bool, [f32; 2], f32, [f32; 4])> {
    let mut primitives = Vec::with_capacity(user_count * 4);

    for i in 0..user_count {
        let x = (i % 50) as f32 * 40.0;
        let y = (i / 50) as f32 * 40.0;

        // User body disc
        primitives.push((true, [x, y], 16.0, [1.0, 1.0, 1.0, 1.0]));

        // Glow rings (multiple layers)
        primitives.push((false, [x, y], 20.0, [0.5, 0.8, 1.0, 0.3]));
        primitives.push((false, [x, y], 24.0, [0.5, 0.8, 1.0, 0.2]));
        primitives.push((false, [x, y], 28.0, [0.5, 0.8, 1.0, 0.1]));
    }

    primitives
}

// ============================================================================
// Instance Population Benchmarks
// ============================================================================

fn benchmark_instance_population(c: &mut Criterion) {
    let mut group = c.benchmark_group("primitive_consolidation/instance_population");

    // Test various entity counts with realistic workloads
    for entity_count in [100, 300, 500, 1000] {
        // Realistic scenario: 80% discs, 20% rings (files + users with glows)
        let file_data = generate_file_primitives(entity_count, 0.2);

        group.throughput(Throughput::Elements(file_data.len() as u64));

        // Separate pipelines (baseline)
        group.bench_with_input(
            BenchmarkId::new("separate_pipelines", entity_count),
            &file_data,
            |b, data| {
                let mut buffers = SeparatePipelineBuffers::new(entity_count * 2);
                b.iter(|| {
                    buffers.clear();
                    for (is_disc, center, radius, color) in data {
                        if *is_disc {
                            buffers.add_circle(
                                black_box(*center),
                                black_box(*radius),
                                black_box(*color),
                            );
                        } else {
                            buffers.add_ring(
                                black_box(*center),
                                black_box(*radius),
                                2.0,
                                black_box(*color),
                            );
                        }
                    }
                    black_box(buffers.draw_call_count())
                });
            },
        );

        // Unified disc pipeline (optimized)
        group.bench_with_input(
            BenchmarkId::new("unified_disc", entity_count),
            &file_data,
            |b, data| {
                let mut buffer = UnifiedDiscBuffer::new(entity_count * 2);
                b.iter(|| {
                    buffer.clear();
                    for (is_disc, center, radius, color) in data {
                        if *is_disc {
                            buffer.add_solid_disc(
                                black_box(*center),
                                black_box(*radius),
                                black_box(*color),
                            );
                        } else {
                            buffer.add_ring(
                                black_box(*center),
                                black_box(*radius),
                                2.0,
                                black_box(*color),
                            );
                        }
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
    let mut group = c.benchmark_group("primitive_consolidation/flush_overhead");

    for entity_count in [100, 300, 500, 1000] {
        let file_data = generate_file_primitives(entity_count, 0.2);

        group.throughput(Throughput::Elements(file_data.len() as u64));

        // Separate pipelines: populate then flush
        group.bench_with_input(
            BenchmarkId::new("separate_pipelines", entity_count),
            &file_data,
            |b, data| {
                let mut buffers = SeparatePipelineBuffers::new(entity_count * 2);
                for (is_disc, center, radius, color) in data {
                    if *is_disc {
                        buffers.add_circle(*center, *radius, *color);
                    } else {
                        buffers.add_ring(*center, *radius, 2.0, *color);
                    }
                }
                b.iter(|| black_box(buffers.simulate_flush()));
            },
        );

        // Unified disc pipeline: populate then flush
        group.bench_with_input(
            BenchmarkId::new("unified_disc", entity_count),
            &file_data,
            |b, data| {
                let mut buffer = UnifiedDiscBuffer::new(entity_count * 2);
                for (is_disc, center, radius, color) in data {
                    if *is_disc {
                        buffer.add_solid_disc(*center, *radius, *color);
                    } else {
                        buffer.add_ring(*center, *radius, 2.0, *color);
                    }
                }
                b.iter(|| black_box(buffer.simulate_flush()));
            },
        );
    }

    group.finish();
}

// ============================================================================
// Draw Call & Pipeline Switch Verification
// ============================================================================

fn benchmark_draw_call_reduction(c: &mut Criterion) {
    let mut group = c.benchmark_group("primitive_consolidation/draw_call_reduction");

    for entity_count in [100, 300, 500, 1000] {
        let file_data = generate_file_primitives(entity_count, 0.2);

        // Separate pipelines
        let mut separate = SeparatePipelineBuffers::new(entity_count * 2);
        for (is_disc, center, radius, color) in &file_data {
            if *is_disc {
                separate.add_circle(*center, *radius, *color);
            } else {
                separate.add_ring(*center, *radius, 2.0, *color);
            }
        }
        let separate_draws = separate.draw_call_count();
        let separate_switches = separate.pipeline_switch_count();

        // Unified disc pipeline
        let mut unified = UnifiedDiscBuffer::new(entity_count * 2);
        for (is_disc, center, radius, color) in &file_data {
            if *is_disc {
                unified.add_solid_disc(*center, *radius, *color);
            } else {
                unified.add_ring(*center, *radius, 2.0, *color);
            }
        }
        let unified_draws = unified.draw_call_count();
        let unified_switches = unified.pipeline_switch_count();

        // Verify counts
        group.bench_function(BenchmarkId::new("verify_separate", entity_count), |b| {
            b.iter(|| {
                black_box(separate_draws);
                black_box(separate_switches);
            });
        });
        group.bench_function(BenchmarkId::new("verify_unified", entity_count), |b| {
            b.iter(|| {
                black_box(unified_draws);
                black_box(unified_switches);
            });
        });

        // Calculate reduction
        let draw_reduction = if separate_draws > 0 {
            100.0 * (1.0 - unified_draws as f64 / separate_draws as f64)
        } else {
            0.0
        };
        eprintln!(
            "Entity count {entity_count}: separate=({separate_draws} draws, {separate_switches} switches), unified=({unified_draws} draws, {unified_switches} switches) → {draw_reduction:.0}% draw reduction"
        );
    }

    group.finish();
}

// ============================================================================
// Full Frame Simulation
// ============================================================================

fn benchmark_full_frame(c: &mut Criterion) {
    let mut group = c.benchmark_group("primitive_consolidation/full_frame");

    // Realistic frame: files + users with various glow ratios
    for entity_count in [100, 300, 500, 1000] {
        let file_data = generate_file_primitives(entity_count, 0.3);
        let user_data = generate_user_primitives(entity_count / 10);

        let total_primitives = file_data.len() + user_data.len();
        group.throughput(Throughput::Elements(total_primitives as u64));

        // Separate pipelines: full frame cycle
        group.bench_with_input(
            BenchmarkId::new("separate_pipelines", entity_count),
            &(&file_data, &user_data),
            |b, (files, users)| {
                let mut buffers = SeparatePipelineBuffers::new(total_primitives);
                b.iter(|| {
                    // Clear from previous frame
                    buffers.clear();

                    // Populate files
                    for (is_disc, center, radius, color) in *files {
                        if *is_disc {
                            buffers.add_circle(
                                black_box(*center),
                                black_box(*radius),
                                black_box(*color),
                            );
                        } else {
                            buffers.add_ring(
                                black_box(*center),
                                black_box(*radius),
                                2.0,
                                black_box(*color),
                            );
                        }
                    }

                    // Populate users
                    for (is_disc, center, radius, color) in *users {
                        if *is_disc {
                            buffers.add_circle(
                                black_box(*center),
                                black_box(*radius),
                                black_box(*color),
                            );
                        } else {
                            buffers.add_ring(
                                black_box(*center),
                                black_box(*radius),
                                2.0,
                                black_box(*color),
                            );
                        }
                    }

                    // Flush
                    black_box(buffers.simulate_flush())
                });
            },
        );

        // Unified disc pipeline: full frame cycle
        group.bench_with_input(
            BenchmarkId::new("unified_disc", entity_count),
            &(&file_data, &user_data),
            |b, (files, users)| {
                let mut buffer = UnifiedDiscBuffer::new(total_primitives);
                b.iter(|| {
                    // Clear from previous frame
                    buffer.clear();

                    // Populate files
                    for (is_disc, center, radius, color) in *files {
                        if *is_disc {
                            buffer.add_solid_disc(
                                black_box(*center),
                                black_box(*radius),
                                black_box(*color),
                            );
                        } else {
                            buffer.add_ring(
                                black_box(*center),
                                black_box(*radius),
                                2.0,
                                black_box(*color),
                            );
                        }
                    }

                    // Populate users
                    for (is_disc, center, radius, color) in *users {
                        if *is_disc {
                            buffer.add_solid_disc(
                                black_box(*center),
                                black_box(*radius),
                                black_box(*color),
                            );
                        } else {
                            buffer.add_ring(
                                black_box(*center),
                                black_box(*radius),
                                2.0,
                                black_box(*color),
                            );
                        }
                    }

                    // Flush
                    black_box(buffer.simulate_flush())
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Memory Overhead Analysis
// ============================================================================

fn benchmark_memory_overhead(c: &mut Criterion) {
    let mut group = c.benchmark_group("primitive_consolidation/memory_overhead");

    // Compare memory footprint per instance
    for entity_count in [100, 500, 1000, 5000] {
        let circle_size = std::mem::size_of::<CircleInstance>(); // 28 bytes
        let ring_size = std::mem::size_of::<RingInstance>(); // 32 bytes
        let disc_size = std::mem::size_of::<DiscInstance>(); // 32 bytes

        // Scenario: 80% circles, 20% rings
        let circle_count = (entity_count as f32 * 0.8) as usize;
        let ring_count = entity_count - circle_count;

        let separate_bytes = circle_count * circle_size + ring_count * ring_size;
        let unified_bytes = entity_count * disc_size;
        // Safe cast: entity counts are small, values won't wrap
        #[allow(clippy::cast_possible_wrap)]
        let overhead_bytes = unified_bytes as i64 - separate_bytes as i64;
        let overhead_pct = 100.0 * overhead_bytes as f64 / separate_bytes as f64;

        group.bench_function(BenchmarkId::new("separate_bytes", entity_count), |b| {
            b.iter(|| black_box(separate_bytes));
        });
        group.bench_function(BenchmarkId::new("unified_bytes", entity_count), |b| {
            b.iter(|| black_box(unified_bytes));
        });

        eprintln!(
            "Entity count {entity_count}: separate={separate_bytes} bytes, unified={unified_bytes} bytes ({overhead_bytes:+} bytes, {overhead_pct:+.1}% overhead)"
        );
    }

    group.finish();
}

// ============================================================================
// Mathematical Analysis
// ============================================================================

fn benchmark_mathematical_analysis(c: &mut Criterion) {
    let mut group = c.benchmark_group("primitive_consolidation/mathematical_analysis");

    // Verify the key mathematical claims:
    // 1. Separate pipelines: 2 draw calls when both circles and rings present
    // 2. Unified pipeline: 1 draw call always
    // 3. Pipeline switches: 1 for separate, 0 for unified

    for n in [50, 100, 250, 500, 1000] {
        let data = generate_file_primitives(n, 0.2);

        // Measure separate approach
        group.bench_with_input(
            BenchmarkId::new("separate_draw_calls", n),
            &data,
            |b, data| {
                let mut buffers = SeparatePipelineBuffers::new(n * 2);
                for (is_disc, center, radius, color) in data {
                    if *is_disc {
                        buffers.add_circle(*center, *radius, *color);
                    } else {
                        buffers.add_ring(*center, *radius, 2.0, *color);
                    }
                }
                b.iter(|| {
                    let draws = buffers.draw_call_count();
                    let switches = buffers.pipeline_switch_count();
                    // Verify: should be 2 draws and 1 switch when both present
                    assert_eq!(draws, 2);
                    assert_eq!(switches, 1);
                    black_box((draws, switches))
                });
            },
        );

        // Measure unified approach
        group.bench_with_input(
            BenchmarkId::new("unified_draw_calls", n),
            &data,
            |b, data| {
                let mut buffer = UnifiedDiscBuffer::new(n * 2);
                for (is_disc, center, radius, color) in data {
                    if *is_disc {
                        buffer.add_solid_disc(*center, *radius, *color);
                    } else {
                        buffer.add_ring(*center, *radius, 2.0, *color);
                    }
                }
                b.iter(|| {
                    let draws = buffer.draw_call_count();
                    let switches = buffer.pipeline_switch_count();
                    // Verify: should be 1 draw and 0 switches
                    assert_eq!(draws, 1);
                    assert_eq!(switches, 0);
                    black_box((draws, switches))
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
    benchmark_memory_overhead,
    benchmark_mathematical_analysis,
);

criterion_main!(benches);
