// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Scale benchmarks for rendering primitives.
//!
//! These benchmarks measure the rendering performance at large entity counts
//! (1k, 5k, 10k, 20k) to verify that optimizations hold under realistic load.
//!
//! ## Benchmark Categories
//!
//! - **Disc rendering**: Filled circles for files and directories
//! - **Circle rendering**: Outlined circles for borders and highlights
//! - **Line rendering**: Straight lines for simple branches
//! - **Spline rendering**: Curved lines for styled branches
//! - **Mixed workload**: Realistic mix of all primitives
//!
//! ## Usage
//!
//! ```bash
//! cargo bench --bench render_scale -p rource-render
//! ```

#![allow(missing_docs)]

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rource_math::{Color, Vec2};
use rource_render::{Renderer, SoftwareRenderer};

/// Screen dimensions for benchmarks.
const BENCH_WIDTH: u32 = 1920;
const BENCH_HEIGHT: u32 = 1080;

/// Creates a set of random-ish positions distributed across the screen.
fn generate_positions(count: usize) -> Vec<Vec2> {
    // Use deterministic "random" positions based on index
    // This ensures reproducible benchmarks
    (0..count)
        .map(|i| {
            let x = ((i * 7919) % BENCH_WIDTH as usize) as f32;
            let y = ((i * 6271) % BENCH_HEIGHT as usize) as f32;
            Vec2::new(x, y)
        })
        .collect()
}

/// Creates colors for entities based on index.
fn generate_colors(count: usize) -> Vec<Color> {
    (0..count)
        .map(|i| {
            let r = ((i * 37) % 256) as f32 / 255.0;
            let g = ((i * 53) % 256) as f32 / 255.0;
            let b = ((i * 79) % 256) as f32 / 255.0;
            Color::new(r, g, b, 0.8)
        })
        .collect()
}

// ============================================================================
// Disc Rendering Benchmarks (Files, Directories)
// ============================================================================

/// Benchmarks rendering filled discs at various scales.
///
/// This simulates rendering files and directory centers.
fn benchmark_disc_rendering(c: &mut Criterion) {
    let mut group = c.benchmark_group("disc_rendering");

    for entity_count in [1000, 5000, 10000, 20000] {
        group.throughput(Throughput::Elements(entity_count as u64));

        let positions = generate_positions(entity_count);
        let colors = generate_colors(entity_count);
        let radii: Vec<f32> = (0..entity_count).map(|i| 2.0 + (i % 10) as f32).collect();

        group.bench_with_input(
            BenchmarkId::new("count", entity_count),
            &(positions, colors, radii),
            |b, (positions, colors, radii)| {
                let mut renderer = SoftwareRenderer::new(BENCH_WIDTH, BENCH_HEIGHT);

                b.iter(|| {
                    renderer.begin_frame();
                    renderer.clear(Color::BLACK);

                    for i in 0..positions.len() {
                        renderer.draw_disc(
                            black_box(positions[i]),
                            black_box(radii[i]),
                            black_box(colors[i]),
                        );
                    }

                    renderer.end_frame();
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Circle Rendering Benchmarks (Borders, Highlights)
// ============================================================================

/// Benchmarks rendering outlined circles at various scales.
///
/// This simulates rendering entity borders and highlight rings.
fn benchmark_circle_rendering(c: &mut Criterion) {
    let mut group = c.benchmark_group("circle_rendering");

    for entity_count in [1000, 5000, 10000, 20000] {
        group.throughput(Throughput::Elements(entity_count as u64));

        let positions = generate_positions(entity_count);
        let colors = generate_colors(entity_count);
        let radii: Vec<f32> = (0..entity_count).map(|i| 5.0 + (i % 15) as f32).collect();

        group.bench_with_input(
            BenchmarkId::new("count", entity_count),
            &(positions, colors, radii),
            |b, (positions, colors, radii)| {
                let mut renderer = SoftwareRenderer::new(BENCH_WIDTH, BENCH_HEIGHT);

                b.iter(|| {
                    renderer.begin_frame();
                    renderer.clear(Color::BLACK);

                    for i in 0..positions.len() {
                        renderer.draw_circle(
                            black_box(positions[i]),
                            black_box(radii[i]),
                            black_box(1.5), // line width
                            black_box(colors[i]),
                        );
                    }

                    renderer.end_frame();
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Line Rendering Benchmarks (Simple Branches)
// ============================================================================

/// Benchmarks rendering straight lines at various scales.
///
/// This simulates rendering branch connections without curves.
fn benchmark_line_rendering(c: &mut Criterion) {
    let mut group = c.benchmark_group("line_rendering");

    for entity_count in [1000, 5000, 10000, 20000] {
        group.throughput(Throughput::Elements(entity_count as u64));

        let starts = generate_positions(entity_count);
        let ends: Vec<Vec2> = starts
            .iter()
            .map(|p| Vec2::new(p.x + 50.0, p.y + 30.0))
            .collect();
        let colors = generate_colors(entity_count);

        group.bench_with_input(
            BenchmarkId::new("count", entity_count),
            &(starts, ends, colors),
            |b, (starts, ends, colors)| {
                let mut renderer = SoftwareRenderer::new(BENCH_WIDTH, BENCH_HEIGHT);

                b.iter(|| {
                    renderer.begin_frame();
                    renderer.clear(Color::BLACK);

                    for i in 0..starts.len() {
                        renderer.draw_line(
                            black_box(starts[i]),
                            black_box(ends[i]),
                            black_box(1.0), // line width
                            black_box(colors[i]),
                        );
                    }

                    renderer.end_frame();
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Spline Rendering Benchmarks (Curved Branches)
// ============================================================================

/// Benchmarks rendering spline curves at various scales.
///
/// This simulates rendering curved branch connections.
fn benchmark_spline_rendering(c: &mut Criterion) {
    let mut group = c.benchmark_group("spline_rendering");

    for entity_count in [500, 1000, 2000, 5000] {
        group.throughput(Throughput::Elements(entity_count as u64));

        // Generate spline control points for each branch
        let splines: Vec<Vec<Vec2>> = generate_positions(entity_count)
            .iter()
            .map(|start| {
                let end = Vec2::new(start.x + 100.0, start.y + 60.0);
                let mid = start.lerp(end, 0.5);
                let ctrl1 = start.lerp(mid, 0.33) + Vec2::new(0.0, 15.0);
                let ctrl2 = mid.lerp(end, 0.66) + Vec2::new(0.0, -10.0);
                vec![*start, ctrl1, mid, ctrl2, end]
            })
            .collect();
        let colors = generate_colors(entity_count);

        group.bench_with_input(
            BenchmarkId::new("count", entity_count),
            &(splines, colors),
            |b, (splines, colors)| {
                let mut renderer = SoftwareRenderer::new(BENCH_WIDTH, BENCH_HEIGHT);

                b.iter(|| {
                    renderer.begin_frame();
                    renderer.clear(Color::BLACK);

                    for i in 0..splines.len() {
                        renderer.draw_spline(
                            black_box(&splines[i]),
                            black_box(1.5), // line width
                            black_box(colors[i]),
                        );
                    }

                    renderer.end_frame();
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Mixed Workload Benchmark (Realistic Scene)
// ============================================================================

/// Benchmarks a realistic mixed workload.
///
/// This simulates a real frame with:
/// - Files (discs with borders)
/// - Users (larger discs with glow)
/// - Branches (lines or splines)
/// - Directories (discs with center dots)
fn benchmark_mixed_workload(c: &mut Criterion) {
    let mut group = c.benchmark_group("mixed_workload");

    // Entity distribution ratios (typical visualization)
    // Files: 70%, Directories: 15%, Users: 5%, Branches: 10%

    for total_entities in [1000, 5000, 10000, 20000] {
        let file_count = total_entities * 70 / 100;
        let dir_count = total_entities * 15 / 100;
        let user_count = total_entities * 5 / 100;
        let branch_count = total_entities * 10 / 100;

        group.throughput(Throughput::Elements(total_entities as u64));

        let file_positions = generate_positions(file_count);
        let file_colors = generate_colors(file_count);
        let dir_positions = generate_positions(dir_count);
        let user_positions = generate_positions(user_count);
        let branch_starts = generate_positions(branch_count);
        let branch_ends: Vec<Vec2> = branch_starts
            .iter()
            .map(|p| Vec2::new(p.x + 80.0, p.y + 50.0))
            .collect();

        group.bench_with_input(
            BenchmarkId::new("total_entities", total_entities),
            &(
                file_positions.clone(),
                file_colors.clone(),
                dir_positions.clone(),
                user_positions.clone(),
                branch_starts.clone(),
                branch_ends.clone(),
            ),
            |b,
             (
                file_positions,
                file_colors,
                dir_positions,
                user_positions,
                branch_starts,
                branch_ends,
            )| {
                let mut renderer = SoftwareRenderer::new(BENCH_WIDTH, BENCH_HEIGHT);

                b.iter(|| {
                    renderer.begin_frame();
                    renderer.clear(Color::BLACK);

                    // Render branches first (back layer)
                    let branch_color = Color::new(0.4, 0.5, 0.6, 0.35);
                    for i in 0..branch_starts.len() {
                        renderer.draw_line(
                            black_box(branch_starts[i]),
                            black_box(branch_ends[i]),
                            black_box(1.0),
                            black_box(branch_color),
                        );
                    }

                    // Render directories
                    let dir_color = Color::new(0.3, 0.35, 0.4, 0.55);
                    for pos in dir_positions {
                        renderer.draw_disc(black_box(*pos), black_box(8.0), black_box(dir_color));
                        // Center dot
                        renderer.draw_disc(
                            black_box(*pos),
                            black_box(2.0),
                            black_box(dir_color.with_alpha(0.4)),
                        );
                    }

                    // Render files
                    for i in 0..file_positions.len() {
                        let radius = 4.0;
                        // File disc
                        renderer.draw_disc(
                            black_box(file_positions[i]),
                            black_box(radius),
                            black_box(file_colors[i]),
                        );
                        // Border
                        let border_color = file_colors[i].with_alpha(0.3);
                        renderer.draw_circle(
                            black_box(file_positions[i]),
                            black_box(radius + 1.0),
                            black_box(0.5),
                            black_box(border_color),
                        );
                    }

                    // Render users (largest, drawn last)
                    let user_color = Color::new(0.2, 0.7, 0.9, 1.0);
                    for pos in user_positions {
                        // Glow layers
                        for layer in 0..3 {
                            let glow_radius = 15.0 * (1.3 + layer as f32 * 0.15);
                            let glow_alpha = 0.15 * (1.0 - layer as f32 * 0.25);
                            renderer.draw_disc(
                                black_box(*pos),
                                black_box(glow_radius),
                                black_box(user_color.with_alpha(glow_alpha)),
                            );
                        }
                        // User disc
                        renderer.draw_disc(black_box(*pos), black_box(15.0), black_box(user_color));
                        // Border
                        renderer.draw_circle(
                            black_box(*pos),
                            black_box(16.0),
                            black_box(1.5),
                            black_box(user_color.with_alpha(0.5)),
                        );
                    }

                    renderer.end_frame();
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Frame Time Measurement
// ============================================================================

/// Benchmarks full frame time including clear and `end_frame`.
///
/// This measures the overhead of frame setup/teardown at various loads.
fn benchmark_frame_overhead(c: &mut Criterion) {
    let mut group = c.benchmark_group("frame_overhead");

    // Just frame management, no drawing
    group.bench_function("empty_frame", |b| {
        let mut renderer = SoftwareRenderer::new(BENCH_WIDTH, BENCH_HEIGHT);
        b.iter(|| {
            renderer.begin_frame();
            renderer.clear(black_box(Color::BLACK));
            renderer.end_frame();
        });
    });

    // Frame with minimal content
    group.bench_function("minimal_frame", |b| {
        let mut renderer = SoftwareRenderer::new(BENCH_WIDTH, BENCH_HEIGHT);
        b.iter(|| {
            renderer.begin_frame();
            renderer.clear(black_box(Color::BLACK));
            renderer.draw_disc(
                black_box(Vec2::new(960.0, 540.0)),
                black_box(50.0),
                black_box(Color::WHITE),
            );
            renderer.end_frame();
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    benchmark_disc_rendering,
    benchmark_circle_rendering,
    benchmark_line_rendering,
    benchmark_spline_rendering,
    benchmark_mixed_workload,
    benchmark_frame_overhead,
);

criterion_main!(benches);
