// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Benchmarks for Barnes-Hut theta parameter optimization.
//!
//! This benchmark suite measures:
//! 1. Force calculation time at various theta values
//! 2. Accuracy vs exact (theta=0) calculation
//! 3. Optimal theta curve based on entity count
//!
//! ## Benchmark Goals
//!
//! - Establish baseline performance at fixed theta (0.8)
//! - Measure speedup at higher theta values (0.9, 1.0, 1.2, 1.5)
//! - Measure accuracy degradation at higher theta values
//! - Determine adaptive theta function coefficients

// Benchmarks don't need documentation - suppress the warning from criterion macros
#![allow(missing_docs)]

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rource_math::{Bounds, Vec2};

/// Creates test bodies distributed across a bounded region.
///
/// Bodies are positioned in a grid-like pattern with some randomness
/// to simulate realistic directory node distributions.
fn create_test_bodies(count: usize) -> Vec<Vec2> {
    let mut bodies = Vec::with_capacity(count);
    let sqrt_count = (count as f32).sqrt() as usize;
    let spacing = 100.0;

    for i in 0..count {
        // Grid position with deterministic "randomness" for reproducibility
        let row = i / sqrt_count;
        let col = i % sqrt_count;

        // Add deterministic offset based on index for realistic distribution
        let offset_x = ((i * 7 + 13) % 50) as f32 - 25.0;
        let offset_y = ((i * 11 + 17) % 50) as f32 - 25.0;

        let x = (col as f32 - sqrt_count as f32 / 2.0) * spacing + offset_x;
        let y = (row as f32 - sqrt_count as f32 / 2.0) * spacing + offset_y;

        bodies.push(Vec2::new(x, y));
    }

    bodies
}

/// Compute bounds for a set of bodies with margin.
fn compute_bounds(bodies: &[Vec2]) -> Bounds {
    let mut min_x = f32::MAX;
    let mut min_y = f32::MAX;
    let mut max_x = f32::MIN;
    let mut max_y = f32::MIN;

    for pos in bodies {
        min_x = min_x.min(pos.x);
        min_y = min_y.min(pos.y);
        max_x = max_x.max(pos.x);
        max_y = max_y.max(pos.y);
    }

    let margin = 100.0;
    Bounds::new(
        Vec2::new(min_x - margin, min_y - margin),
        Vec2::new(max_x + margin, max_y + margin),
    )
}

/// Benchmarks force calculation time at various theta values.
///
/// This establishes the speed vs accuracy tradeoff for different theta parameters.
/// Lower theta = more accurate but slower, higher theta = faster but less accurate.
fn bench_barnes_hut_theta_speed(c: &mut Criterion) {
    use rource_core::physics::barnes_hut::{BarnesHutTree, Body};

    let mut group = c.benchmark_group("barnes_hut/theta_speed");

    // Test at multiple entity counts to verify scaling
    for entity_count in [100, 500, 1000, 5000] {
        let bodies = create_test_bodies(entity_count);
        let bounds = compute_bounds(&bodies);

        group.throughput(Throughput::Elements(entity_count as u64));

        // Test different theta values
        for theta in [0.3, 0.5, 0.7, 0.8, 1.0, 1.2, 1.5] {
            group.bench_with_input(
                BenchmarkId::new(format!("entities_{entity_count}"), format!("theta_{theta}")),
                &theta,
                |b, &theta| {
                    let mut tree = BarnesHutTree::with_theta(bounds.clone(), theta);

                    // Insert all bodies
                    for pos in &bodies {
                        tree.insert(Body::new(*pos));
                    }

                    // Benchmark force calculation for all bodies
                    b.iter(|| {
                        let mut total_force = Vec2::ZERO;
                        for pos in &bodies {
                            let body = Body::new(*pos);
                            let force =
                                tree.calculate_force(&body, black_box(800.0), black_box(25.0));
                            total_force += force;
                        }
                        black_box(total_force)
                    });
                },
            );
        }
    }

    group.finish();
}

/// Benchmarks the full force layout cycle including tree building.
///
/// This measures realistic per-frame performance including:
/// 1. Tree construction
/// 2. Body insertion
/// 3. Force calculation for all bodies
fn bench_barnes_hut_full_cycle(c: &mut Criterion) {
    use rource_core::physics::barnes_hut::{BarnesHutTree, Body};

    let mut group = c.benchmark_group("barnes_hut/full_cycle");

    for entity_count in [100, 500, 1000, 5000] {
        let bodies = create_test_bodies(entity_count);
        let bounds = compute_bounds(&bodies);

        group.throughput(Throughput::Elements(entity_count as u64));

        // Test key theta values
        for theta in [0.5, 0.8, 1.0, 1.5] {
            group.bench_with_input(
                BenchmarkId::new(format!("entities_{entity_count}"), format!("theta_{theta}")),
                &theta,
                |b, &theta| {
                    b.iter(|| {
                        // Build tree from scratch (simulates per-frame rebuild)
                        let mut tree = BarnesHutTree::with_theta(bounds.clone(), theta);

                        // Insert all bodies
                        for pos in &bodies {
                            tree.insert(Body::new(*pos));
                        }

                        // Calculate forces for all bodies
                        let mut forces: Vec<Vec2> = Vec::with_capacity(bodies.len());
                        for pos in &bodies {
                            let body = Body::new(*pos);
                            let force =
                                tree.calculate_force(&body, black_box(800.0), black_box(25.0));
                            forces.push(force);
                        }

                        black_box(forces)
                    });
                },
            );
        }
    }

    group.finish();
}

/// Benchmarks accuracy of different theta values compared to exact calculation.
///
/// Uses theta=0.0 as the "exact" baseline (no approximation) and measures
/// the relative error of approximated forces at higher theta values.
///
/// This is not a speed benchmark but rather a measurement of accuracy
/// to help determine acceptable theta ranges.
fn bench_barnes_hut_accuracy(c: &mut Criterion) {
    use rource_core::physics::barnes_hut::{BarnesHutTree, Body};

    let mut group = c.benchmark_group("barnes_hut/accuracy");

    // Test accuracy at a representative entity count
    for entity_count in [100, 500, 1000] {
        let bodies = create_test_bodies(entity_count);
        let bounds = compute_bounds(&bodies);

        group.throughput(Throughput::Elements(entity_count as u64));

        // Pre-compute exact forces (theta=0, but still using Barnes-Hut structure)
        // Note: theta=0 in Barnes-Hut still uses the tree but never approximates
        let mut exact_tree = BarnesHutTree::with_theta(bounds.clone(), 0.0);
        for pos in &bodies {
            exact_tree.insert(Body::new(*pos));
        }
        let exact_forces: Vec<Vec2> = bodies
            .iter()
            .map(|pos| {
                let body = Body::new(*pos);
                exact_tree.calculate_force(&body, 800.0, 25.0)
            })
            .collect();

        // Test accuracy at various theta values
        for theta in [0.5, 0.8, 1.0, 1.5] {
            group.bench_with_input(
                BenchmarkId::new(format!("entities_{entity_count}"), format!("theta_{theta}")),
                &theta,
                |b, &theta| {
                    let mut tree = BarnesHutTree::with_theta(bounds.clone(), theta);
                    for pos in &bodies {
                        tree.insert(Body::new(*pos));
                    }

                    b.iter(|| {
                        // Calculate approximated forces
                        let approx_forces: Vec<Vec2> = bodies
                            .iter()
                            .map(|pos| {
                                let body = Body::new(*pos);
                                tree.calculate_force(&body, black_box(800.0), black_box(25.0))
                            })
                            .collect();

                        // Calculate relative error
                        let total_error: f32 = approx_forces
                            .iter()
                            .zip(exact_forces.iter())
                            .map(|(approx, exact)| {
                                let exact_len = exact.length();
                                if exact_len > 0.001 {
                                    (*approx - *exact).length() / exact_len
                                } else {
                                    0.0
                                }
                            })
                            .sum();

                        let avg_error = total_error / bodies.len() as f32;
                        black_box(avg_error)
                    });
                },
            );
        }
    }

    group.finish();
}

/// Benchmarks adaptive theta selection overhead.
///
/// Measures the cost of computing adaptive theta based on entity count and FPS,
/// ensuring the overhead is negligible compared to force calculation savings.
fn bench_adaptive_theta_overhead(c: &mut Criterion) {
    let mut group = c.benchmark_group("barnes_hut/adaptive_overhead");

    // Test adaptive theta calculation overhead
    for entity_count in [100, 500, 1000, 5000] {
        group.throughput(Throughput::Elements(1));

        group.bench_with_input(
            BenchmarkId::new("compute_theta", entity_count),
            &entity_count,
            |b, &count| {
                b.iter(|| {
                    // Simulate adaptive theta calculation
                    // This is the proposed formula from FUTURE_OPTIMIZATIONS.md
                    let base_theta = 0.5f32;
                    let count_factor = (count as f32 / 500.0).log2().max(0.0) * 0.1;
                    let fps = black_box(30.0f32);
                    let fps_factor = if fps < 30.0 {
                        (30.0 - fps) / 30.0 * 0.2
                    } else {
                        0.0
                    };
                    let theta = (base_theta + count_factor + fps_factor).min(1.5);
                    black_box(theta)
                });
            },
        );
    }

    group.finish();
}

/// Benchmarks tree construction time separately from force calculation.
///
/// This helps identify whether optimization opportunities exist in
/// tree building vs force computation.
fn bench_tree_construction(c: &mut Criterion) {
    use rource_core::physics::barnes_hut::{BarnesHutTree, Body};

    let mut group = c.benchmark_group("barnes_hut/tree_construction");

    for entity_count in [100, 500, 1000, 5000] {
        let bodies = create_test_bodies(entity_count);
        let bounds = compute_bounds(&bodies);

        group.throughput(Throughput::Elements(entity_count as u64));

        group.bench_with_input(
            BenchmarkId::new("build", entity_count),
            &entity_count,
            |b, _| {
                b.iter(|| {
                    let mut tree = BarnesHutTree::new(bounds.clone());
                    for pos in &bodies {
                        tree.insert(Body::new(*pos));
                    }
                    black_box(tree.total_mass())
                });
            },
        );
    }

    group.finish();
}

/// Benchmarks tree clear and reuse vs fresh allocation.
///
/// Verifies that tree reuse (clear + reinsert) is faster than
/// creating a new tree each frame.
fn bench_tree_reuse(c: &mut Criterion) {
    use rource_core::physics::barnes_hut::{BarnesHutTree, Body};

    let mut group = c.benchmark_group("barnes_hut/tree_reuse");

    for entity_count in [500, 1000, 5000] {
        let bodies = create_test_bodies(entity_count);
        let bounds = compute_bounds(&bodies);

        group.throughput(Throughput::Elements(entity_count as u64));

        // Benchmark: fresh allocation each frame
        group.bench_with_input(
            BenchmarkId::new("fresh_alloc", entity_count),
            &entity_count,
            |b, _| {
                b.iter(|| {
                    let mut tree = BarnesHutTree::new(bounds.clone());
                    for pos in &bodies {
                        tree.insert(Body::new(*pos));
                    }
                    black_box(tree.total_mass())
                });
            },
        );

        // Benchmark: clear and reuse
        group.bench_with_input(
            BenchmarkId::new("clear_reuse", entity_count),
            &entity_count,
            |b, _| {
                let mut tree = BarnesHutTree::new(bounds.clone());
                // Prime the tree structure
                for pos in &bodies {
                    tree.insert(Body::new(*pos));
                }

                b.iter(|| {
                    tree.clear();
                    for pos in &bodies {
                        tree.insert(Body::new(*pos));
                    }
                    black_box(tree.total_mass())
                });
            },
        );
    }

    group.finish();
}

/// Benchmarks fixed theta (0.8) vs adaptive theta.
///
/// This is the key benchmark showing the improvement from Phase 62.
/// Compares the current default (fixed θ=0.8) against the new adaptive theta.
fn bench_fixed_vs_adaptive(c: &mut Criterion) {
    use rource_core::physics::barnes_hut::{calculate_adaptive_theta, BarnesHutTree, Body};

    let mut group = c.benchmark_group("barnes_hut/fixed_vs_adaptive");

    for entity_count in [100, 500, 1000, 5000] {
        let bodies = create_test_bodies(entity_count);
        let bounds = compute_bounds(&bodies);

        group.throughput(Throughput::Elements(entity_count as u64));

        // Fixed theta = 0.8 (baseline, current default)
        group.bench_with_input(
            BenchmarkId::new(format!("entities_{entity_count}"), "fixed_0.8"),
            &entity_count,
            |b, _| {
                let mut tree = BarnesHutTree::with_theta(bounds.clone(), 0.8);
                for pos in &bodies {
                    tree.insert(Body::new(*pos));
                }

                b.iter(|| {
                    let mut total_force = Vec2::ZERO;
                    for pos in &bodies {
                        let body = Body::new(*pos);
                        let force = tree.calculate_force(&body, black_box(800.0), black_box(25.0));
                        total_force += force;
                    }
                    black_box(total_force)
                });
            },
        );

        // Adaptive theta (new Phase 62 optimization)
        let adaptive_theta = calculate_adaptive_theta(entity_count);
        group.bench_with_input(
            BenchmarkId::new(
                format!("entities_{entity_count}"),
                format!("adaptive_{adaptive_theta:.2}"),
            ),
            &entity_count,
            |b, _| {
                let mut tree = BarnesHutTree::with_theta(bounds.clone(), adaptive_theta);
                for pos in &bodies {
                    tree.insert(Body::new(*pos));
                }

                b.iter(|| {
                    let mut total_force = Vec2::ZERO;
                    for pos in &bodies {
                        let body = Body::new(*pos);
                        let force = tree.calculate_force(&body, black_box(800.0), black_box(25.0));
                        total_force += force;
                    }
                    black_box(total_force)
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_barnes_hut_theta_speed,
    bench_barnes_hut_full_cycle,
    bench_barnes_hut_accuracy,
    bench_adaptive_theta_overhead,
    bench_tree_construction,
    bench_tree_reuse,
    bench_fixed_vs_adaptive,
);

criterion_main!(benches);
