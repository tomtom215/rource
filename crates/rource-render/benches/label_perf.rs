// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Label collision detection benchmarks.
//!
//! Measures the performance of label placement and collision detection
//! in the core library (rource-render).
//!
//! Run with: cargo bench -p rource-render --bench label_perf

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rource_math::Vec2;
use rource_render::LabelPlacer;

/// Benchmark LabelPlacer creation.
fn bench_label_placer_new(c: &mut Criterion) {
    c.bench_function("LabelPlacer::new", |b| {
        b.iter(|| std::hint::black_box(LabelPlacer::new(1.0)));
    });
}

/// Benchmark LabelPlacer reset.
fn bench_label_placer_reset(c: &mut Criterion) {
    let mut group = c.benchmark_group("LabelPlacer::reset");

    for label_count in [0, 10, 50, 100, 200] {
        let mut placer = LabelPlacer::new(1.0);

        // Pre-populate with labels
        for i in 0..label_count {
            placer.try_place(
                Vec2::new(i as f32 * 100.0, (i / 20) as f32 * 50.0),
                50.0,
                20.0,
            );
        }

        group.throughput(Throughput::Elements(1));
        group.bench_with_input(
            BenchmarkId::new("labels", label_count),
            &label_count,
            |b, _| {
                b.iter(|| {
                    placer.reset(1.0);
                    // Add one label to make reset realistic
                    placer.try_place(Vec2::new(0.0, 0.0), 50.0, 20.0);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark try_place with increasing label counts (collision detection scaling).
///
/// This is the key benchmark for O(n) vs O(1) complexity.
fn bench_label_placer_try_place(c: &mut Criterion) {
    let mut group = c.benchmark_group("LabelPlacer::try_place");

    for label_count in [0, 10, 25, 50, 100, 200] {
        let mut placer = LabelPlacer::new(1.0);
        placer.set_viewport(4000.0, 3000.0); // Large viewport to avoid bounds rejection

        // Pre-populate with labels (spread out to avoid early collisions)
        for i in 0..label_count {
            let x = (i % 30) as f32 * 120.0;
            let y = (i / 30) as f32 * 60.0;
            placer.try_place(Vec2::new(x, y), 50.0, 20.0);
        }

        group.throughput(Throughput::Elements(1));
        group.bench_with_input(
            BenchmarkId::new("existing_labels", label_count),
            &label_count,
            |b, _| {
                // Try to place a label that will need to check against all existing labels
                // but won't collide (placed in empty space)
                let test_pos = Vec2::new(3500.0, 2500.0);
                b.iter(|| {
                    let result = placer.try_place(test_pos, 50.0, 20.0);
                    // Reset to allow repeated placement
                    if result {
                        placer.reset(1.0);
                        // Re-populate
                        for i in 0..label_count {
                            let x = (i % 30) as f32 * 120.0;
                            let y = (i / 30) as f32 * 60.0;
                            placer.try_place(Vec2::new(x, y), 50.0, 20.0);
                        }
                    }
                    std::hint::black_box(result)
                });
            },
        );
    }

    group.finish();
}

/// Benchmark collision checking only (without placement).
///
/// This isolates the collision detection cost from the Vec push.
fn bench_collision_detection(c: &mut Criterion) {
    let mut group = c.benchmark_group("collision_detection");

    for label_count in [10, 25, 50, 100, 200] {
        let mut placer = LabelPlacer::new(1.0);
        placer.set_viewport(4000.0, 3000.0);

        // Pre-populate with labels
        for i in 0..label_count {
            let x = (i % 30) as f32 * 120.0;
            let y = (i / 30) as f32 * 60.0;
            placer.try_place(Vec2::new(x, y), 50.0, 20.0);
        }

        group.throughput(Throughput::Elements(label_count as u64));
        group.bench_with_input(
            BenchmarkId::new("labels", label_count),
            &label_count,
            |b, _| {
                // Place a label that collides (forces checking all existing labels)
                let colliding_pos = Vec2::new(0.0, 0.0);
                b.iter(|| {
                    // This will check against all labels before finding collision
                    std::hint::black_box(placer.try_place(colliding_pos, 50.0, 20.0))
                });
            },
        );
    }

    group.finish();
}

/// Benchmark try_place_with_fallback (multiple collision checks per call).
fn bench_try_place_with_fallback(c: &mut Criterion) {
    let mut group = c.benchmark_group("LabelPlacer::try_place_with_fallback");

    for label_count in [10, 25, 50, 100] {
        let mut placer = LabelPlacer::new(1.0);
        placer.set_viewport(4000.0, 3000.0);

        // Pre-populate with labels
        for i in 0..label_count {
            let x = (i % 20) as f32 * 100.0;
            let y = (i / 20) as f32 * 80.0;
            placer.try_place(Vec2::new(x, y), 50.0, 20.0);
        }

        group.throughput(Throughput::Elements(1));
        group.bench_with_input(
            BenchmarkId::new("existing_labels", label_count),
            &label_count,
            |b, _| {
                let primary = Vec2::new(2000.0, 1500.0);
                let anchor = Vec2::new(1990.0, 1490.0);
                b.iter(|| {
                    let result = placer.try_place_with_fallback(primary, 50.0, 20.0, anchor, 10.0);
                    // Reset if placed to allow repeated benchmark
                    if result.is_some() {
                        placer.reset(1.0);
                        for i in 0..label_count {
                            let x = (i % 20) as f32 * 100.0;
                            let y = (i / 20) as f32 * 80.0;
                            placer.try_place(Vec2::new(x, y), 50.0, 20.0);
                        }
                    }
                    std::hint::black_box(result)
                });
            },
        );
    }

    group.finish();
}

/// Benchmark full label placement scenario (realistic frame simulation).
fn bench_full_frame_scenario(c: &mut Criterion) {
    c.bench_function("full_frame_30_users_50_files", |b| {
        b.iter(|| {
            let mut placer = LabelPlacer::new(1.0);
            placer.set_viewport(1920.0, 1080.0);

            // Place user labels (high priority, spread across screen)
            for i in 0..30 {
                let x = (i % 10) as f32 * 150.0;
                let y = (i / 10) as f32 * 200.0;
                placer.try_place_with_fallback(
                    Vec2::new(x + 20.0, y),
                    60.0,
                    18.0,
                    Vec2::new(x, y + 10.0),
                    15.0,
                );
            }

            // Place file labels (lower priority, denser)
            for i in 0..50 {
                let x = (i % 15) as f32 * 100.0;
                let y = (i / 15) as f32 * 150.0 + 50.0;
                placer.try_place_with_fallback(
                    Vec2::new(x + 10.0, y),
                    50.0,
                    14.0,
                    Vec2::new(x, y + 5.0),
                    8.0,
                );
            }

            std::hint::black_box(placer.count())
        });
    });
}

criterion_group!(
    benches,
    bench_label_placer_new,
    bench_label_placer_reset,
    bench_label_placer_try_place,
    bench_collision_detection,
    bench_try_place_with_fallback,
    bench_full_frame_scenario,
);

criterion_main!(benches);
