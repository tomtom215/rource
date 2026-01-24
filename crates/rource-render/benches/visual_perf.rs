// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Visual rendering performance benchmarks.
//!
//! These benchmarks measure the performance of visual rendering functions
//! including branch curve creation and perpendicular vector operations.

#![allow(missing_docs)]
#![allow(clippy::doc_markdown)]

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rource_math::Vec2;

// ============================================================================
// Perpendicular Vector Normalization Benchmarks
// ============================================================================

/// Baseline: Normalize perpendicular then multiply by length.
///
/// This was the old approach:
/// ```ignore
/// let perp = Vec2::new(-dir.y, dir.x).normalized();
/// let offset = perp * length * tension * 0.15;
/// ```
#[inline]
fn perpendicular_normalized(dir: Vec2, length: f32, tension: f32) -> Vec2 {
    let perp = Vec2::new(-dir.y, dir.x).normalized();
    perp * length * tension * 0.15
}

/// Optimized: Skip normalization since perpendicular has same length as original.
///
/// Key insight: |(-dir.y, dir.x)| == |dir| == length
/// Therefore: (perp / length) * length = perp
///
/// This eliminates one sqrt() call.
#[inline]
fn perpendicular_optimized(dir: Vec2, _length: f32, tension: f32) -> Vec2 {
    let perp = Vec2::new(-dir.y, dir.x);
    perp * tension * 0.15
}

/// Full branch curve creation baseline (with normalized perpendicular).
#[inline]
fn create_branch_curve_baseline(start: Vec2, end: Vec2, tension: f32) -> Vec<Vec2> {
    let mid = start.lerp(end, 0.5);
    let dir = end - start;
    let length = dir.length();

    if length < 1.0 {
        return vec![start, end];
    }

    // Old approach: normalize then multiply by length
    let perp = Vec2::new(-dir.y, dir.x).normalized();
    let offset = perp * length * tension * 0.15;

    // Create control points
    let ctrl1 = start.lerp(mid, 0.33) + offset * 0.5;
    let ctrl2 = start.lerp(mid, 0.66) + offset;
    let ctrl3 = mid.lerp(end, 0.33) + offset * 0.5;
    let ctrl4 = mid.lerp(end, 0.66);

    vec![start, ctrl1, ctrl2, ctrl3, ctrl4, end]
}

/// Full branch curve creation optimized (perpendicular without normalization).
#[inline]
fn create_branch_curve_optimized(start: Vec2, end: Vec2, tension: f32) -> Vec<Vec2> {
    let mid = start.lerp(end, 0.5);
    let dir = end - start;
    let length = dir.length();

    if length < 1.0 {
        return vec![start, end];
    }

    // Optimized: perpendicular already has length |dir|, no normalization needed
    let perp = Vec2::new(-dir.y, dir.x);
    let offset = perp * tension * 0.15;

    // Create control points
    let ctrl1 = start.lerp(mid, 0.33) + offset * 0.5;
    let ctrl2 = start.lerp(mid, 0.66) + offset;
    let ctrl3 = mid.lerp(end, 0.33) + offset * 0.5;
    let ctrl4 = mid.lerp(end, 0.66);

    vec![start, ctrl1, ctrl2, ctrl3, ctrl4, end]
}

// ============================================================================
// Benchmarks
// ============================================================================

fn benchmark_perpendicular(c: &mut Criterion) {
    let mut group = c.benchmark_group("perpendicular_normalization");

    // Test vectors of various lengths
    let test_cases = vec![
        (Vec2::new(10.0, 0.0), 10.0, "horizontal"),
        (Vec2::new(0.0, 10.0), 10.0, "vertical"),
        (Vec2::new(30.0, 40.0), 50.0, "3-4-5 triangle"),
        (Vec2::new(100.0, 200.0), 223.6, "long diagonal"),
    ];

    for (dir, length, name) in &test_cases {
        let tension = 0.3;

        group.bench_with_input(
            BenchmarkId::new("baseline", name),
            &(*dir, *length, tension),
            |b, &(dir, length, tension)| {
                b.iter(|| {
                    perpendicular_normalized(black_box(dir), black_box(length), black_box(tension))
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("optimized", name),
            &(*dir, *length, tension),
            |b, &(dir, length, tension)| {
                b.iter(|| {
                    perpendicular_optimized(black_box(dir), black_box(length), black_box(tension))
                })
            },
        );
    }

    group.finish();
}

fn benchmark_branch_curve(c: &mut Criterion) {
    let mut group = c.benchmark_group("branch_curve_creation");

    // Typical branch distances in a visualization
    let test_cases = vec![
        (Vec2::new(0.0, 0.0), Vec2::new(50.0, 30.0), "short_branch"),
        (
            Vec2::new(0.0, 0.0),
            Vec2::new(150.0, 100.0),
            "medium_branch",
        ),
        (Vec2::new(0.0, 0.0), Vec2::new(300.0, 200.0), "long_branch"),
    ];

    for (start, end, name) in &test_cases {
        let tension = 0.3;

        group.bench_with_input(
            BenchmarkId::new("baseline", name),
            &(*start, *end, tension),
            |b, &(start, end, tension)| {
                b.iter(|| {
                    create_branch_curve_baseline(
                        black_box(start),
                        black_box(end),
                        black_box(tension),
                    )
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("optimized", name),
            &(*start, *end, tension),
            |b, &(start, end, tension)| {
                b.iter(|| {
                    create_branch_curve_optimized(
                        black_box(start),
                        black_box(end),
                        black_box(tension),
                    )
                })
            },
        );
    }

    group.finish();
}

fn benchmark_batch_curves(c: &mut Criterion) {
    let mut group = c.benchmark_group("batch_branch_curves");
    group.throughput(Throughput::Elements(1000));

    // Generate 1000 random-ish branch endpoints
    let branches: Vec<(Vec2, Vec2)> = (0..1000)
        .map(|i| {
            let angle = (i as f32 * 0.1).sin() * std::f32::consts::PI;
            let dist = 50.0 + (i as f32 * 0.3).cos() * 100.0;
            let start = Vec2::new((i % 100) as f32 * 10.0, (i / 100) as f32 * 10.0);
            let end = start + Vec2::new(angle.cos() * dist, angle.sin() * dist);
            (start, end)
        })
        .collect();

    let tension = 0.3;

    group.bench_function("baseline_1000", |b| {
        b.iter(|| {
            for (start, end) in &branches {
                black_box(create_branch_curve_baseline(*start, *end, tension));
            }
        })
    });

    group.bench_function("optimized_1000", |b| {
        b.iter(|| {
            for (start, end) in &branches {
                black_box(create_branch_curve_optimized(*start, *end, tension));
            }
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    benchmark_perpendicular,
    benchmark_branch_curve,
    benchmark_batch_curves
);
criterion_main!(benches);
