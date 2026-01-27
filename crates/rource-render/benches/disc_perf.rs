// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Disc rendering performance benchmarks.
//!
//! These benchmarks measure the performance of disc rendering operations
//! with statistical rigor (100 samples, 95% CI) for Phase 72 verification.

#![allow(missing_docs)]

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rource_math::Color;
use rource_render::backend::software::optimized::{
    draw_disc_optimized, draw_disc_precomputed, draw_disc_simd,
};
use std::hint::black_box;

// ============================================================================
// Disc Rendering Benchmarks
// ============================================================================

/// Benchmark disc rendering with different algorithms at various radii.
fn bench_disc_rendering(c: &mut Criterion) {
    let mut group = c.benchmark_group("disc_render");
    group.sample_size(100); // 100 samples for statistical significance

    // Test radii that span the threshold (radius < 12 uses fallback)
    for radius in [8, 12, 20, 50, 100, 150] {
        // Calculate viewport size to fit disc with margin
        let size = (radius as u32 * 3).max(100);
        let center = size as f32 / 2.0;
        let pixel_count = (radius as f32 * radius as f32 * std::f32::consts::PI) as u64;

        group.throughput(Throughput::Elements(pixel_count));

        // Benchmark original (draw_disc_optimized)
        group.bench_with_input(
            BenchmarkId::new("optimized", radius),
            &radius,
            |b, &radius| {
                let mut pixels = vec![0xFF00_0000u32; (size * size) as usize];
                b.iter(|| {
                    draw_disc_optimized(
                        &mut pixels,
                        size,
                        size,
                        center,
                        center,
                        radius as f32,
                        Color::WHITE,
                    );
                    black_box(&pixels);
                });
            },
        );

        // Benchmark Phase 71 SIMD (runtime run tracking)
        group.bench_with_input(
            BenchmarkId::new("simd_p71", radius),
            &radius,
            |b, &radius| {
                let mut pixels = vec![0xFF00_0000u32; (size * size) as usize];
                b.iter(|| {
                    draw_disc_simd(
                        &mut pixels,
                        size,
                        size,
                        center,
                        center,
                        radius as f32,
                        Color::WHITE,
                    );
                    black_box(&pixels);
                });
            },
        );

        // Benchmark Phase 72 precomputed (pre-computed inner bounds)
        group.bench_with_input(
            BenchmarkId::new("precomputed_p72", radius),
            &radius,
            |b, &radius| {
                let mut pixels = vec![0xFF00_0000u32; (size * size) as usize];
                b.iter(|| {
                    draw_disc_precomputed(
                        &mut pixels,
                        size,
                        size,
                        center,
                        center,
                        radius as f32,
                        Color::WHITE,
                    );
                    black_box(&pixels);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark disc rendering with alpha blending (partial transparency).
fn bench_disc_alpha(c: &mut Criterion) {
    let mut group = c.benchmark_group("disc_alpha");
    group.sample_size(100);

    let radius = 50;
    let size = 200u32;
    let center = 100.0f32;

    for alpha in [0.25, 0.5, 0.75, 1.0] {
        let color = Color::new(1.0, 0.5, 0.25, alpha);
        let pixel_count = (radius as f32 * radius as f32 * std::f32::consts::PI) as u64;

        group.throughput(Throughput::Elements(pixel_count));

        group.bench_with_input(
            BenchmarkId::new("optimized", format!("a={:.2}", alpha)),
            &color,
            |b, color| {
                let mut pixels = vec![0xFF00_0000u32; (size * size) as usize];
                b.iter(|| {
                    draw_disc_optimized(
                        &mut pixels,
                        size,
                        size,
                        center,
                        center,
                        radius as f32,
                        *color,
                    );
                    black_box(&pixels);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("precomputed_p72", format!("a={:.2}", alpha)),
            &color,
            |b, color| {
                let mut pixels = vec![0xFF00_0000u32; (size * size) as usize];
                b.iter(|| {
                    draw_disc_precomputed(
                        &mut pixels,
                        size,
                        size,
                        center,
                        center,
                        radius as f32,
                        *color,
                    );
                    black_box(&pixels);
                });
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_disc_rendering, bench_disc_alpha);
criterion_main!(benches);
