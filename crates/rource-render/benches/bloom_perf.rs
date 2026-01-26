// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Bloom effect performance benchmarks.
//!
//! These benchmarks measure the performance of the bloom effect at various
//! resolutions to verify optimization effectiveness.

#![allow(missing_docs)]

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rource_render::effects::BloomEffect;
use std::hint::black_box;

/// Creates a test pixel buffer with some bright regions for bloom testing.
fn create_test_buffer(width: usize, height: usize) -> Vec<u32> {
    let mut pixels = vec![0xFF00_0000u32; width * height];

    // Add some bright white regions scattered around
    for y in (0..height).step_by(height / 4) {
        for x in (0..width).step_by(width / 4) {
            // Create 8x8 bright spots
            for dy in 0..8.min(height - y) {
                for dx in 0..8.min(width - x) {
                    pixels[(y + dy) * width + (x + dx)] = 0xFFFF_FFFF;
                }
            }
        }
    }

    pixels
}

/// Benchmark the full bloom effect pipeline.
fn bench_bloom_full(c: &mut Criterion) {
    let mut group = c.benchmark_group("bloom_full");

    // Test at different resolutions (downscaled buffer sizes)
    // Default downscale=4, so 1920x1080 -> 480x270
    let resolutions = [
        (320, 180, "320x180"), // Small (e.g., 1280x720 / 4)
        (480, 270, "480x270"), // Medium (1920x1080 / 4)
        (640, 360, "640x360"), // Large (2560x1440 / 4)
        (960, 540, "960x540"), // XL (3840x2160 / 4)
    ];

    for (width, height, label) in resolutions {
        let full_w = width * 4;
        let full_h = height * 4;
        let pixel_count = (full_w * full_h) as u64;

        group.throughput(Throughput::Elements(pixel_count));

        let mut bloom = BloomEffect::new();
        let mut pixels = create_test_buffer(full_w, full_h);

        // Warm up buffers
        bloom.apply(&mut pixels, full_w, full_h);

        group.bench_with_input(BenchmarkId::new("apply", label), &label, |b, _| {
            b.iter(|| {
                let mut test_pixels = create_test_buffer(full_w, full_h);
                bloom.apply(black_box(&mut test_pixels), full_w, full_h);
                black_box(test_pixels)
            });
        });
    }

    group.finish();
}

/// Benchmark just the blur operation (most cache-sensitive part).
fn bench_bloom_blur_only(c: &mut Criterion) {
    let mut group = c.benchmark_group("bloom_blur");

    // Test blur at downscaled buffer sizes
    let sizes = [
        (120, 68, "120x68"),   // 480x270 / 4
        (240, 135, "240x135"), // 960x540 / 4
        (480, 270, "480x270"), // Direct
        (960, 540, "960x540"), // Large
    ];

    for (width, height, label) in sizes {
        let pixel_count = (width * height) as u64;
        group.throughput(Throughput::Elements(pixel_count));

        // Use downscale=1 to directly test blur at these sizes
        let mut bloom = BloomEffect::new().with_downscale(1);
        let mut pixels = create_test_buffer(width, height);

        // Warm up
        bloom.apply(&mut pixels, width, height);

        group.bench_with_input(BenchmarkId::new("passes", label), &label, |b, _| {
            b.iter(|| {
                let mut test_pixels = create_test_buffer(width, height);
                bloom.apply(black_box(&mut test_pixels), width, height);
                black_box(test_pixels)
            });
        });
    }

    group.finish();
}

/// Benchmark with varying number of blur passes.
fn bench_bloom_passes(c: &mut Criterion) {
    let mut group = c.benchmark_group("bloom_passes");

    let width = 480;
    let height = 270;
    let pixel_count = (width * height) as u64;
    group.throughput(Throughput::Elements(pixel_count));

    for passes in [1, 2, 3, 4] {
        let mut bloom = BloomEffect::new().with_downscale(1).with_passes(passes);
        let mut pixels = create_test_buffer(width, height);

        // Warm up
        bloom.apply(&mut pixels, width, height);

        group.bench_with_input(BenchmarkId::new("count", passes), &passes, |b, _| {
            b.iter(|| {
                let mut test_pixels = create_test_buffer(width, height);
                bloom.apply(black_box(&mut test_pixels), width, height);
                black_box(test_pixels)
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_bloom_full,
    bench_bloom_blur_only,
    bench_bloom_passes
);
criterion_main!(benches);
