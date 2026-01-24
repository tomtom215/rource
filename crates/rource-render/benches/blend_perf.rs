// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Alpha blending performance benchmarks.
//!
//! These benchmarks measure the performance of color blending operations
//! which are called for every non-opaque pixel during rendering.

#![allow(missing_docs)]
#![allow(clippy::unreadable_literal)]
#![allow(clippy::cast_lossless)]
#![allow(clippy::unnecessary_cast)]
#![allow(clippy::doc_markdown)]

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rource_math::Color;

// ============================================================================
// Current implementation (floating-point)
// ============================================================================

/// Current blend_color implementation (baseline).
#[inline]
fn blend_color_baseline(existing: u32, src: Color) -> u32 {
    let alpha = src.a;
    if alpha < 0.001 {
        return existing;
    }

    let inv_alpha = 1.0 - alpha;

    // Extract existing RGB
    let dst_r = ((existing >> 16) & 0xFF) as f32;
    let dst_g = ((existing >> 8) & 0xFF) as f32;
    let dst_b = (existing & 0xFF) as f32;

    // Source RGB (0-1 in Color)
    let src_r = src.r * 255.0;
    let src_g = src.g * 255.0;
    let src_b = src.b * 255.0;

    // Blend
    let new_r = ((src_r * alpha + dst_r * inv_alpha) as u32).min(255);
    let new_g = ((src_g * alpha + dst_g * inv_alpha) as u32).min(255);
    let new_b = ((src_b * alpha + dst_b * inv_alpha) as u32).min(255);

    0xFF00_0000 | (new_r << 16) | (new_g << 8) | new_b
}

// ============================================================================
// Optimized implementation (fixed-point 8.8 arithmetic)
// ============================================================================

/// Optimized blend using 8.8 fixed-point arithmetic.
///
/// Key optimizations:
/// 1. Convert alpha to 0-256 integer range (avoids float in inner loop)
/// 2. Use integer multiply-shift instead of float multiply
/// 3. Avoid min() by using saturating arithmetic or clamping range
#[inline]
fn blend_color_fixed_point(existing: u32, src: Color) -> u32 {
    // Convert alpha to 0-256 range (8.8 fixed point with 8-bit fraction)
    // Using 256 instead of 255 allows shift-based division: x * alpha >> 8
    let alpha_u16 = (src.a * 256.0) as u16;

    if alpha_u16 == 0 {
        return existing;
    }

    // Fast path for fully opaque
    if alpha_u16 >= 256 {
        let r = (src.r * 255.0) as u32;
        let g = (src.g * 255.0) as u32;
        let b = (src.b * 255.0) as u32;
        return 0xFF00_0000 | (r << 16) | (g << 8) | b;
    }

    let inv_alpha = 256 - alpha_u16;

    // Extract existing RGB as u16 for intermediate calculations
    let dst_r = ((existing >> 16) & 0xFF) as u16;
    let dst_g = ((existing >> 8) & 0xFF) as u16;
    let dst_b = (existing & 0xFF) as u16;

    // Convert source RGB to 0-255 range
    let src_r = (src.r * 255.0) as u16;
    let src_g = (src.g * 255.0) as u16;
    let src_b = (src.b * 255.0) as u16;

    // Blend using fixed-point: result = (src * alpha + dst * inv_alpha) >> 8
    // Max value: 255 * 256 + 255 * 256 = 130560, fits in u32
    let new_r = ((src_r as u32 * alpha_u16 as u32 + dst_r as u32 * inv_alpha as u32) >> 8) as u32;
    let new_g = ((src_g as u32 * alpha_u16 as u32 + dst_g as u32 * inv_alpha as u32) >> 8) as u32;
    let new_b = ((src_b as u32 * alpha_u16 as u32 + dst_b as u32 * inv_alpha as u32) >> 8) as u32;

    0xFF00_0000 | (new_r << 16) | (new_g << 8) | new_b
}

// ============================================================================
// Alternative: Pre-multiplied source optimization
// ============================================================================

/// Blend with pre-converted source (for batch operations).
///
/// When rendering multiple pixels with the same color, we can pre-convert
/// the color components once and reuse them.
#[inline]
fn blend_color_preconverted(
    existing: u32,
    src_r: u16,
    src_g: u16,
    src_b: u16,
    alpha_u16: u16,
    inv_alpha: u16,
) -> u32 {
    if alpha_u16 == 0 {
        return existing;
    }

    // Extract existing RGB
    let dst_r = ((existing >> 16) & 0xFF) as u16;
    let dst_g = ((existing >> 8) & 0xFF) as u16;
    let dst_b = (existing & 0xFF) as u16;

    // Blend using fixed-point
    let new_r = ((src_r as u32 * alpha_u16 as u32 + dst_r as u32 * inv_alpha as u32) >> 8) as u32;
    let new_g = ((src_g as u32 * alpha_u16 as u32 + dst_g as u32 * inv_alpha as u32) >> 8) as u32;
    let new_b = ((src_b as u32 * alpha_u16 as u32 + dst_b as u32 * inv_alpha as u32) >> 8) as u32;

    0xFF00_0000 | (new_r << 16) | (new_g << 8) | new_b
}

/// Converts a Color to pre-computed blend parameters.
#[inline]
fn preconvert_color(color: Color) -> (u16, u16, u16, u16, u16) {
    let alpha_u16 = (color.a * 256.0) as u16;
    let inv_alpha = 256u16.saturating_sub(alpha_u16);
    let src_r = (color.r * 255.0) as u16;
    let src_g = (color.g * 255.0) as u16;
    let src_b = (color.b * 255.0) as u16;
    (src_r, src_g, src_b, alpha_u16, inv_alpha)
}

// ============================================================================
// Benchmarks
// ============================================================================

/// Creates test data for blending benchmarks.
fn create_test_data(count: usize) -> (Vec<u32>, Vec<Color>) {
    let mut backgrounds = Vec::with_capacity(count);
    let mut colors = Vec::with_capacity(count);

    for i in 0..count {
        // Varied background colors
        let bg_r = ((i * 37) % 256) as u32;
        let bg_g = ((i * 73) % 256) as u32;
        let bg_b = ((i * 113) % 256) as u32;
        backgrounds.push(0xFF00_0000 | (bg_r << 16) | (bg_g << 8) | bg_b);

        // Varied source colors with different alpha values
        let alpha = ((i % 100) as f32) / 100.0;
        let r = ((i * 17) % 256) as f32 / 255.0;
        let g = ((i * 31) % 256) as f32 / 255.0;
        let b = ((i * 47) % 256) as f32 / 255.0;
        colors.push(Color::new(r, g, b, alpha));
    }

    (backgrounds, colors)
}

/// Benchmark single-pixel blend operations.
fn bench_blend_single(c: &mut Criterion) {
    let mut group = c.benchmark_group("blend_single");

    // Test with different alpha values
    let alphas = [0.0, 0.25, 0.5, 0.75, 1.0];
    let background = 0xFF80_4020u32; // Some arbitrary background

    for alpha in alphas {
        let color = Color::new(1.0, 0.5, 0.25, alpha);

        group.bench_with_input(
            BenchmarkId::new("baseline", format!("alpha={alpha}")),
            &alpha,
            |b, _| {
                b.iter(|| blend_color_baseline(black_box(background), black_box(color)));
            },
        );

        group.bench_with_input(
            BenchmarkId::new("fixed_point", format!("alpha={alpha}")),
            &alpha,
            |b, _| {
                b.iter(|| blend_color_fixed_point(black_box(background), black_box(color)));
            },
        );
    }

    group.finish();
}

/// Benchmark batch blend operations (simulates rendering a filled shape).
fn bench_blend_batch(c: &mut Criterion) {
    let mut group = c.benchmark_group("blend_batch");

    // Simulate different rendering scenarios
    for pixel_count in [1000, 10000, 100000] {
        group.throughput(Throughput::Elements(pixel_count as u64));

        let (backgrounds, colors) = create_test_data(pixel_count);

        // Baseline
        group.bench_with_input(
            BenchmarkId::new("baseline", pixel_count),
            &pixel_count,
            |b, _| {
                b.iter(|| {
                    let mut result = 0u32;
                    for (bg, color) in backgrounds.iter().zip(colors.iter()) {
                        result ^= blend_color_baseline(*bg, *color);
                    }
                    black_box(result)
                });
            },
        );

        // Fixed-point
        group.bench_with_input(
            BenchmarkId::new("fixed_point", pixel_count),
            &pixel_count,
            |b, _| {
                b.iter(|| {
                    let mut result = 0u32;
                    for (bg, color) in backgrounds.iter().zip(colors.iter()) {
                        result ^= blend_color_fixed_point(*bg, *color);
                    }
                    black_box(result)
                });
            },
        );
    }

    group.finish();
}

/// Benchmark same-color batch (common case: filling a shape with single color).
fn bench_blend_same_color(c: &mut Criterion) {
    let mut group = c.benchmark_group("blend_same_color");

    let pixel_count = 50000; // Typical disc size
    group.throughput(Throughput::Elements(pixel_count as u64));

    let mut backgrounds = Vec::with_capacity(pixel_count);
    for i in 0..pixel_count {
        let bg = 0xFF00_0000 | ((i as u32 * 17) % 0xFF_FFFF);
        backgrounds.push(bg);
    }

    let color = Color::new(0.8, 0.3, 0.1, 0.6);

    // Baseline (no preconversion)
    group.bench_function("baseline", |b| {
        b.iter(|| {
            let mut result = 0u32;
            for bg in &backgrounds {
                result ^= blend_color_baseline(*bg, color);
            }
            black_box(result)
        });
    });

    // Fixed-point (no preconversion)
    group.bench_function("fixed_point", |b| {
        b.iter(|| {
            let mut result = 0u32;
            for bg in &backgrounds {
                result ^= blend_color_fixed_point(*bg, color);
            }
            black_box(result)
        });
    });

    // Pre-converted (optimal for same-color batch)
    group.bench_function("preconverted", |b| {
        let (src_r, src_g, src_b, alpha, inv_alpha) = preconvert_color(color);
        b.iter(|| {
            let mut result = 0u32;
            for bg in &backgrounds {
                result ^= blend_color_preconverted(*bg, src_r, src_g, src_b, alpha, inv_alpha);
            }
            black_box(result)
        });
    });

    group.finish();
}

/// Verify correctness of optimized implementations.
#[test]
fn test_blend_correctness() {
    let test_cases = [
        (0xFF00_0000, Color::new(1.0, 0.0, 0.0, 0.5)),
        (0xFFFF_FFFF, Color::new(0.0, 1.0, 0.0, 0.25)),
        (0xFF80_8080, Color::new(0.5, 0.5, 0.5, 0.75)),
        (0xFF12_3456, Color::new(0.1, 0.2, 0.3, 0.0)), // Zero alpha
        (0xFF12_3456, Color::new(0.1, 0.2, 0.3, 1.0)), // Full alpha
    ];

    for (bg, color) in test_cases {
        let baseline = blend_color_baseline(bg, color);
        let fixed = blend_color_fixed_point(bg, color);

        // Allow 1 unit difference due to rounding
        let diff_r = ((baseline >> 16) & 0xFF) as i32 - ((fixed >> 16) & 0xFF) as i32;
        let diff_g = ((baseline >> 8) & 0xFF) as i32 - ((fixed >> 8) & 0xFF) as i32;
        let diff_b = (baseline & 0xFF) as i32 - (fixed & 0xFF) as i32;

        assert!(
            diff_r.abs() <= 1 && diff_g.abs() <= 1 && diff_b.abs() <= 1,
            "Mismatch at bg={bg:#010X}, color={color:?}: baseline={baseline:#010X}, fixed={fixed:#010X}"
        );
    }
}

criterion_group!(
    benches,
    bench_blend_single,
    bench_blend_batch,
    bench_blend_same_color
);
criterion_main!(benches);
