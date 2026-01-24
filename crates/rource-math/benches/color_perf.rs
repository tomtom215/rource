// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Color conversion performance benchmarks.
//!
//! These benchmarks measure the performance of color conversion operations
//! which are called frequently during rendering and UI operations.

#![allow(missing_docs)]
#![allow(clippy::unreadable_literal)]
#![allow(clippy::cast_lossless)]
#![allow(clippy::doc_markdown)]

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rource_math::Color;

// ============================================================================
// Baseline implementations (current)
// ============================================================================

/// Current from_hex implementation.
#[inline]
fn from_hex_baseline(hex: u32) -> Color {
    Color::new(
        ((hex >> 16) & 0xFF) as f32 / 255.0,
        ((hex >> 8) & 0xFF) as f32 / 255.0,
        (hex & 0xFF) as f32 / 255.0,
        1.0,
    )
}

/// Current from_rgba8 implementation.
#[inline]
fn from_rgba8_baseline(r: u8, g: u8, b: u8, a: u8) -> Color {
    Color::new(
        f32::from(r) / 255.0,
        f32::from(g) / 255.0,
        f32::from(b) / 255.0,
        f32::from(a) / 255.0,
    )
}

/// Current to_argb8 implementation.
#[inline]
fn to_argb8_baseline(c: Color) -> u32 {
    let r = (c.r.clamp(0.0, 1.0) * 255.0).round() as u32;
    let g = (c.g.clamp(0.0, 1.0) * 255.0).round() as u32;
    let b = (c.b.clamp(0.0, 1.0) * 255.0).round() as u32;
    let a = (c.a.clamp(0.0, 1.0) * 255.0).round() as u32;
    (a << 24) | (r << 16) | (g << 8) | b
}

// ============================================================================
// Optimized implementations (lookup table)
// ============================================================================

/// Lookup table for u8 -> f32 conversion (0-255 -> 0.0-1.0).
/// Pre-computed at compile time for deterministic results.
static U8_TO_F32_LUT: [f32; 256] = {
    let mut table = [0.0f32; 256];
    let mut i = 0u32;
    while i < 256 {
        // Use integer division to get exact values
        // i / 255.0 computed at compile time
        table[i as usize] = i as f32 / 255.0;
        i += 1;
    }
    table
};

/// Reciprocal of 255 for fast division.
const INV_255: f32 = 1.0 / 255.0;

/// Optimized from_hex using lookup table.
#[inline]
fn from_hex_lut(hex: u32) -> Color {
    Color::new(
        U8_TO_F32_LUT[((hex >> 16) & 0xFF) as usize],
        U8_TO_F32_LUT[((hex >> 8) & 0xFF) as usize],
        U8_TO_F32_LUT[(hex & 0xFF) as usize],
        1.0,
    )
}

/// Optimized from_rgba8 using lookup table.
#[inline]
fn from_rgba8_lut(r: u8, g: u8, b: u8, a: u8) -> Color {
    Color::new(
        U8_TO_F32_LUT[r as usize],
        U8_TO_F32_LUT[g as usize],
        U8_TO_F32_LUT[b as usize],
        U8_TO_F32_LUT[a as usize],
    )
}

/// Optimized from_hex using reciprocal multiplication.
#[inline]
fn from_hex_reciprocal(hex: u32) -> Color {
    Color::new(
        ((hex >> 16) & 0xFF) as f32 * INV_255,
        ((hex >> 8) & 0xFF) as f32 * INV_255,
        (hex & 0xFF) as f32 * INV_255,
        1.0,
    )
}

/// Optimized from_rgba8 using reciprocal multiplication.
#[inline]
fn from_rgba8_reciprocal(r: u8, g: u8, b: u8, a: u8) -> Color {
    Color::new(
        r as f32 * INV_255,
        g as f32 * INV_255,
        b as f32 * INV_255,
        a as f32 * INV_255,
    )
}

/// Optimized to_argb8 without round() - uses truncation.
/// Note: May differ by ±1 from baseline due to rounding mode.
#[inline]
fn to_argb8_no_round(c: Color) -> u32 {
    // Add 0.5 before truncation to simulate rounding
    let r = ((c.r.clamp(0.0, 1.0) * 255.0) + 0.5) as u32;
    let g = ((c.g.clamp(0.0, 1.0) * 255.0) + 0.5) as u32;
    let b = ((c.b.clamp(0.0, 1.0) * 255.0) + 0.5) as u32;
    let a = ((c.a.clamp(0.0, 1.0) * 255.0) + 0.5) as u32;
    (a << 24) | (r << 16) | (g << 8) | b
}

/// Lookup table for f32 -> u8 conversion (clamped 0.0-1.0 range).
/// Uses 1024 entries for smooth interpolation.
static F32_TO_U8_LUT: [u8; 1025] = {
    let mut table = [0u8; 1025];
    let mut i = 0u32;
    while i <= 1024 {
        // Map 0..1024 to 0..255 with rounding
        let val = (i * 255 + 512) / 1024;
        table[i as usize] = if val > 255 { 255 } else { val as u8 };
        i += 1;
    }
    table
};

/// Optimized to_argb8 using lookup table.
#[inline]
fn to_argb8_lut(c: Color) -> u32 {
    // Scale to 0-1024 range for table lookup
    let r_idx = ((c.r.clamp(0.0, 1.0) * 1024.0) as usize).min(1024);
    let g_idx = ((c.g.clamp(0.0, 1.0) * 1024.0) as usize).min(1024);
    let b_idx = ((c.b.clamp(0.0, 1.0) * 1024.0) as usize).min(1024);
    let a_idx = ((c.a.clamp(0.0, 1.0) * 1024.0) as usize).min(1024);

    let r = F32_TO_U8_LUT[r_idx] as u32;
    let g = F32_TO_U8_LUT[g_idx] as u32;
    let b = F32_TO_U8_LUT[b_idx] as u32;
    let a = F32_TO_U8_LUT[a_idx] as u32;

    (a << 24) | (r << 16) | (g << 8) | b
}

// ============================================================================
// Benchmarks
// ============================================================================

fn bench_from_hex(c: &mut Criterion) {
    let mut group = c.benchmark_group("from_hex");

    let test_colors = [0xFF0000u32, 0x00FF00, 0x0000FF, 0x808080, 0xFFA500];

    group.bench_function("baseline", |b| {
        b.iter(|| {
            let mut sum = 0.0f32;
            for &hex in &test_colors {
                let color = from_hex_baseline(black_box(hex));
                sum += color.r + color.g + color.b;
            }
            black_box(sum)
        });
    });

    group.bench_function("lut", |b| {
        b.iter(|| {
            let mut sum = 0.0f32;
            for &hex in &test_colors {
                let color = from_hex_lut(black_box(hex));
                sum += color.r + color.g + color.b;
            }
            black_box(sum)
        });
    });

    group.bench_function("reciprocal", |b| {
        b.iter(|| {
            let mut sum = 0.0f32;
            for &hex in &test_colors {
                let color = from_hex_reciprocal(black_box(hex));
                sum += color.r + color.g + color.b;
            }
            black_box(sum)
        });
    });

    group.finish();
}

fn bench_from_rgba8(c: &mut Criterion) {
    let mut group = c.benchmark_group("from_rgba8");

    let test_values: [(u8, u8, u8, u8); 5] = [
        (255, 0, 0, 255),
        (0, 255, 0, 128),
        (0, 0, 255, 64),
        (128, 128, 128, 255),
        (255, 165, 0, 200),
    ];

    group.bench_function("baseline", |b| {
        b.iter(|| {
            let mut sum = 0.0f32;
            for &(r, g, b_val, a) in &test_values {
                let color =
                    from_rgba8_baseline(black_box(r), black_box(g), black_box(b_val), black_box(a));
                sum += color.r + color.g + color.b + color.a;
            }
            black_box(sum)
        });
    });

    group.bench_function("lut", |b| {
        b.iter(|| {
            let mut sum = 0.0f32;
            for &(r, g, b_val, a) in &test_values {
                let color =
                    from_rgba8_lut(black_box(r), black_box(g), black_box(b_val), black_box(a));
                sum += color.r + color.g + color.b + color.a;
            }
            black_box(sum)
        });
    });

    group.bench_function("reciprocal", |b| {
        b.iter(|| {
            let mut sum = 0.0f32;
            for &(r, g, b_val, a) in &test_values {
                let color = from_rgba8_reciprocal(
                    black_box(r),
                    black_box(g),
                    black_box(b_val),
                    black_box(a),
                );
                sum += color.r + color.g + color.b + color.a;
            }
            black_box(sum)
        });
    });

    group.finish();
}

fn bench_to_argb8(c: &mut Criterion) {
    let mut group = c.benchmark_group("to_argb8");

    let test_colors = [
        Color::new(1.0, 0.0, 0.0, 1.0),
        Color::new(0.0, 1.0, 0.0, 0.5),
        Color::new(0.0, 0.0, 1.0, 0.25),
        Color::new(0.5, 0.5, 0.5, 1.0),
        Color::new(1.0, 0.647, 0.0, 0.8),
    ];

    group.bench_function("baseline", |b| {
        b.iter(|| {
            let mut sum = 0u32;
            for color in &test_colors {
                sum ^= to_argb8_baseline(black_box(*color));
            }
            black_box(sum)
        });
    });

    group.bench_function("no_round", |b| {
        b.iter(|| {
            let mut sum = 0u32;
            for color in &test_colors {
                sum ^= to_argb8_no_round(black_box(*color));
            }
            black_box(sum)
        });
    });

    group.bench_function("lut", |b| {
        b.iter(|| {
            let mut sum = 0u32;
            for color in &test_colors {
                sum ^= to_argb8_lut(black_box(*color));
            }
            black_box(sum)
        });
    });

    group.finish();
}

fn bench_batch_conversion(c: &mut Criterion) {
    let mut group = c.benchmark_group("batch_conversion");

    // Simulate a realistic workload: 1000 color conversions
    let count = 1000;
    group.throughput(Throughput::Elements(count as u64));

    // Generate test data
    let hex_colors: Vec<u32> = (0..count)
        .map(|i| {
            let r = ((i * 17) % 256) as u32;
            let g = ((i * 31) % 256) as u32;
            let b = ((i * 47) % 256) as u32;
            (r << 16) | (g << 8) | b
        })
        .collect();

    let float_colors: Vec<Color> = (0..count)
        .map(|i| {
            Color::new(
                ((i * 17) % 256) as f32 / 255.0,
                ((i * 31) % 256) as f32 / 255.0,
                ((i * 47) % 256) as f32 / 255.0,
                1.0,
            )
        })
        .collect();

    // from_hex batch
    group.bench_with_input(
        BenchmarkId::new("from_hex_baseline", count),
        &count,
        |b, _| {
            b.iter(|| {
                let mut sum = 0.0f32;
                for &hex in &hex_colors {
                    let c = from_hex_baseline(hex);
                    sum += c.r;
                }
                black_box(sum)
            });
        },
    );

    group.bench_with_input(BenchmarkId::new("from_hex_lut", count), &count, |b, _| {
        b.iter(|| {
            let mut sum = 0.0f32;
            for &hex in &hex_colors {
                let c = from_hex_lut(hex);
                sum += c.r;
            }
            black_box(sum)
        });
    });

    group.bench_with_input(
        BenchmarkId::new("from_hex_reciprocal", count),
        &count,
        |b, _| {
            b.iter(|| {
                let mut sum = 0.0f32;
                for &hex in &hex_colors {
                    let c = from_hex_reciprocal(hex);
                    sum += c.r;
                }
                black_box(sum)
            });
        },
    );

    // to_argb8 batch
    group.bench_with_input(
        BenchmarkId::new("to_argb8_baseline", count),
        &count,
        |b, _| {
            b.iter(|| {
                let mut sum = 0u32;
                for c in &float_colors {
                    sum ^= to_argb8_baseline(*c);
                }
                black_box(sum)
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("to_argb8_no_round", count),
        &count,
        |b, _| {
            b.iter(|| {
                let mut sum = 0u32;
                for c in &float_colors {
                    sum ^= to_argb8_no_round(*c);
                }
                black_box(sum)
            });
        },
    );

    group.finish();
}

/// Verify correctness of optimized implementations.
#[test]
fn test_from_hex_correctness() {
    let test_cases = [
        0x000000u32,
        0xFF0000,
        0x00FF00,
        0x0000FF,
        0xFFFFFF,
        0x808080,
    ];

    for hex in test_cases {
        let baseline = from_hex_baseline(hex);
        let lut = from_hex_lut(hex);
        let recip = from_hex_reciprocal(hex);

        // LUT should be exact
        assert!(
            (baseline.r - lut.r).abs() < 0.0001,
            "LUT r mismatch for {hex:#08X}"
        );
        assert!(
            (baseline.g - lut.g).abs() < 0.0001,
            "LUT g mismatch for {hex:#08X}"
        );
        assert!(
            (baseline.b - lut.b).abs() < 0.0001,
            "LUT b mismatch for {hex:#08X}"
        );

        // Reciprocal should be very close
        assert!(
            (baseline.r - recip.r).abs() < 0.0001,
            "Recip r mismatch for {hex:#08X}"
        );
        assert!(
            (baseline.g - recip.g).abs() < 0.0001,
            "Recip g mismatch for {hex:#08X}"
        );
        assert!(
            (baseline.b - recip.b).abs() < 0.0001,
            "Recip b mismatch for {hex:#08X}"
        );
    }
}

#[test]
fn test_to_argb8_correctness() {
    let test_colors = [
        Color::new(0.0, 0.0, 0.0, 1.0),
        Color::new(1.0, 0.0, 0.0, 1.0),
        Color::new(0.0, 1.0, 0.0, 1.0),
        Color::new(0.0, 0.0, 1.0, 1.0),
        Color::new(1.0, 1.0, 1.0, 1.0),
        Color::new(0.5, 0.5, 0.5, 1.0),
    ];

    for color in test_colors {
        let baseline = to_argb8_baseline(color);
        let no_round = to_argb8_no_round(color);
        let lut = to_argb8_lut(color);

        // Allow ±1 difference due to rounding modes
        let diff_r = ((baseline >> 16) & 0xFF) as i32 - ((no_round >> 16) & 0xFF) as i32;
        let diff_g = ((baseline >> 8) & 0xFF) as i32 - ((no_round >> 8) & 0xFF) as i32;
        let diff_b = (baseline & 0xFF) as i32 - (no_round & 0xFF) as i32;

        assert!(diff_r.abs() <= 1, "no_round r diff too large for {color:?}");
        assert!(diff_g.abs() <= 1, "no_round g diff too large for {color:?}");
        assert!(diff_b.abs() <= 1, "no_round b diff too large for {color:?}");

        let diff_r = ((baseline >> 16) & 0xFF) as i32 - ((lut >> 16) & 0xFF) as i32;
        let diff_g = ((baseline >> 8) & 0xFF) as i32 - ((lut >> 8) & 0xFF) as i32;
        let diff_b = (baseline & 0xFF) as i32 - (lut & 0xFF) as i32;

        assert!(diff_r.abs() <= 1, "LUT r diff too large for {color:?}");
        assert!(diff_g.abs() <= 1, "LUT g diff too large for {color:?}");
        assert!(diff_b.abs() <= 1, "LUT b diff too large for {color:?}");
    }
}

criterion_group!(
    benches,
    bench_from_hex,
    bench_from_rgba8,
    bench_to_argb8,
    bench_batch_conversion,
);
criterion_main!(benches);
