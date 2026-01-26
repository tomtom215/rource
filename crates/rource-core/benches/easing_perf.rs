// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Easing function performance benchmarks.
//!
//! These benchmarks measure the performance of easing functions which are
//! called frequently during animations (every frame for active tweens).

#![allow(missing_docs)]
#![allow(clippy::doc_markdown)]

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rource_core::animation::{ease, Easing};
use std::hint::black_box;

// ============================================================================
// Baseline implementations using powi() for comparison
// ============================================================================

/// Baseline QuadInOut using powi(2)
#[inline]
fn quad_in_out_baseline(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    if t < 0.5 {
        2.0 * t * t
    } else {
        1.0 - (-2.0 * t + 2.0).powi(2) * 0.5
    }
}

/// Optimized QuadInOut using direct multiplication
#[inline]
fn quad_in_out_optimized(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    if t < 0.5 {
        2.0 * t * t
    } else {
        let u = -2.0 * t + 2.0;
        1.0 - (u * u) * 0.5
    }
}

/// Baseline CubicOut using powi(3)
#[inline]
fn cubic_out_baseline(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    1.0 - (1.0 - t).powi(3)
}

/// Optimized CubicOut using direct multiplication
#[inline]
fn cubic_out_optimized(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    let u = 1.0 - t;
    1.0 - u * u * u
}

/// Baseline QuartOut using powi(4)
#[inline]
fn quart_out_baseline(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    1.0 - (1.0 - t).powi(4)
}

/// Optimized QuartOut using direct multiplication
#[inline]
fn quart_out_optimized(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    let u = 1.0 - t;
    let u2 = u * u;
    1.0 - u2 * u2
}

/// Baseline QuintOut using powi(5)
#[inline]
fn quint_out_baseline(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    1.0 - (1.0 - t).powi(5)
}

/// Optimized QuintOut using direct multiplication
#[inline]
fn quint_out_optimized(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    let u = 1.0 - t;
    let u2 = u * u;
    1.0 - u2 * u2 * u
}

// ============================================================================
// Benchmarks
// ============================================================================

fn benchmark_individual_easings(c: &mut Criterion) {
    let mut group = c.benchmark_group("easing_powi_vs_multiply");

    // Test at various t values
    let t_values = [0.25f32, 0.5, 0.75];

    for t in t_values {
        // QuadInOut
        group.bench_with_input(
            BenchmarkId::new("quad_in_out/baseline", format!("t={t}")),
            &t,
            |b, &t| b.iter(|| quad_in_out_baseline(black_box(t))),
        );
        group.bench_with_input(
            BenchmarkId::new("quad_in_out/optimized", format!("t={t}")),
            &t,
            |b, &t| b.iter(|| quad_in_out_optimized(black_box(t))),
        );

        // CubicOut
        group.bench_with_input(
            BenchmarkId::new("cubic_out/baseline", format!("t={t}")),
            &t,
            |b, &t| b.iter(|| cubic_out_baseline(black_box(t))),
        );
        group.bench_with_input(
            BenchmarkId::new("cubic_out/optimized", format!("t={t}")),
            &t,
            |b, &t| b.iter(|| cubic_out_optimized(black_box(t))),
        );

        // QuartOut
        group.bench_with_input(
            BenchmarkId::new("quart_out/baseline", format!("t={t}")),
            &t,
            |b, &t| b.iter(|| quart_out_baseline(black_box(t))),
        );
        group.bench_with_input(
            BenchmarkId::new("quart_out/optimized", format!("t={t}")),
            &t,
            |b, &t| b.iter(|| quart_out_optimized(black_box(t))),
        );

        // QuintOut
        group.bench_with_input(
            BenchmarkId::new("quint_out/baseline", format!("t={t}")),
            &t,
            |b, &t| b.iter(|| quint_out_baseline(black_box(t))),
        );
        group.bench_with_input(
            BenchmarkId::new("quint_out/optimized", format!("t={t}")),
            &t,
            |b, &t| b.iter(|| quint_out_optimized(black_box(t))),
        );
    }

    group.finish();
}

fn benchmark_easing_batch(c: &mut Criterion) {
    let mut group = c.benchmark_group("easing_batch");
    group.throughput(Throughput::Elements(1000));

    // Simulate 1000 tween updates (typical animation scenario)
    let t_values: Vec<f32> = (0..1000).map(|i| (i as f32) / 1000.0).collect();

    // Most commonly used easings
    let easings = [
        ("Linear", Easing::Linear),
        ("QuadOut", Easing::QuadOut),
        ("QuadInOut", Easing::QuadInOut),
        ("CubicOut", Easing::CubicOut),
        ("QuartOut", Easing::QuartOut),
        ("QuintOut", Easing::QuintOut),
    ];

    for (name, easing) in easings {
        group.bench_function(name, |b| {
            b.iter(|| {
                let mut sum = 0.0f32;
                for &t in &t_values {
                    sum += ease(black_box(t), easing);
                }
                sum
            });
        });
    }

    group.finish();
}

fn benchmark_production_animation(c: &mut Criterion) {
    let mut group = c.benchmark_group("production_animation");

    // Simulate a typical frame with multiple active tweens
    // Each tween computes eased progress once per frame
    let tween_count = 50; // Typical: ~50 active tweens (files fading, users moving, etc.)
    let frames = 60; // One second at 60fps

    group.throughput(Throughput::Elements((tween_count * frames) as u64));

    // Generate random-ish t values representing tween progress
    let t_values: Vec<f32> = (0..tween_count * frames)
        .map(|i| ((i as f32 * 0.0137).sin() * 0.5 + 0.5).clamp(0.0, 1.0))
        .collect();

    group.bench_function("QuadOut_production", |b| {
        b.iter(|| {
            let mut sum = 0.0f32;
            for &t in &t_values {
                sum += ease(black_box(t), Easing::QuadOut);
            }
            sum
        });
    });

    group.bench_function("CubicInOut_production", |b| {
        b.iter(|| {
            let mut sum = 0.0f32;
            for &t in &t_values {
                sum += ease(black_box(t), Easing::CubicInOut);
            }
            sum
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    benchmark_individual_easings,
    benchmark_easing_batch,
    benchmark_production_animation
);
criterion_main!(benches);
