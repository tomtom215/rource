// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Performance benchmark tests for `render_phases` module.
//!
//! These tests measure the performance impact of label collision detection
//! and beam limiting. They use `std::time::Instant` for timing.
//!
//! Run with: cargo test -p rource-wasm bench_ --release -- --nocapture

use rource_math::Vec2;

use crate::render_phases::estimate_text_width;
use crate::render_phases::helpers::compute_file_effective_radius;
use crate::render_phases::label_placer::LabelPlacer;

#[test]
fn bench_label_placer_new() {
    use std::time::Instant;

    const ITERATIONS: u32 = 10_000;
    let start = Instant::now();

    for _ in 0..ITERATIONS {
        let _ = std::hint::black_box(LabelPlacer::new(1.0));
    }

    let elapsed = start.elapsed();
    let per_op = elapsed.as_nanos() / u128::from(ITERATIONS);
    println!("\nLabelPlacer::new(): {ITERATIONS} iterations in {elapsed:?} ({per_op} ns/op)");

    // Note: LabelPlacer::new() is a ONE-TIME startup cost, not per-frame.
    // The per-frame cost is reset() which is ~250ns.
    // Assertion: creation should be < 150µs (150,000 ns) - acceptable startup cost
    // (Relaxed from 50µs→100µs→150µs to account for CI runner variability,
    // especially Windows runners which measured 113µs in CI)
    assert!(
        per_op < 150_000,
        "LabelPlacer::new() too slow: {per_op} ns/op (one-time startup cost, limit: 150µs)"
    );
}

#[test]
fn bench_label_placer_reset() {
    use std::time::Instant;

    const ITERATIONS: u32 = 100_000;
    let mut placer = LabelPlacer::new(1.0);

    // Pre-populate with some labels to make reset realistic
    for i in 0..50 {
        placer.try_place(Vec2::new(i as f32 * 100.0, 0.0), 50.0, 20.0);
    }

    let start = Instant::now();

    for _ in 0..ITERATIONS {
        placer.reset(1.0);
        // Add a label to make reset non-trivial
        placer.try_place(Vec2::new(0.0, 0.0), 50.0, 20.0);
    }

    let elapsed = start.elapsed();
    let per_op = elapsed.as_nanos() / u128::from(ITERATIONS);
    println!("\nLabelPlacer::reset(): {ITERATIONS} iterations in {elapsed:?} ({per_op} ns/op)");

    // Assertion: reset should be < 2µs (2,000 ns)
    // (Relaxed from 1µs to account for CI runner variability - CI measured 1041ns)
    assert!(
        per_op < 2_000,
        "LabelPlacer::reset() too slow: {per_op} ns/op"
    );
}

#[test]
fn bench_label_placer_try_place() {
    use std::time::Instant;

    const ITERATIONS: u32 = 100_000;
    let mut placer = LabelPlacer::new(1.0);

    let start = Instant::now();

    for i in 0..ITERATIONS {
        // Spread labels across grid to avoid collision checks
        let x = (i % 100) as f32 * 60.0;
        let y = (i / 100) as f32 * 30.0;
        placer.try_place(Vec2::new(x, y), 50.0, 20.0);

        // Reset periodically to avoid filling up
        if i % 1000 == 999 {
            placer.reset(1.0);
        }
    }

    let elapsed = start.elapsed();
    let per_op = elapsed.as_nanos() / u128::from(ITERATIONS);
    println!("\nLabelPlacer::try_place() (no collision): {ITERATIONS} iterations in {elapsed:?} ({per_op} ns/op)");

    // Assertion: try_place should be < 500ns
    assert!(
        per_op < 500,
        "LabelPlacer::try_place() too slow: {per_op} ns/op"
    );
}

#[test]
fn bench_label_placer_try_place_with_fallback() {
    use std::time::Instant;

    const ITERATIONS: u32 = 50_000;
    let mut placer = LabelPlacer::new(1.0);

    // Pre-populate with labels to force fallback checks
    for i in 0..20 {
        placer.try_place(Vec2::new(i as f32 * 60.0, 0.0), 50.0, 20.0);
    }

    let start = Instant::now();

    for i in 0..ITERATIONS {
        let x = (i % 20) as f32 * 60.0;
        let _ = placer.try_place_with_fallback(
            Vec2::new(x, 0.0), // Will collide with existing
            50.0,
            20.0,
            Vec2::new(x, 25.0),
            5.0,
        );

        if i % 500 == 499 {
            placer.reset(1.0);
            for j in 0..20 {
                placer.try_place(Vec2::new(j as f32 * 60.0, 0.0), 50.0, 20.0);
            }
        }
    }

    let elapsed = start.elapsed();
    let per_op = elapsed.as_nanos() / u128::from(ITERATIONS);
    println!("\nLabelPlacer::try_place_with_fallback(): {ITERATIONS} iterations in {elapsed:?} ({per_op} ns/op)");

    // Assertion: try_place_with_fallback should be < 2µs (may need 4 collision checks)
    assert!(
        per_op < 2_000,
        "LabelPlacer::try_place_with_fallback() too slow: {per_op} ns/op"
    );
}

#[test]
fn bench_beam_sorting() {
    use std::time::Instant;

    const ITERATIONS: u32 = 10_000;

    // Simulate 100 active actions with progress values
    let actions: Vec<(usize, f32)> = (0..100).map(|i| (i, (i as f32) / 100.0)).collect();

    let start = Instant::now();

    for _ in 0..ITERATIONS {
        let mut active = actions.clone();
        active.sort_unstable_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));
        let _limited: Vec<_> = std::hint::black_box(active.into_iter().take(15).collect());
    }

    let elapsed = start.elapsed();
    let per_op = elapsed.as_nanos() / u128::from(ITERATIONS);
    println!("\nBeam sorting (100 actions, take 15): {ITERATIONS} iterations in {elapsed:?} ({per_op} ns/op)");

    // Assertion: sorting 100 items should be < 5µs
    assert!(per_op < 5_000, "Beam sorting too slow: {per_op} ns/op");
}

#[test]
fn bench_user_label_sorting() {
    use std::time::Instant;

    const ITERATIONS: u32 = 10_000;

    // Simulate 50 user candidates with priority values
    let candidates: Vec<(usize, Vec2, f32, f32, f32)> = (0..50)
        .map(|i| (i, Vec2::new(i as f32 * 10.0, 0.0), 5.0, 1.0, i as f32))
        .collect();

    let start = Instant::now();

    for _ in 0..ITERATIONS {
        let mut users = candidates.clone();
        // Sort by priority (last field) descending
        users.sort_unstable_by(|a, b| b.4.partial_cmp(&a.4).unwrap_or(std::cmp::Ordering::Equal));
        let _ = std::hint::black_box(users);
    }

    let elapsed = start.elapsed();
    let per_op = elapsed.as_nanos() / u128::from(ITERATIONS);
    println!(
        "\nUser label sorting (50 users): {ITERATIONS} iterations in {elapsed:?} ({per_op} ns/op)"
    );

    // Assertion: sorting 50 items should be < 3µs
    assert!(
        per_op < 3_000,
        "User label sorting too slow: {per_op} ns/op"
    );
}

#[test]
fn bench_full_label_placement_scenario() {
    use std::time::Instant;

    const ITERATIONS: u32 = 1_000;

    // Simulate realistic scenario: 30 user labels + 50 file labels per frame
    let start = Instant::now();

    for _ in 0..ITERATIONS {
        let mut placer = LabelPlacer::new(1.0);

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
    }

    let elapsed = start.elapsed();
    let per_frame = elapsed.as_micros() / u128::from(ITERATIONS);
    println!("\nFull label placement (30 users + 50 files): {ITERATIONS} frames in {elapsed:?} ({per_frame} µs/frame)");

    // Assertion: full frame should be < 500µs (well within 16.67ms budget)
    // Relaxed from 250µs: Windows CI runners are significantly slower than
    // Linux/macOS (274µs observed on windows-latest vs ~80µs on Linux)
    assert!(
        per_frame < 500,
        "Full label placement too slow: {per_frame} µs/frame"
    );

    // Note: 500µs is 3% of a 16.67ms frame budget at 60fps
    // This is acceptable overhead for collision-free labels
}

#[test]
fn bench_estimate_text_width() {
    use std::time::Instant;

    const ITERATIONS: u32 = 1_000_000;

    // Test with ASCII strings (most common case)
    let ascii_strings = [
        "main.rs",
        "README.md",
        "src/lib.rs",
        "tests/integration_test.rs",
        "package.json",
    ];

    // Test with UTF-8 strings
    let utf8_strings = [
        "über_config.json",
        "日本語ファイル.txt",
        "файл.rs",
        "María García",
        "田中太郎",
    ];

    let size = 12.0;
    let total_ascii = u128::from(ITERATIONS) * ascii_strings.len() as u128;
    let total_utf8 = u128::from(ITERATIONS) * utf8_strings.len() as u128;

    // Benchmark ASCII
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        for s in &ascii_strings {
            let _ = std::hint::black_box(estimate_text_width(s, size));
        }
    }
    let ascii_elapsed = start.elapsed();
    let ascii_per_call_ps = (ascii_elapsed.as_nanos() * 1000) / total_ascii; // picoseconds

    // Benchmark UTF-8
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        for s in &utf8_strings {
            let _ = std::hint::black_box(estimate_text_width(s, size));
        }
    }
    let utf8_elapsed = start.elapsed();
    let utf8_per_call_ps = (utf8_elapsed.as_nanos() * 1000) / total_utf8; // picoseconds

    println!("\nestimate_text_width (Phase 68: chars.count() × 0.62):");
    println!(
        "  ASCII ({} calls): {:.1} ps/call ({:.2} ns/call)",
        total_ascii,
        ascii_per_call_ps,
        ascii_per_call_ps as f64 / 1000.0
    );
    println!(
        "  UTF-8 ({} calls): {:.1} ps/call ({:.2} ns/call)",
        total_utf8,
        utf8_per_call_ps,
        utf8_per_call_ps as f64 / 1000.0
    );
    println!("  Total time: ASCII={ascii_elapsed:?}, UTF-8={utf8_elapsed:?}");

    // Assertion: should be < 50ns per call even with UTF-8 (chars().count() is O(n))
    assert!(
        utf8_per_call_ps < 50_000, // 50ns in picoseconds
        "estimate_text_width too slow: {utf8_per_call_ps} ps/call"
    );
}

/// Benchmark for Phase 70 glow rendering optimization.
///
/// Measures the theoretical improvement from:
/// 1. LOD culling (skip glow when `effective_radius` < 3.0)
/// 2. Reduced glow radius (2.0x -> 1.5x = 43.75% fewer pixels)
///
/// Run with: `cargo test -p rource-wasm bench_glow --release -- --nocapture`
#[test]
fn bench_glow_lod_culling() {
    use std::time::Instant;

    const ITERATIONS: u32 = 100_000;

    // Simulate decision logic for glow rendering
    // This measures the overhead of the LOD culling check itself

    // Scenario: 1000 files with various radii (realistic distribution)
    // Radii range from 1.0 to 10.0, with uniform distribution across file indices
    let file_radii: Vec<f32> = (0..1000)
        .map(|i| {
            // Use prime-based mixing to decorrelate radius from index
            let base = ((i * 7 + 3) % 10) as f32 + 1.0; // 1.0 to 10.0
            compute_file_effective_radius(base)
        })
        .collect();

    // 5% of files are touched, distributed uniformly
    let touch_states: Vec<bool> = (0..1000).map(|i| i % 20 == 0).collect();

    // Measure decision overhead for Phase 70 condition
    let start = Instant::now();
    let mut glow_count = 0u32;
    for _ in 0..ITERATIONS {
        for i in 0..file_radii.len() {
            let is_touched = touch_states[i];
            let effective_radius = file_radii[i];

            // Phase 70 condition
            if is_touched && effective_radius >= 3.0 {
                glow_count += 1;
            }
        }
    }
    let elapsed = start.elapsed();
    let total_decisions = u128::from(ITERATIONS) * 1000;
    let ns_per_decision = elapsed.as_nanos() / total_decisions;

    // Count how many glows would be rendered vs skipped
    let files_touched = touch_states.iter().filter(|&&t| t).count();
    let files_large_enough = file_radii.iter().filter(|&&r| r >= 3.0).count();
    let files_both = file_radii
        .iter()
        .zip(touch_states.iter())
        .filter(|&(&r, &t)| t && r >= 3.0)
        .count();

    let touched_skip_pct = if files_touched > 0 {
        100.0 - (files_both as f64 / files_touched as f64 * 100.0)
    } else {
        0.0
    };

    // Area reduction from 2.0x to 1.5x
    let old_area_multiplier = 4.0_f64; // 2.0^2
    let new_area_multiplier = 2.25_f64; // 1.5^2
    let area_reduction_pct = (1.0 - new_area_multiplier / old_area_multiplier) * 100.0;

    println!("\nPhase 70 Glow LOD Culling Benchmark:");
    println!("  Files tested: 1000 (5% touched = {files_touched})");
    println!("  Files with effective_radius >= 3.0: {files_large_enough}");
    println!("  Files rendering glow (touched AND large): {files_both}");
    println!("  LOD culling saves: {touched_skip_pct:.1}% of touched file glows");
    println!("  Decision overhead: {ns_per_decision} ns/file (negligible)");
    println!("  Glow count (sanity check): {glow_count}");
    println!("  Glow area reduction (radius 2.0x->1.5x): {area_reduction_pct:.2}%");

    // Decision overhead should be < 1ns (just a comparison)
    assert!(
        ns_per_decision < 5,
        "LOD culling decision overhead too high: {ns_per_decision} ns"
    );
}

/// Phase 84: Comparative benchmark — `format!()` JSON vs. zero-copy buffer writes.
///
/// Measures Rust-side cost only. Uses floating-point division for precise ns/op
/// to avoid integer truncation artifacts in speedup calculation.
#[test]
#[allow(clippy::too_many_lines)]
fn bench_stats_buffer_vs_json() {
    use crate::wasm_api::stats::format_frame_stats;
    use std::time::Instant;

    const ITERATIONS: u32 = 100_000;

    // Representative values (same across both paths for fair comparison)
    let fps: f64 = 60.0;
    let frame_time_ms: f64 = 16.67;
    let total_entities: usize = 1500;
    let visible_files: usize = 200;
    let visible_users: usize = 5;
    let visible_directories: usize = 50;
    let active_actions: usize = 10;
    let draw_calls: usize = 6;
    let width: u32 = 1920;
    let height: u32 = 1080;
    let is_playing = true;
    let commit_count: usize = 5432;
    let current_commit: usize = 2716;
    let total_files: usize = 1200;
    let total_users: usize = 45;
    let total_dirs: usize = 350;

    // ---- Benchmark 1: format!() JSON serialization (current legacy path) ----
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let json = std::hint::black_box(format_frame_stats(
            fps,
            frame_time_ms,
            total_entities,
            visible_files,
            visible_users,
            visible_directories,
            active_actions,
            draw_calls,
            width,
            height,
            is_playing,
            commit_count,
            current_commit,
            total_files,
            total_users,
            total_dirs,
        ));
        std::hint::black_box(&json);
    }
    let json_elapsed = start.elapsed();
    let json_ns_total = json_elapsed.as_nanos();
    let json_ns_per_op = json_ns_total as f64 / f64::from(ITERATIONS);

    // ---- Benchmark 2: Buffer writes (zero-copy path) ----
    let mut buffer = [0.0_f32; 32];
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        buffer[0] = fps as f32;
        buffer[1] = frame_time_ms as f32;
        buffer[2] = total_entities as f32;
        buffer[3] = visible_files as f32;
        buffer[4] = visible_users as f32;
        buffer[5] = visible_directories as f32;
        buffer[6] = active_actions as f32;
        buffer[7] = draw_calls as f32;
        buffer[8] = width as f32;
        buffer[9] = height as f32;
        buffer[10] = if is_playing { 1.0 } else { 0.0 };
        buffer[11] = commit_count as f32;
        buffer[12] = current_commit as f32;
        buffer[13] = total_files as f32;
        buffer[14] = total_users as f32;
        buffer[15] = total_dirs as f32;
        buffer[16] = 500.0; // mouse_x
        buffer[17] = 300.0; // mouse_y
        buffer[18] = 250.0; // world_x
        buffer[19] = 150.0; // world_y
        std::hint::black_box(&buffer);
    }
    let buffer_elapsed = start.elapsed();
    let buffer_ns_total = buffer_elapsed.as_nanos();
    let buffer_ns_per_op = buffer_ns_total as f64 / f64::from(ITERATIONS);

    // Calculate improvement using floating-point values (no truncation artifacts)
    let speedup = json_ns_per_op / buffer_ns_per_op;
    let reduction_pct = (1.0 - buffer_ns_per_op / json_ns_per_op) * 100.0;

    println!(
        "\nPhase 84: Stats Buffer vs JSON Serialization ({ITERATIONS} iterations, f64 precision):"
    );
    println!("  format!() JSON:    {json_ns_per_op:.2} ns/op ({json_elapsed:?} total)");
    println!("  Buffer writes:     {buffer_ns_per_op:.2} ns/op ({buffer_elapsed:?} total)");
    println!("  Speedup:           {speedup:.1}x");
    println!("  Reduction:         {reduction_pct:.2}%");
    println!();
    println!("  Note: Measures Rust-side cost only.");
    println!("  JS-side additionally eliminates JSON.parse() overhead.");

    // Assertions:
    // 1. Buffer writes must be faster than JSON serialization
    assert!(
        buffer_ns_per_op < json_ns_per_op,
        "Buffer writes ({buffer_ns_per_op:.2} ns) should be faster than JSON ({json_ns_per_op:.2} ns)"
    );

    // 2. Speedup must be at least 50x (conservative; measured ~500x)
    assert!(
        speedup >= 50.0,
        "Expected at least 50x speedup, got {speedup:.1}x"
    );
}
