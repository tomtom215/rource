// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Deterministic instruction-count benchmarks using iai-callgrind.
//!
//! These benchmarks measure CPU instructions executed, which is deterministic
//! across runs (unlike wall-clock time). This makes them ideal for CI regression
//! detection where timing variance would cause false positives.
//!
//! Run with: `cargo bench --bench iai_scene`
//! Requires: valgrind installed (Linux only)

// Suppress warnings from macro-generated code
#![allow(missing_docs)]

use iai_callgrind::{library_benchmark, library_benchmark_group, main};
use rource_core::scene::{ActionType, Scene};
use rource_math::{Bounds, Vec2};
use std::fmt::Write;
use std::hint::black_box;
use std::path::{Path, PathBuf};

// ============================================================================
// Setup Functions (not measured)
// ============================================================================

fn create_test_scene(file_count: usize, dir_depth: usize) -> Scene {
    let mut scene = Scene::new();

    // Create files distributed across directory structure
    for i in 0..file_count {
        let depth = i % (dir_depth + 1);
        let dir_index = i / 10;

        let path: PathBuf = if depth == 0 {
            format!("file_{i}.rs").into()
        } else {
            let mut path_str = String::new();
            for d in 0..depth {
                let _ = write!(path_str, "dir_{}/", (dir_index + d) % 50);
            }
            let _ = write!(path_str, "file_{i}.rs");
            path_str.into()
        };

        scene.create_file(&path);
    }

    // Create some users
    for i in 0..50 {
        scene.get_or_create_user(&format!("user_{i}"));
    }

    // Warm up physics (minimal - we want to measure steady state)
    for _ in 0..5 {
        scene.update(1.0 / 60.0);
    }

    scene
}

// ============================================================================
// Scene Update Benchmarks
// ============================================================================

// Benchmark Scene::update() with 100 files - baseline for small repos
#[library_benchmark]
fn bench_scene_update_100() -> u64 {
    let mut scene = create_test_scene(100, 3);
    scene.update(black_box(1.0 / 60.0));
    scene.file_count() as u64
}

// Benchmark Scene::update() with 1000 files - medium repo
#[library_benchmark]
fn bench_scene_update_1000() -> u64 {
    let mut scene = create_test_scene(1000, 5);
    scene.update(black_box(1.0 / 60.0));
    scene.file_count() as u64
}

// Benchmark Scene::update() with 5000 files - large repo (stress test)
#[library_benchmark]
fn bench_scene_update_5000() -> u64 {
    let mut scene = create_test_scene(5000, 6);
    scene.update(black_box(1.0 / 60.0));
    scene.file_count() as u64
}

library_benchmark_group!(
    name = scene_update_group;
    benchmarks = bench_scene_update_100, bench_scene_update_1000, bench_scene_update_5000
);

// ============================================================================
// Spatial Query Benchmarks
// ============================================================================

// Benchmark visible_entities() with 500 files
#[library_benchmark]
fn bench_spatial_query_500() -> usize {
    let mut scene = create_test_scene(500, 4);
    scene.rebuild_spatial_index();
    let bounds = Bounds::new(Vec2::new(-2500.0, -2500.0), Vec2::new(2500.0, 2500.0));
    let (dirs, files, users) = scene.visible_entities(black_box(&bounds));
    dirs.len() + files.len() + users.len()
}

// Benchmark visible_entities() with 2000 files
#[library_benchmark]
fn bench_spatial_query_2000() -> usize {
    let mut scene = create_test_scene(2000, 4);
    scene.rebuild_spatial_index();
    let bounds = Bounds::new(Vec2::new(-2500.0, -2500.0), Vec2::new(2500.0, 2500.0));
    let (dirs, files, users) = scene.visible_entities(black_box(&bounds));
    dirs.len() + files.len() + users.len()
}

// Benchmark visible_entities() with 10000 files - stress test
#[library_benchmark]
fn bench_spatial_query_10000() -> usize {
    let mut scene = create_test_scene(10000, 5);
    scene.rebuild_spatial_index();
    let bounds = Bounds::new(Vec2::new(-2500.0, -2500.0), Vec2::new(2500.0, 2500.0));
    let (dirs, files, users) = scene.visible_entities(black_box(&bounds));
    dirs.len() + files.len() + users.len()
}

library_benchmark_group!(
    name = spatial_query_group;
    benchmarks = bench_spatial_query_500, bench_spatial_query_2000, bench_spatial_query_10000
);

// ============================================================================
// Commit Application Benchmarks
// ============================================================================

fn setup_apply_commit_scene() -> Scene {
    let mut scene = Scene::new();
    for i in 0..500 {
        scene.create_file(&PathBuf::from(format!("src/existing_{i}.rs")));
    }
    scene
}

// Benchmark apply_commit with 10 files per commit
#[library_benchmark]
fn bench_apply_commit_10() -> usize {
    let mut scene = setup_apply_commit_scene();
    let paths: Vec<_> = (0..10)
        .map(|i| {
            let path = if i % 3 == 0 {
                PathBuf::from(format!("src/existing_{}.rs", i % 500))
            } else {
                PathBuf::from(format!("src/new_{i}.rs"))
            };
            let action = if i % 3 == 0 {
                ActionType::Modify
            } else {
                ActionType::Create
            };
            (path, action)
        })
        .collect();
    let files: Vec<(&Path, ActionType)> = paths.iter().map(|(p, a)| (p.as_path(), *a)).collect();
    scene.apply_commit(black_box("author_0"), &files);
    scene.file_count()
}

// Benchmark apply_commit with 50 files per commit
#[library_benchmark]
fn bench_apply_commit_50() -> usize {
    let mut scene = setup_apply_commit_scene();
    let paths: Vec<_> = (0..50)
        .map(|i| {
            let path = if i % 3 == 0 {
                PathBuf::from(format!("src/existing_{}.rs", i % 500))
            } else {
                PathBuf::from(format!("src/new_{i}.rs"))
            };
            let action = if i % 3 == 0 {
                ActionType::Modify
            } else {
                ActionType::Create
            };
            (path, action)
        })
        .collect();
    let files: Vec<(&Path, ActionType)> = paths.iter().map(|(p, a)| (p.as_path(), *a)).collect();
    scene.apply_commit(black_box("author_0"), &files);
    scene.file_count()
}

// Benchmark apply_commit with 100 files per commit - large batch
#[library_benchmark]
fn bench_apply_commit_100() -> usize {
    let mut scene = setup_apply_commit_scene();
    let paths: Vec<_> = (0..100)
        .map(|i| {
            let path = if i % 3 == 0 {
                PathBuf::from(format!("src/existing_{}.rs", i % 500))
            } else {
                PathBuf::from(format!("src/new_{i}.rs"))
            };
            let action = if i % 3 == 0 {
                ActionType::Modify
            } else {
                ActionType::Create
            };
            (path, action)
        })
        .collect();
    let files: Vec<(&Path, ActionType)> = paths.iter().map(|(p, a)| (p.as_path(), *a)).collect();
    scene.apply_commit(black_box("author_0"), &files);
    scene.file_count()
}

library_benchmark_group!(
    name = apply_commit_group;
    benchmarks = bench_apply_commit_10, bench_apply_commit_50, bench_apply_commit_100
);

// ============================================================================
// Spatial Index Rebuild Benchmarks
// ============================================================================

// Benchmark rebuild_spatial_index with 500 entities
#[library_benchmark]
fn bench_rebuild_index_500() {
    let mut scene = create_test_scene(500, 4);
    scene.rebuild_spatial_index();
}

// Benchmark rebuild_spatial_index with 2000 entities
#[library_benchmark]
fn bench_rebuild_index_2000() {
    let mut scene = create_test_scene(2000, 4);
    scene.rebuild_spatial_index();
}

// Benchmark rebuild_spatial_index with 10000 entities - stress test
#[library_benchmark]
fn bench_rebuild_index_10000() {
    let mut scene = create_test_scene(10000, 5);
    scene.rebuild_spatial_index();
}

library_benchmark_group!(
    name = rebuild_index_group;
    benchmarks = bench_rebuild_index_500, bench_rebuild_index_2000, bench_rebuild_index_10000
);

// ============================================================================
// Extension Stats Benchmarks
// ============================================================================

// Benchmark file_extension_stats with 500 files (uncached)
#[library_benchmark]
fn bench_extension_stats_500() -> usize {
    let mut scene = create_test_scene(500, 4);
    scene.invalidate_extension_stats();
    scene.file_extension_stats().len()
}

// Benchmark file_extension_stats with 2000 files (uncached)
#[library_benchmark]
fn bench_extension_stats_2000() -> usize {
    let mut scene = create_test_scene(2000, 4);
    scene.invalidate_extension_stats();
    scene.file_extension_stats().len()
}

library_benchmark_group!(
    name = extension_stats_group;
    benchmarks = bench_extension_stats_500, bench_extension_stats_2000
);

// ============================================================================
// Main
// ============================================================================

main!(
    library_benchmark_groups = scene_update_group,
    spatial_query_group,
    apply_commit_group,
    rebuild_index_group,
    extension_stats_group
);
