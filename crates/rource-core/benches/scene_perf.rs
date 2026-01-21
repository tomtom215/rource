//! Performance benchmarks for Scene operations.
//!
//! These benchmarks measure the performance of critical scene operations
//! to establish baselines and verify optimizations.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rource_core::scene::{ActionType, Scene};
use std::path::PathBuf;

/// Creates a scene with the specified number of files distributed across directories.
fn create_test_scene(file_count: usize, dir_depth: usize) -> Scene {
    let mut scene = Scene::new();

    // Create files distributed across directory structure
    for i in 0..file_count {
        // Create varied directory depths
        let depth = i % (dir_depth + 1);
        let dir_index = i / 10; // Group files into directories

        let path: PathBuf = if depth == 0 {
            format!("file_{i}.rs").into()
        } else {
            let mut path_str = String::new();
            for d in 0..depth {
                path_str.push_str(&format!("dir_{}/", (dir_index + d) % 50));
            }
            path_str.push_str(&format!("file_{i}.rs"));
            path_str.into()
        };

        scene.create_file(&path);
    }

    // Create some users
    for i in 0..50 {
        scene.get_or_create_user(&format!("user_{i}"));
    }

    // Warm up physics
    for _ in 0..10 {
        scene.update(1.0 / 60.0);
    }

    scene
}

/// Benchmarks Scene::update() which is called every frame.
fn bench_scene_update(c: &mut Criterion) {
    let mut group = c.benchmark_group("scene_update");

    for file_count in [100, 500, 1000, 5000] {
        group.throughput(Throughput::Elements(1)); // 1 frame

        group.bench_with_input(
            BenchmarkId::new("files", file_count),
            &file_count,
            |b, &count| {
                let mut scene = create_test_scene(count, 5);
                b.iter(|| {
                    scene.update(black_box(1.0 / 60.0));
                });
            },
        );
    }

    group.finish();
}

/// Benchmarks the force-directed layout calculations.
fn bench_force_layout(c: &mut Criterion) {
    let mut group = c.benchmark_group("force_layout");

    // This measures just the update portion with varying directory counts
    for dir_count in [10, 50, 100, 200] {
        group.throughput(Throughput::Elements(dir_count as u64));

        group.bench_with_input(
            BenchmarkId::new("directories", dir_count),
            &dir_count,
            |b, &count| {
                // Create scene with directories (each file creates parent dirs)
                let file_count = count * 5; // ~5 files per directory
                let mut scene = create_test_scene(file_count, 3);

                // Warm up
                for _ in 0..5 {
                    scene.update(1.0 / 60.0);
                }

                b.iter(|| {
                    scene.update(black_box(1.0 / 60.0));
                });
            },
        );
    }

    group.finish();
}

/// Benchmarks visible_entities() spatial queries.
fn bench_spatial_query(c: &mut Criterion) {
    use rource_math::{Bounds, Vec2};

    let mut group = c.benchmark_group("spatial_query");

    for file_count in [500, 2000, 10000] {
        group.throughput(Throughput::Elements(1)); // 1 query

        group.bench_with_input(
            BenchmarkId::new("files", file_count),
            &file_count,
            |b, &count| {
                let mut scene = create_test_scene(count, 4);
                scene.rebuild_spatial_index();

                // Query bounds covering ~25% of scene
                let bounds = Bounds::new(Vec2::new(-2500.0, -2500.0), Vec2::new(2500.0, 2500.0));

                b.iter(|| {
                    let (dirs, files, users) = scene.visible_entities(black_box(&bounds));
                    black_box((dirs, files, users))
                });
            },
        );
    }

    group.finish();
}

/// Benchmarks file_extension_stats() which computes legend data.
fn bench_extension_stats(c: &mut Criterion) {
    let mut group = c.benchmark_group("extension_stats");

    for file_count in [100, 500, 2000] {
        group.throughput(Throughput::Elements(file_count as u64));

        group.bench_with_input(
            BenchmarkId::new("files", file_count),
            &file_count,
            |b, &count| {
                let mut scene = create_test_scene(count, 4);

                b.iter(|| {
                    // Force cache invalidation to measure actual computation cost
                    scene.invalidate_extension_stats();
                    let stats = scene.file_extension_stats();
                    // Return the length to avoid lifetime issues while still using the result
                    black_box(stats.len())
                });
            },
        );
    }

    group.finish();
}

/// Benchmarks cached file_extension_stats() to show cache benefit.
fn bench_extension_stats_cached(c: &mut Criterion) {
    let mut group = c.benchmark_group("extension_stats_cached");

    for file_count in [100, 500, 2000] {
        group.throughput(Throughput::Elements(file_count as u64));

        group.bench_with_input(
            BenchmarkId::new("files", file_count),
            &file_count,
            |b, &count| {
                let mut scene = create_test_scene(count, 4);
                // Prime the cache
                let _ = scene.file_extension_stats();

                b.iter(|| {
                    // This should hit the cache most of the time
                    let stats = scene.file_extension_stats();
                    // Return the length to avoid lifetime issues while still using the result
                    black_box(stats.len())
                });
            },
        );
    }

    group.finish();
}

/// Benchmarks apply_commit() which processes VCS data.
fn bench_apply_commit(c: &mut Criterion) {
    let mut group = c.benchmark_group("apply_commit");

    for batch_size in [1, 10, 50, 100] {
        group.throughput(Throughput::Elements(batch_size as u64));

        group.bench_with_input(
            BenchmarkId::new("files_per_commit", batch_size),
            &batch_size,
            |b, &size| {
                let mut scene = Scene::new();

                // Pre-create some files to have a mix of creates and modifies
                for i in 0..500 {
                    scene.create_file(&PathBuf::from(format!("src/existing_{i}.rs")));
                }

                let mut commit_num = 0;
                b.iter(|| {
                    let files: Vec<_> = (0..size)
                        .map(|i| {
                            let path = if i % 3 == 0 {
                                // Modify existing
                                PathBuf::from(format!("src/existing_{}.rs", i % 500))
                            } else {
                                // Create new
                                PathBuf::from(format!("src/new_{}_{i}.rs", commit_num))
                            };
                            let action = if i % 3 == 0 {
                                ActionType::Modify
                            } else {
                                ActionType::Create
                            };
                            (path, action)
                        })
                        .collect();

                    scene.apply_commit(black_box(&format!("author_{}", commit_num % 50)), &files);
                    commit_num += 1;
                });
            },
        );
    }

    group.finish();
}

/// Benchmarks rebuild_spatial_index() which is called periodically.
fn bench_rebuild_spatial_index(c: &mut Criterion) {
    let mut group = c.benchmark_group("rebuild_spatial_index");

    for file_count in [500, 2000, 10000] {
        group.throughput(Throughput::Elements(file_count as u64));

        group.bench_with_input(
            BenchmarkId::new("entities", file_count),
            &file_count,
            |b, &count| {
                let mut scene = create_test_scene(count, 4);

                b.iter(|| {
                    scene.rebuild_spatial_index();
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_scene_update,
    bench_force_layout,
    bench_spatial_query,
    bench_extension_stats,
    bench_extension_stats_cached,
    bench_apply_commit,
    bench_rebuild_spatial_index,
);

criterion_main!(benches);
