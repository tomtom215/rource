// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Full-frame benchmark: measures every render phase individually and in total.
//!
//! Uses a no-op renderer to isolate CPU-side rendering logic cost from GPU work.
//! Creates a realistic scene (50 dirs, 200 files, 5 users, 10 actions) and
//! benchmarks each phase to identify bottlenecks toward the 2-5 µs target.
//!
//! Run with: `cargo test -p rource-wasm bench_full_frame --release -- --nocapture`

use std::path::Path;
use std::time::Instant;

use rource_core::config::WatermarkSettings;
use rource_core::scene::ActionType;
use rource_core::{Camera, Scene};
use rource_math::{Bounds, Color, Mat4, Vec2};
use rource_render::{FontId, Renderer, TextureId};

use crate::render_phases::label_placer::LabelPlacer;
use crate::render_phases::{
    render_actions, render_directories, render_directory_labels, render_file_labels, render_files,
    render_user_labels, render_users, render_watermark, RenderContext,
};

// =============================================================================
// No-Op Renderer (measures CPU overhead only, zero GPU cost)
// =============================================================================

/// A no-op renderer that counts draw calls but does zero work.
/// This isolates CPU-side render logic cost from actual GPU rendering.
struct NoOpRenderer {
    draw_calls: u32,
}

impl NoOpRenderer {
    fn new() -> Self {
        Self { draw_calls: 0 }
    }

    fn reset(&mut self) {
        self.draw_calls = 0;
    }

    fn draw_calls(&self) -> u32 {
        self.draw_calls
    }
}

impl Renderer for NoOpRenderer {
    fn begin_frame(&mut self) {}
    fn end_frame(&mut self) {}
    fn clear(&mut self, _color: Color) {}

    fn draw_circle(&mut self, _center: Vec2, _radius: f32, _width: f32, _color: Color) {
        self.draw_calls += 1;
    }

    fn draw_disc(&mut self, _center: Vec2, _radius: f32, _color: Color) {
        self.draw_calls += 1;
    }

    fn draw_line(&mut self, _start: Vec2, _end: Vec2, _width: f32, _color: Color) {
        self.draw_calls += 1;
    }

    fn draw_spline(&mut self, _points: &[Vec2], _width: f32, _color: Color) {
        self.draw_calls += 1;
    }

    fn draw_quad(&mut self, _bounds: Bounds, _texture: Option<TextureId>, _color: Color) {
        self.draw_calls += 1;
    }

    fn draw_text(
        &mut self,
        _text: &str,
        _position: Vec2,
        _font: FontId,
        _size: f32,
        _color: Color,
    ) {
        self.draw_calls += 1;
    }

    fn set_transform(&mut self, _transform: Mat4) {}
    fn transform(&self) -> Mat4 {
        Mat4::IDENTITY
    }
    fn push_clip(&mut self, _bounds: Bounds) {}
    fn pop_clip(&mut self) {}
    fn resize(&mut self, _width: u32, _height: u32) {}
    fn width(&self) -> u32 {
        1920
    }
    fn height(&self) -> u32 {
        1080
    }
    fn load_texture(&mut self, _width: u32, _height: u32, _data: &[u8]) -> TextureId {
        TextureId::new(0)
    }
    fn unload_texture(&mut self, _texture: TextureId) {}
    fn load_font(&mut self, _data: &[u8]) -> Option<FontId> {
        Some(FontId::new(0))
    }
}

// =============================================================================
// Test Scene Builder
// =============================================================================

/// Creates a realistic test scene for benchmarking.
///
/// - ~50 directories (from file paths with depth 1-4)
/// - 200 files spread across directories
/// - 5 users
/// - 10 active actions (user→file modifications)
///
/// Scene is warmed up with 30 physics steps for stable positions.
fn create_bench_scene() -> Scene {
    let mut scene = Scene::new();

    // Create 200 files across directory structure (creates dirs automatically)
    let dir_prefixes = [
        "src",
        "src/core",
        "src/core/math",
        "src/core/physics",
        "src/render",
        "src/render/backend",
        "src/render/shaders",
        "tests",
        "tests/unit",
        "tests/integration",
        "docs",
        "docs/api",
        "scripts",
        "config",
        "assets",
        "assets/fonts",
        "assets/icons",
        "lib",
        "lib/utils",
        "lib/types",
    ];

    for i in 0..200 {
        let dir_idx = i % dir_prefixes.len();
        let path_str = format!("{}/file_{i}.rs", dir_prefixes[dir_idx]);
        scene.create_file(Path::new(&path_str));
    }

    // Create 5 users
    let user_names = ["alice", "bob", "carol", "dave", "eve"];
    for name in &user_names {
        scene.get_or_create_user(name);
    }

    // Apply some commits to create active actions
    for i in 0..10 {
        let user = user_names[i % user_names.len()];
        let dir_idx = i % dir_prefixes.len();
        let path_str = format!("{}/file_{i}.rs", dir_prefixes[dir_idx]);
        let path = Path::new(&path_str);
        let files: Vec<(&Path, ActionType)> = vec![(path, ActionType::Modify)];
        scene.apply_commit(user, files.into_iter());
    }

    // Warm up physics for stable entity positions
    for _ in 0..30 {
        scene.update(1.0 / 60.0);
    }

    // Rebuild spatial index for queries
    scene.rebuild_spatial_index();

    scene
}

/// Creates a camera centered on the scene at a typical zoom level.
fn create_bench_camera() -> Camera {
    let mut camera = Camera::new(1920.0, 1080.0);
    camera.jump_to(Vec2::ZERO);
    camera.set_zoom(0.5);
    // Settle camera
    for _ in 0..10 {
        camera.update(1.0 / 60.0);
    }
    camera
}

// =============================================================================
// Full-Frame Benchmark
// =============================================================================

/// Benchmarks every render phase individually and the complete frame.
///
/// This is the primary benchmark for measuring the 2-5 µs frame budget target.
/// Each phase is measured separately to identify bottlenecks, then the total
/// frame is measured to verify the budget.
///
/// # Architecture
///
/// Uses scoped blocks to satisfy the borrow checker:
/// - Spatial query benchmark (needs `&mut` buffers) runs first
/// - Individual phase benchmarks (need `&` buffers via `RenderContext`) run in a scoped block
/// - Total frame benchmark (needs both `&mut` for spatial + `&` for render) creates
///   `RenderContext` inside each loop iteration after the spatial query completes
#[test]
#[allow(clippy::too_many_lines)]
fn bench_full_frame_all_phases() {
    const ITERATIONS: u32 = 1_000;

    let scene = create_bench_scene();
    let camera = create_bench_camera();
    let mut renderer = NoOpRenderer::new();
    let mut label_placer = LabelPlacer::new(camera.zoom());
    let mut active_actions_buf: Vec<(usize, f32)> = Vec::with_capacity(100);
    let mut curve_buf: Vec<Vec2> = Vec::with_capacity(32);
    let mut user_label_candidates: Vec<(rource_core::UserId, Vec2, f32, f32, f32)> =
        Vec::with_capacity(50);
    let mut file_label_candidates: Vec<(rource_core::FileId, Vec2, f32, f32, f32)> =
        Vec::with_capacity(200);
    let watermark = WatermarkSettings::default();

    let visible_bounds = camera.visible_bounds();
    let expanded_bounds = Scene::expand_bounds_for_visibility(&visible_bounds, 200.0);

    // Pre-populate visibility buffers
    let mut visible_dirs_buf = Vec::new();
    let mut visible_files_buf = Vec::new();
    let mut visible_users_buf = Vec::new();
    scene.visible_entities_into(
        &expanded_bounds,
        &mut visible_dirs_buf,
        &mut visible_files_buf,
        &mut visible_users_buf,
    );

    let screen_width = 1920.0_f32;
    let screen_height = 1080.0_f32;

    println!("\n=== Full-Frame Render Phase Benchmark ===");
    println!(
        "Scene: {} dirs, {} files, {} users, {} actions",
        scene.directory_count(),
        scene.file_count(),
        scene.user_count(),
        scene.action_count(),
    );
    println!(
        "Visible: {} dirs, {} files, {} users",
        visible_dirs_buf.len(),
        visible_files_buf.len(),
        visible_users_buf.len(),
    );
    println!(
        "Camera zoom: {:.2}, iterations: {ITERATIONS}",
        camera.zoom()
    );
    println!();

    // ---- Phase 1: visible_entities_into (spatial query) ----
    // Runs FIRST because it needs &mut access to buffers
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        scene.visible_entities_into(
            &expanded_bounds,
            &mut visible_dirs_buf,
            &mut visible_files_buf,
            &mut visible_users_buf,
        );
    }
    let spatial_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);

    // Individual phase benchmarks in a scoped block.
    // RenderContext borrows the visibility buffers immutably; all phase benchmarks
    // that use ctx must complete before ctx is dropped.
    let (
        dirs_ns,
        dirs_calls,
        dir_labels_ns,
        dir_label_calls,
        files_ns,
        file_calls,
        actions_ns,
        action_calls,
        users_ns,
        user_calls,
        label_reset_ns,
        user_labels_ns,
        user_label_calls,
        file_labels_ns,
        file_label_calls,
        watermark_ns,
        watermark_calls,
    ) = {
        let ctx = RenderContext {
            visible_bounds,
            camera_zoom: camera.zoom(),
            use_curves: camera.zoom() < 0.8,
            visible_dirs: &visible_dirs_buf,
            visible_files: &visible_files_buf,
            visible_users: &visible_users_buf,
            show_labels: true,
            font_id: Some(FontId::new(0)),
            font_size: 12.0,
            branch_depth_fade: 0.5,
            branch_opacity_max: 0.6,
        };

        // ---- Phase 2: render_directories ----
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            renderer.reset();
            render_directories(&mut renderer, &ctx, &scene, &camera, &mut curve_buf);
        }
        let dirs_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);
        let dirs_calls = renderer.draw_calls();

        // ---- Phase 3: render_directory_labels ----
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            renderer.reset();
            render_directory_labels(&mut renderer, &ctx, &scene, &camera);
        }
        let dir_labels_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);
        let dir_label_calls = renderer.draw_calls();

        // ---- Phase 4: render_files ----
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            renderer.reset();
            render_files(&mut renderer, &ctx, &scene, &camera, &mut curve_buf);
        }
        let files_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);
        let file_calls = renderer.draw_calls();

        // ---- Phase 5: render_actions ----
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            renderer.reset();
            render_actions(
                &mut renderer,
                &ctx,
                &scene,
                &camera,
                &mut active_actions_buf,
            );
        }
        let actions_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);
        let action_calls = renderer.draw_calls();

        // ---- Phase 6: render_users ----
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            renderer.reset();
            render_users(&mut renderer, &ctx, &scene, &camera);
        }
        let users_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);
        let user_calls = renderer.draw_calls();

        // ---- Phase 7: label_placer reset + set_viewport ----
        label_placer.reset(ctx.camera_zoom);
        label_placer.set_viewport(screen_width, screen_height);
        for i in 0..30 {
            label_placer.try_place(Vec2::new(i as f32 * 100.0, 0.0), 60.0, 18.0);
        }

        let start = Instant::now();
        for _ in 0..ITERATIONS {
            label_placer.reset(ctx.camera_zoom);
            label_placer.set_viewport(screen_width, screen_height);
            for j in 0..5 {
                label_placer.try_place(Vec2::new(j as f32 * 100.0, 0.0), 60.0, 18.0);
            }
        }
        let label_reset_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);

        // ---- Phase 8: render_user_labels ----
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            label_placer.reset(ctx.camera_zoom);
            label_placer.set_viewport(screen_width, screen_height);
            renderer.reset();
            render_user_labels(
                &mut renderer,
                &ctx,
                &scene,
                &camera,
                &mut user_label_candidates,
                &mut label_placer,
            );
        }
        let user_labels_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);
        let user_label_calls = renderer.draw_calls();

        // ---- Phase 9: render_file_labels (production order: after user labels) ----
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            label_placer.reset(ctx.camera_zoom);
            label_placer.set_viewport(screen_width, screen_height);
            render_user_labels(
                &mut renderer,
                &ctx,
                &scene,
                &camera,
                &mut user_label_candidates,
                &mut label_placer,
            );
            renderer.reset();
            render_file_labels(
                &mut renderer,
                &ctx,
                &scene,
                &camera,
                &mut file_label_candidates,
                &mut label_placer,
            );
        }
        let file_labels_total_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);
        let file_labels_ns = file_labels_total_ns.saturating_sub(user_labels_ns);
        let file_label_calls = renderer.draw_calls();

        // ---- Phase 10: render_watermark ----
        let start = Instant::now();
        for _ in 0..ITERATIONS {
            renderer.reset();
            render_watermark(
                &mut renderer,
                &watermark,
                Some(FontId::new(0)),
                screen_width,
                screen_height,
            );
        }
        let watermark_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);
        let watermark_calls = renderer.draw_calls();

        (
            dirs_ns,
            dirs_calls,
            dir_labels_ns,
            dir_label_calls,
            files_ns,
            file_calls,
            actions_ns,
            action_calls,
            users_ns,
            user_calls,
            label_reset_ns,
            user_labels_ns,
            user_label_calls,
            file_labels_ns,
            file_label_calls,
            watermark_ns,
            watermark_calls,
        )
    }; // ctx dropped here — visibility buffers are free for &mut again

    // ---- TOTAL FRAME (all phases in production order) ----
    // Creates RenderContext inside each iteration after spatial query completes,
    // matching the production code pattern in lib.rs render().
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        renderer.reset();
        renderer.begin_frame();
        renderer.clear(Color::new(0.0, 0.0, 0.0, 1.0));

        scene.visible_entities_into(
            &expanded_bounds,
            &mut visible_dirs_buf,
            &mut visible_files_buf,
            &mut visible_users_buf,
        );

        let frame_ctx = RenderContext {
            visible_bounds,
            camera_zoom: camera.zoom(),
            use_curves: camera.zoom() < 0.8,
            visible_dirs: &visible_dirs_buf,
            visible_files: &visible_files_buf,
            visible_users: &visible_users_buf,
            show_labels: true,
            font_id: Some(FontId::new(0)),
            font_size: 12.0,
            branch_depth_fade: 0.5,
            branch_opacity_max: 0.6,
        };

        render_directories(&mut renderer, &frame_ctx, &scene, &camera, &mut curve_buf);
        render_directory_labels(&mut renderer, &frame_ctx, &scene, &camera);
        render_files(&mut renderer, &frame_ctx, &scene, &camera, &mut curve_buf);
        render_actions(
            &mut renderer,
            &frame_ctx,
            &scene,
            &camera,
            &mut active_actions_buf,
        );
        render_users(&mut renderer, &frame_ctx, &scene, &camera);

        label_placer.reset(frame_ctx.camera_zoom);
        label_placer.set_viewport(screen_width, screen_height);

        render_user_labels(
            &mut renderer,
            &frame_ctx,
            &scene,
            &camera,
            &mut user_label_candidates,
            &mut label_placer,
        );
        render_file_labels(
            &mut renderer,
            &frame_ctx,
            &scene,
            &camera,
            &mut file_label_candidates,
            &mut label_placer,
        );
        render_watermark(
            &mut renderer,
            &watermark,
            Some(FontId::new(0)),
            screen_width,
            screen_height,
        );

        renderer.end_frame();
    }
    let total_ns = start.elapsed().as_nanos() / u128::from(ITERATIONS);
    let total_draw_calls = renderer.draw_calls();

    // ---- Sum of individual phases ----
    let sum_ns = spatial_ns
        + dirs_ns
        + dir_labels_ns
        + files_ns
        + actions_ns
        + users_ns
        + label_reset_ns
        + user_labels_ns
        + file_labels_ns
        + watermark_ns;

    // ---- Print Results ----
    println!("| Phase                   | Time (ns) | Time (µs) | % of Frame | Draw Calls |");
    println!("|-------------------------|-----------|-----------|------------|------------|");
    print_row("visible_entities_into", spatial_ns, total_ns, 0);
    print_row("render_directories", dirs_ns, total_ns, dirs_calls);
    print_row(
        "render_directory_labels",
        dir_labels_ns,
        total_ns,
        dir_label_calls,
    );
    print_row("render_files", files_ns, total_ns, file_calls);
    print_row("render_actions", actions_ns, total_ns, action_calls);
    print_row("render_users", users_ns, total_ns, user_calls);
    print_row("label_placer reset", label_reset_ns, total_ns, 0);
    print_row(
        "render_user_labels",
        user_labels_ns,
        total_ns,
        user_label_calls,
    );
    print_row(
        "render_file_labels",
        file_labels_ns,
        total_ns,
        file_label_calls,
    );
    print_row("render_watermark", watermark_ns, total_ns, watermark_calls);
    println!("|-------------------------|-----------|-----------|------------|------------|");
    println!(
        "| Sum of phases           | {sum_ns:>9} | {:>9.2} |     100.0% |            |",
        sum_ns as f64 / 1000.0,
    );
    println!(
        "| **TOTAL FRAME**         | {total_ns:>9} | {:>9.2} |            | {:>10} |",
        total_ns as f64 / 1000.0,
        total_draw_calls,
    );
    println!();

    // Budget analysis
    let total_us = total_ns as f64 / 1000.0;
    println!("Frame budget analysis:");
    println!("  Total frame:  {total_us:.2} µs");
    println!("  2 µs target:  {:.1}% utilized", total_us / 2.0 * 100.0);
    println!("  5 µs target:  {:.1}% utilized", total_us / 5.0 * 100.0);
    println!("  20 µs target: {:.1}% utilized", total_us / 20.0 * 100.0);

    // Top 3 bottlenecks
    let mut phases: Vec<(&str, u128)> = vec![
        ("visible_entities_into", spatial_ns),
        ("render_directories", dirs_ns),
        ("render_directory_labels", dir_labels_ns),
        ("render_files", files_ns),
        ("render_actions", actions_ns),
        ("render_users", users_ns),
        ("label_placer reset", label_reset_ns),
        ("render_user_labels", user_labels_ns),
        ("render_file_labels", file_labels_ns),
        ("render_watermark", watermark_ns),
    ];
    phases.sort_by(|a, b| b.1.cmp(&a.1));
    println!();
    println!("Top 3 bottlenecks:");
    for (i, (name, ns)) in phases.iter().take(3).enumerate() {
        println!(
            "  {}. {} — {} ns ({:.2} µs, {:.1}% of frame)",
            i + 1,
            name,
            ns,
            *ns as f64 / 1000.0,
            *ns as f64 / total_ns as f64 * 100.0,
        );
    }

    // CI-friendly assertion: total frame should be under 200 µs
    // (CI runners are 10-50x slower than dev hardware; dev target is 2-5 µs)
    assert!(
        total_ns < 200_000,
        "Total frame too slow: {total_ns} ns ({total_us:.2} µs), CI limit: 200 µs",
    );
}

/// Helper: prints a row of the benchmark table.
fn print_row(name: &str, ns: u128, total_ns: u128, draw_calls: u32) {
    let us = ns as f64 / 1000.0;
    let pct = if total_ns > 0 {
        ns as f64 / total_ns as f64 * 100.0
    } else {
        0.0
    };
    let calls_str = if draw_calls > 0 {
        format!("{draw_calls:>10}")
    } else {
        String::from("          ")
    };
    println!("| {name:<23} | {ns:>9} | {us:>9.2} | {pct:>9.1}% | {calls_str} |");
}

// =============================================================================
// Individual Phase Benchmarks (for targeted profiling)
// =============================================================================

/// Benchmarks spatial query in isolation with varying entity counts.
#[test]
fn bench_full_frame_spatial_query() {
    const ITERATIONS: u32 = 10_000;

    let scene = create_bench_scene();
    let camera = create_bench_camera();
    let visible_bounds = camera.visible_bounds();
    let expanded = Scene::expand_bounds_for_visibility(&visible_bounds, 200.0);

    let mut dirs = Vec::new();
    let mut files = Vec::new();
    let mut users = Vec::new();

    let start = Instant::now();
    for _ in 0..ITERATIONS {
        scene.visible_entities_into(&expanded, &mut dirs, &mut files, &mut users);
    }
    let elapsed = start.elapsed();
    let per_op = elapsed.as_nanos() / u128::from(ITERATIONS);

    println!(
        "\nSpatial query: {} ns/op ({:.2} µs) — {} dirs, {} files, {} users",
        per_op,
        per_op as f64 / 1000.0,
        dirs.len(),
        files.len(),
        users.len(),
    );

    // Spatial query should be very fast (R-tree/quadtree)
    assert!(
        per_op < 50_000,
        "Spatial query too slow: {per_op} ns (limit: 50 µs)"
    );
}

/// Benchmarks `render_files` phase with realistic file count.
#[test]
fn bench_full_frame_render_files() {
    const ITERATIONS: u32 = 5_000;

    let scene = create_bench_scene();
    let camera = create_bench_camera();
    let mut renderer = NoOpRenderer::new();
    let mut curve_buf: Vec<Vec2> = Vec::with_capacity(32);
    let visible_bounds = camera.visible_bounds();
    let expanded = Scene::expand_bounds_for_visibility(&visible_bounds, 200.0);

    let mut dirs = Vec::new();
    let mut files = Vec::new();
    let mut users = Vec::new();
    scene.visible_entities_into(&expanded, &mut dirs, &mut files, &mut users);

    let ctx = RenderContext {
        visible_bounds,
        camera_zoom: camera.zoom(),
        use_curves: camera.zoom() < 0.8,
        visible_dirs: &dirs,
        visible_files: &files,
        visible_users: &users,
        show_labels: true,
        font_id: Some(FontId::new(0)),
        font_size: 12.0,
        branch_depth_fade: 0.5,
        branch_opacity_max: 0.6,
    };

    let start = Instant::now();
    for _ in 0..ITERATIONS {
        renderer.reset();
        render_files(&mut renderer, &ctx, &scene, &camera, &mut curve_buf);
    }
    let elapsed = start.elapsed();
    let per_op = elapsed.as_nanos() / u128::from(ITERATIONS);

    println!(
        "\nrender_files: {} ns/op ({:.2} µs) — {} visible files, {} draw calls/frame",
        per_op,
        per_op as f64 / 1000.0,
        files.len(),
        renderer.draw_calls(),
    );

    assert!(
        per_op < 100_000,
        "render_files too slow: {per_op} ns (limit: 100 µs)"
    );
}

/// Benchmarks the combined label placement pipeline (user + file labels).
#[test]
fn bench_full_frame_label_pipeline() {
    const ITERATIONS: u32 = 2_000;

    let scene = create_bench_scene();
    let camera = create_bench_camera();
    let mut renderer = NoOpRenderer::new();
    let mut label_placer = LabelPlacer::new(camera.zoom());
    let mut user_candidates: Vec<(rource_core::UserId, Vec2, f32, f32, f32)> =
        Vec::with_capacity(50);
    let mut file_candidates: Vec<(rource_core::FileId, Vec2, f32, f32, f32)> =
        Vec::with_capacity(200);

    let visible_bounds = camera.visible_bounds();
    let expanded = Scene::expand_bounds_for_visibility(&visible_bounds, 200.0);

    let mut dirs = Vec::new();
    let mut files = Vec::new();
    let mut users = Vec::new();
    scene.visible_entities_into(&expanded, &mut dirs, &mut files, &mut users);

    let ctx = RenderContext {
        visible_bounds,
        camera_zoom: camera.zoom(),
        use_curves: camera.zoom() < 0.8,
        visible_dirs: &dirs,
        visible_files: &files,
        visible_users: &users,
        show_labels: true,
        font_id: Some(FontId::new(0)),
        font_size: 12.0,
        branch_depth_fade: 0.5,
        branch_opacity_max: 0.6,
    };

    let start = Instant::now();
    for _ in 0..ITERATIONS {
        renderer.reset();

        label_placer.reset(ctx.camera_zoom);
        label_placer.set_viewport(1920.0, 1080.0);

        render_user_labels(
            &mut renderer,
            &ctx,
            &scene,
            &camera,
            &mut user_candidates,
            &mut label_placer,
        );

        render_file_labels(
            &mut renderer,
            &ctx,
            &scene,
            &camera,
            &mut file_candidates,
            &mut label_placer,
        );
    }
    let elapsed = start.elapsed();
    let per_op = elapsed.as_nanos() / u128::from(ITERATIONS);

    println!(
        "\nLabel pipeline (reset + user + file): {} ns/op ({:.2} µs) — {} draw calls/frame",
        per_op,
        per_op as f64 / 1000.0,
        renderer.draw_calls(),
    );

    // Label pipeline is the most expensive part; should be < 10 µs on dev
    assert!(
        per_op < 100_000,
        "Label pipeline too slow: {per_op} ns (limit: 100 µs)"
    );
}
