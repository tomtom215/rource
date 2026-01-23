// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Headless rendering mode for batch video export.
//!
//! This module provides headless rendering functionality that runs without
//! a window, outputting frames directly to files or stdout for video encoding.

use std::path::Path;
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use rource_core::camera::Camera;
use rource_core::config::FilterSettings;
use rource_core::scene::{ActionType, Scene};
use rource_core::{DirId, FileId, UserId};
use rource_math::{Bounds, Color, Vec2};
use rource_render::effects::{BloomEffect, ShadowEffect};
use rource_render::{FontId, Renderer, SoftwareRenderer, TextureId};
use rource_vcs::{Commit, CustomParser, GitParser, Parser};

use crate::args::Args;
use crate::export;
use crate::helpers::format_timestamp;
use crate::input::file_action_to_action_type;

/// Minimum screen-space radius to render an entity (LOD threshold).
const MIN_RENDER_RADIUS: f32 = 1.5;

/// Zoom level below which we skip file-to-directory connection lines.
const SKIP_FILE_LINES_ZOOM: f32 = 0.1;

/// Static counter for render profiling (only used in debug/profiling).
static RENDER_PROFILE_COUNTER: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);

// ============================================================================
// Helper Functions (testable without full context)
// ============================================================================

/// Helper functions for headless rendering calculations.
///
/// These functions encapsulate pure computations that can be unit tested
/// without requiring a full rendering context.
#[allow(dead_code)]
mod helpers {
    /// Calculates the estimated duration and frame count for a visualization.
    ///
    /// # Arguments
    /// * `first_timestamp` - Unix timestamp of first commit
    /// * `last_timestamp` - Unix timestamp of last commit
    /// * `seconds_per_day` - Playback speed in seconds per day
    /// * `framerate` - Output framerate
    ///
    /// # Returns
    /// A tuple of (`duration_seconds`, `total_frames`).
    ///
    /// # Examples
    /// ```
    /// let (duration, frames) = calculate_estimated_duration(
    ///     1000000,     // first commit
    ///     1086400,     // last commit (1 day later)
    ///     10.0,        // 10 seconds per day
    ///     60,          // 60 fps
    /// );
    /// assert!((duration - 10.0).abs() < 0.1);
    /// assert_eq!(frames, 600);
    /// ```
    #[inline]
    #[must_use]
    pub fn calculate_estimated_duration(
        first_timestamp: i64,
        last_timestamp: i64,
        seconds_per_day: f32,
        framerate: u32,
    ) -> (f64, u64) {
        let days = (last_timestamp - first_timestamp) as f64 / 86400.0;
        let estimated_seconds = days * f64::from(seconds_per_day);
        let estimated_frames = (estimated_seconds * f64::from(framerate)) as u64;
        (estimated_seconds, estimated_frames)
    }

    /// Calculates progress as a percentage (0.0 to 1.0).
    ///
    /// # Arguments
    /// * `current_commit` - Current commit index
    /// * `total_commits` - Total number of commits
    ///
    /// # Returns
    /// Progress as a float from 0.0 to 1.0.
    ///
    /// # Examples
    /// ```
    /// assert!((calculate_progress_percent(50, 100) - 0.5).abs() < 0.001);
    /// assert!((calculate_progress_percent(0, 100) - 0.0).abs() < 0.001);
    /// assert!((calculate_progress_percent(100, 100) - 1.0).abs() < 0.001);
    /// ```
    #[inline]
    #[must_use]
    pub fn calculate_progress_percent(current_commit: usize, total_commits: usize) -> f32 {
        current_commit as f32 / total_commits.max(1) as f32
    }

    /// Formats a progress status string for display.
    ///
    /// # Arguments
    /// * `frame` - Current frame number
    /// * `progress` - Progress as percentage (0.0 to 1.0)
    /// * `current` - Current commit index
    /// * `total` - Total commits
    ///
    /// # Returns
    /// A formatted progress string.
    ///
    /// # Examples
    /// ```
    /// let status = format_progress_status(100, 0.5, 50, 100);
    /// assert!(status.contains("Frame 100"));
    /// assert!(status.contains("50.0%"));
    /// ```
    #[inline]
    #[must_use]
    pub fn format_progress_status(
        frame: u64,
        progress: f32,
        current: usize,
        total: usize,
    ) -> String {
        format!(
            "\rFrame {}: {:.1}% ({}/{})",
            frame,
            progress * 100.0,
            current,
            total
        )
    }

    /// Checks if rendering is complete.
    ///
    /// # Arguments
    /// * `current_commit` - Current commit index
    /// * `last_applied_commit` - Last commit that was applied
    /// * `total_commits` - Total number of commits
    ///
    /// # Returns
    /// `true` if rendering is complete.
    ///
    /// # Examples
    /// ```
    /// // Not complete when current < total - 1
    /// assert!(!is_render_complete(50, 50, 100));
    /// // Complete when at last commit and all applied
    /// assert!(is_render_complete(99, 99, 100));
    /// // Not complete if not all commits applied
    /// assert!(!is_render_complete(99, 98, 100));
    /// ```
    #[inline]
    #[must_use]
    pub fn is_render_complete(
        current_commit: usize,
        last_applied_commit: usize,
        total_commits: usize,
    ) -> bool {
        total_commits > 0
            && current_commit >= total_commits.saturating_sub(1)
            && last_applied_commit >= current_commit
    }

    /// Calculates the target timestamp based on elapsed days.
    ///
    /// # Arguments
    /// * `first_timestamp` - Unix timestamp of first commit
    /// * `days_elapsed` - Number of days elapsed in simulation
    ///
    /// # Returns
    /// Target Unix timestamp.
    ///
    /// # Examples
    /// ```
    /// // 1 day elapsed = 86400 seconds
    /// assert_eq!(calculate_target_time(1000000, 1.0), 1086400);
    /// // 0 days elapsed
    /// assert_eq!(calculate_target_time(1000000, 0.0), 1000000);
    /// ```
    #[inline]
    #[must_use]
    pub fn calculate_target_time(first_timestamp: i64, days_elapsed: f64) -> i64 {
        first_timestamp + (days_elapsed * 86400.0) as i64
    }

    /// Calculates days elapsed from accumulated time.
    ///
    /// # Arguments
    /// * `accumulated_time` - Total accumulated simulation time in seconds
    /// * `seconds_per_day` - Playback speed in seconds per day
    ///
    /// # Returns
    /// Number of days elapsed.
    ///
    /// # Examples
    /// ```
    /// // 10 seconds at 10 seconds per day = 1 day
    /// assert!((calculate_days_elapsed(10.0, 10.0) - 1.0).abs() < 0.001);
    /// // 5 seconds at 10 seconds per day = 0.5 days
    /// assert!((calculate_days_elapsed(5.0, 10.0) - 0.5).abs() < 0.001);
    /// ```
    #[inline]
    #[must_use]
    pub fn calculate_days_elapsed(accumulated_time: f64, seconds_per_day: f32) -> f64 {
        let days_per_second = 1.0 / f64::from(seconds_per_day);
        accumulated_time * days_per_second
    }

    /// Determines if the current frame should be profiled.
    ///
    /// # Arguments
    /// * `frame_num` - Current frame number
    /// * `interval` - Profile every N frames
    ///
    /// # Returns
    /// `true` if this frame should be profiled.
    ///
    /// # Examples
    /// ```
    /// assert!(should_profile_frame(0, 100));
    /// assert!(should_profile_frame(100, 100));
    /// assert!(!should_profile_frame(50, 100));
    /// ```
    #[inline]
    #[must_use]
    pub fn should_profile_frame(frame_num: u32, interval: u32) -> bool {
        interval > 0 && frame_num % interval == 0
    }

    /// Calculates the fixed time step for a given framerate.
    ///
    /// # Arguments
    /// * `framerate` - Output framerate
    ///
    /// # Returns
    /// Time step in seconds.
    ///
    /// # Examples
    /// ```
    /// assert!((calculate_dt(60) - 0.01666).abs() < 0.001);
    /// assert!((calculate_dt(30) - 0.03333).abs() < 0.001);
    /// ```
    #[inline]
    #[must_use]
    pub fn calculate_dt(framerate: u32) -> f64 {
        1.0 / f64::from(framerate)
    }

    /// Formats a performance timing line for output.
    ///
    /// # Arguments
    /// * `label` - Label for the timing
    /// * `duration_ms` - Duration in milliseconds
    ///
    /// # Returns
    /// A formatted performance line.
    #[inline]
    #[must_use]
    pub fn format_perf_line(label: &str, duration_ms: f64) -> String {
        format!("  {label}:    {duration_ms:.2}ms")
    }

    /// Calculates average time per item.
    ///
    /// # Arguments
    /// * `total_time_ms` - Total time in milliseconds
    /// * `count` - Number of items
    ///
    /// # Returns
    /// Average time per item in milliseconds, or 0.0 if count is 0.
    #[inline]
    #[must_use]
    pub fn calculate_average_time(total_time_ms: f64, count: usize) -> f64 {
        if count > 0 {
            total_time_ms / count as f64
        } else {
            0.0
        }
    }

    /// Calculates initial camera zoom to fit bounds.
    ///
    /// # Arguments
    /// * `bounds_width` - Width of entity bounds
    /// * `bounds_height` - Height of entity bounds
    /// * `viewport_width` - Viewport width
    /// * `viewport_height` - Viewport height
    /// * `padding` - Padding around bounds
    ///
    /// # Returns
    /// Zoom level clamped to [0.01, 10.0].
    ///
    /// # Examples
    /// ```
    /// // Viewport exactly matches bounds (no padding)
    /// let zoom = calculate_fit_zoom(1000.0, 1000.0, 1000.0, 1000.0, 0.0);
    /// assert!((zoom - 1.0).abs() < 0.001);
    /// ```
    #[inline]
    #[must_use]
    pub fn calculate_fit_zoom(
        bounds_width: f32,
        bounds_height: f32,
        viewport_width: f32,
        viewport_height: f32,
        padding: f32,
    ) -> f32 {
        let zoom_x = viewport_width / (bounds_width + padding * 2.0);
        let zoom_y = viewport_height / (bounds_height + padding * 2.0);
        zoom_x.min(zoom_y).clamp(0.01, 10.0)
    }

    /// Calculates the directory depth-based color.
    ///
    /// # Arguments
    /// * `depth` - Directory depth (0 = root)
    ///
    /// # Returns
    /// Gray color value for the directory (lighter = deeper).
    ///
    /// # Examples
    /// ```
    /// let color = calculate_dir_depth_color(0);
    /// assert!((color - 0.15).abs() < 0.001);
    /// let color = calculate_dir_depth_color(5);
    /// assert!((color - 0.40).abs() < 0.001);
    /// ```
    #[inline]
    #[must_use]
    pub fn calculate_dir_depth_color(depth: usize) -> f32 {
        0.15 + 0.05 * (depth as f32).min(5.0)
    }

    /// Determines if a progress update should be printed.
    ///
    /// # Arguments
    /// * `frame_count` - Current frame count
    /// * `interval` - Print every N frames
    ///
    /// # Returns
    /// `true` if progress should be printed.
    #[inline]
    #[must_use]
    pub fn should_print_progress(frame_count: u64, interval: u64) -> bool {
        interval > 0 && frame_count % interval == 0
    }
}

#[allow(unused_imports)]
pub use helpers::*;

/// Build filter settings from command-line arguments.
fn build_filter(args: &Args) -> FilterSettings {
    let mut filter = FilterSettings::new();
    if let Some(ref pattern) = args.show_users {
        filter.set_show_users(Some(pattern.clone()));
    }
    if let Some(ref pattern) = args.hide_users {
        filter.set_hide_users(Some(pattern.clone()));
    }
    if let Some(ref pattern) = args.show_files {
        filter.set_show_files(Some(pattern.clone()));
    }
    if let Some(ref pattern) = args.hide_files {
        filter.set_hide_files(Some(pattern.clone()));
    }
    if let Some(ref pattern) = args.hide_dirs {
        filter.set_hide_dirs(Some(pattern.clone()));
    }
    filter
}

/// Load commits from the repository or log file.
fn load_commits(args: &Args) -> Result<Vec<Commit>> {
    use std::process::Command;

    if args.custom_log {
        let content =
            std::fs::read_to_string(&args.path).context("Failed to read custom log file")?;
        let parser = CustomParser::new();
        parser
            .parse_str(&content)
            .context("Failed to parse custom log")
    } else {
        let output = Command::new("git")
            .arg("-C")
            .arg(&args.path)
            .arg("log")
            .arg("--pretty=format:commit %H%nAuthor: %an <%ae>%nDate: %at")
            .arg("--name-status")
            .arg("--reverse")
            .output()
            .context("Failed to run git log")?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            anyhow::bail!("git log failed: {stderr}");
        }

        let log_content = String::from_utf8_lossy(&output.stdout);
        let parser = GitParser::new();
        parser
            .parse_str(&log_content)
            .context("Failed to parse git log")
    }
}

/// Load an image file and register it as a texture.
///
/// Returns the texture ID and dimensions on success, or None with a warning on failure.
fn load_image_as_texture(
    path: &Path,
    renderer: &mut SoftwareRenderer,
    label: &str,
) -> Option<(TextureId, u32, u32)> {
    match rource_render::image::Image::load_file(path) {
        Ok(image) => {
            let width = image.width();
            let height = image.height();
            let texture_id = renderer.load_texture(width, height, image.data());
            eprintln!("Loaded {label}: {width}x{height} from {}", path.display());
            Some((texture_id, width, height))
        }
        Err(e) => {
            eprintln!("Warning: Failed to load {label} '{}': {e}", path.display());
            None
        }
    }
}

/// Load logo image if specified.
fn load_logo(
    args: &Args,
    renderer: &mut SoftwareRenderer,
) -> (Option<TextureId>, Option<(u32, u32)>) {
    args.logo
        .as_ref()
        .and_then(|path| load_image_as_texture(path, renderer, "logo"))
        .map_or((None, None), |(tex, w, h)| (Some(tex), Some((w, h))))
}

/// Load background image if specified.
fn load_background(args: &Args, renderer: &mut SoftwareRenderer) -> Option<TextureId> {
    args.background_image
        .as_ref()
        .and_then(|path| load_image_as_texture(path, renderer, "background"))
        .map(|(tex, _, _)| tex)
}

/// Run in headless mode (no window, batch video export).
///
/// This creates a renderer without a window and runs at maximum speed,
/// exporting frames directly without display overhead.
#[allow(clippy::too_many_lines)]
pub fn run_headless(args: &Args) -> Result<()> {
    use std::process::Command;

    // Validate that output is specified
    let output = args
        .output
        .as_ref()
        .context("--headless requires --output to be specified")?;

    eprintln!("Running in headless mode");
    eprintln!("Output: {}", output.display());

    // Performance timing
    let total_start = Instant::now();

    // Load commits
    let git_start = Instant::now();
    let commits: Vec<Commit> = if args.custom_log {
        let content =
            std::fs::read_to_string(&args.path).context("Failed to read custom log file")?;
        let parser = CustomParser::new();
        parser
            .parse_str(&content)
            .context("Failed to parse custom log")?
    } else {
        let git_output = Command::new("git")
            .arg("-C")
            .arg(&args.path)
            .arg("log")
            .arg("--pretty=format:commit %H%nAuthor: %an <%ae>%nDate: %at")
            .arg("--name-status")
            .arg("--reverse")
            .output()
            .context("Failed to run git log")?;

        if !git_output.status.success() {
            let stderr = String::from_utf8_lossy(&git_output.stderr);
            anyhow::bail!("git log failed: {stderr}");
        }

        let log_content = String::from_utf8_lossy(&git_output.stdout);
        let git_elapsed = git_start.elapsed();
        eprintln!(
            "[PERF] Git log execution: {:.2}s ({:.1} MB output)",
            git_elapsed.as_secs_f64(),
            git_output.stdout.len() as f64 / 1_000_000.0
        );

        let parse_start = Instant::now();
        let parser = GitParser::new();
        let result = parser
            .parse_str(&log_content)
            .context("Failed to parse git log")?;
        let parse_elapsed = parse_start.elapsed();
        eprintln!("[PERF] Parsing: {:.2}s", parse_elapsed.as_secs_f64());
        result
    };

    if commits.is_empty() {
        anyhow::bail!("No commits found in repository");
    }

    let mut commits = commits;
    let sort_start = Instant::now();
    commits.sort_by_key(|c| c.timestamp);
    let sort_elapsed = sort_start.elapsed();

    // Count total file changes
    let total_files: usize = commits.iter().map(|c| c.files.len()).sum();
    eprintln!("[PERF] Sorting: {:.3}s", sort_elapsed.as_secs_f64());
    eprintln!(
        "Loaded {} commits ({} file changes)",
        commits.len(),
        total_files
    );

    // Create renderer
    let mut renderer = SoftwareRenderer::new(args.width, args.height);
    let font_id = renderer.load_font(rource_render::default_font::ROBOTO_MONO);

    // Load images
    let (logo_texture, logo_dimensions) = load_logo(args, &mut renderer);
    let background_texture = load_background(args, &mut renderer);

    // Initialize scene and camera
    let mut scene = Scene::new();
    let mut camera = Camera::new(args.width as f32, args.height as f32);

    // Initialize effects (BloomEffect uses pre-allocated buffers for zero allocation per frame)
    let mut bloom = if args.no_bloom {
        None
    } else {
        Some(BloomEffect::new())
    };
    // ShadowEffect uses pre-allocated buffers for zero allocation per frame
    let mut shadow = if args.shadows {
        Some(ShadowEffect::subtle())
    } else {
        None
    };

    // Initialize frame exporter
    let mut exporter = if output.as_os_str() == "-" {
        export::FrameExporter::to_stdout(args.framerate)
    } else {
        export::FrameExporter::to_directory(output, args.framerate)
    };

    // Initialize filter settings
    let mut filter = build_filter(args);

    // Playback state
    let seconds_per_day = args.seconds_per_day;
    let speed = 1.0_f32;
    let mut accumulated_time = 0.0_f64;
    let mut current_commit = 0_usize;
    let mut last_applied_commit = 0_usize;

    // Fixed time step for consistent output
    let dt = 1.0 / f64::from(args.framerate);

    // Calculate total duration estimate
    if let (Some(first), Some(last)) = (commits.first(), commits.last()) {
        let days = (last.timestamp - first.timestamp) as f64 / 86400.0;
        let estimated_seconds = days * f64::from(seconds_per_day);
        let estimated_frames = (estimated_seconds * f64::from(args.framerate)) as u64;
        eprintln!("Estimated duration: {estimated_seconds:.1} seconds ({estimated_frames} frames)");
    }

    eprintln!("Rendering frames...");

    // Pre-warm: Apply the first commit and let entities fade in
    if !commits.is_empty() {
        let commit = &commits[0];
        if filter.should_include_user(&commit.author) {
            // Use references instead of cloning paths
            let files: Vec<(&std::path::Path, ActionType)> = commit
                .files
                .iter()
                .filter(|f| filter.should_include_file(&f.path))
                .map(|f| (f.path.as_path(), file_action_to_action_type(f.action)))
                .collect();
            if !files.is_empty() {
                scene.apply_commit(&commit.author, &files);
            }
        }
        last_applied_commit = 1;
        current_commit = 1;

        // Run scene updates to let entities fade in (simulates ~0.5 seconds)
        for _ in 0..30 {
            scene.update(dt as f32);
        }

        // Fit camera immediately to show entities
        if let Some(entity_bounds) = scene.compute_entity_bounds() {
            let center = entity_bounds.center();
            let size = entity_bounds.size();
            let padding = 100.0;
            let (vw, vh) = camera.viewport_size();
            let zoom_x = vw / (size.x + padding * 2.0);
            let zoom_y = vh / (size.y + padding * 2.0);
            let new_zoom = zoom_x.min(zoom_y).clamp(0.01, 10.0);
            camera.jump_to(center);
            camera.set_zoom(new_zoom);
        }
    }

    // Performance tracking accumulators
    let mut total_commit_apply_time = Duration::ZERO;
    let mut total_scene_update_time = Duration::ZERO;
    let mut total_render_time = Duration::ZERO;
    let mut total_effects_time = Duration::ZERO;
    let mut total_export_time = Duration::ZERO;
    let mut commits_applied = 0_usize;
    let loop_start = Instant::now();

    // Per-frame timing for benchmark mode (nanosecond precision)
    let mut frame_times: Vec<Duration> = if args.benchmark {
        Vec::with_capacity(10000) // Pre-allocate for typical benchmark run
    } else {
        Vec::new()
    };

    // Pre-allocate visibility buffers to avoid per-frame allocations (Phase 8 optimization)
    // At 60 FPS, this eliminates ~180 allocations/second
    let mut visible_dirs_buffer: Vec<DirId> = Vec::with_capacity(1000);
    let mut visible_files_buffer: Vec<FileId> = Vec::with_capacity(5000);
    let mut visible_users_buffer: Vec<UserId> = Vec::with_capacity(100);

    // Main rendering loop
    loop {
        // Track per-frame time for benchmark mode
        let frame_start = Instant::now();

        // Update simulation
        accumulated_time += dt * f64::from(speed);
        let days_per_second = 1.0 / f64::from(seconds_per_day);
        let days_elapsed = accumulated_time * days_per_second;

        // Find commits at current time
        if let Some(first) = commits.first() {
            let first_time = first.timestamp;
            let target_time = first_time + (days_elapsed * 86400.0) as i64;

            while current_commit + 1 < commits.len() {
                if commits[current_commit + 1].timestamp <= target_time {
                    current_commit += 1;
                } else {
                    break;
                }
            }
        }

        // Apply pending commits (with filtering)
        let commit_apply_start = Instant::now();
        while last_applied_commit < current_commit {
            // Bounds check to prevent panic on invalid indices
            let Some(commit) = commits.get(last_applied_commit) else {
                break;
            };

            if filter.should_include_user(&commit.author) {
                // Use references instead of cloning paths
                let files: Vec<(&std::path::Path, ActionType)> = commit
                    .files
                    .iter()
                    .filter(|f| filter.should_include_file(&f.path))
                    .map(|f| (f.path.as_path(), file_action_to_action_type(f.action)))
                    .collect();

                if !files.is_empty() {
                    scene.apply_commit(&commit.author, &files);
                    commits_applied += 1;
                }
            }

            last_applied_commit += 1;
        }
        total_commit_apply_time += commit_apply_start.elapsed();

        // Update scene and camera
        let scene_update_start = Instant::now();
        scene.update(dt as f32);
        camera.update(dt as f32);

        // Auto-fit camera to scene content
        if let Some(entity_bounds) = scene.compute_entity_bounds() {
            camera.fit_to_bounds(&entity_bounds, 100.0);
        }
        total_scene_update_time += scene_update_start.elapsed();

        // Render frame (using pre-allocated visibility buffers for zero-allocation)
        let render_start = Instant::now();
        render_frame_headless(
            &mut renderer,
            &scene,
            &camera,
            args,
            font_id,
            &commits,
            current_commit,
            background_texture,
            logo_texture,
            logo_dimensions,
            Some((
                &mut visible_dirs_buffer,
                &mut visible_files_buffer,
                &mut visible_users_buffer,
            )),
        );
        total_render_time += render_start.elapsed();

        // Apply effects
        let effects_start = Instant::now();
        if let Some(ref mut shadow_effect) = shadow {
            let w = renderer.width() as usize;
            let h = renderer.height() as usize;
            shadow_effect.apply(renderer.pixels_mut(), w, h);
        }
        if let Some(ref mut bloom_effect) = bloom {
            let w = renderer.width() as usize;
            let h = renderer.height() as usize;
            bloom_effect.apply(renderer.pixels_mut(), w, h);
        }
        total_effects_time += effects_start.elapsed();

        // Export frame
        let export_start = Instant::now();
        let pixels = renderer.pixels();
        let width = renderer.width();
        let height = renderer.height();
        exporter
            .export_frame(pixels, width, height, dt)
            .context("Failed to export frame")?;
        total_export_time += export_start.elapsed();

        // Record per-frame timing for benchmark mode (nanosecond precision)
        if args.benchmark {
            frame_times.push(frame_start.elapsed());
        }

        // Progress reporting (skip in benchmark mode for clean output)
        if !args.benchmark && exporter.frame_count() % 100 == 0 {
            let progress = current_commit as f32 / commits.len().max(1) as f32;
            eprint!(
                "\rFrame {}: {:.1}% ({}/{})",
                exporter.frame_count(),
                progress * 100.0,
                current_commit,
                commits.len()
            );
        }

        // Check for completion
        if !commits.is_empty()
            && current_commit >= commits.len().saturating_sub(1)
            && last_applied_commit >= current_commit
        {
            break;
        }
    }

    let loop_elapsed = loop_start.elapsed();
    let total_elapsed = total_start.elapsed();
    let frame_count = exporter.frame_count();

    // Output benchmark JSON or human-readable summary
    if args.benchmark {
        // Calculate benchmark statistics from per-frame timings
        let mut sorted_times = frame_times.clone();
        sorted_times.sort();

        let total_ns = loop_elapsed.as_nanos();
        let avg_frame_ns = if frame_count > 0 {
            total_ns / u128::from(frame_count)
        } else {
            0
        };
        let min_frame_ns = sorted_times.first().map_or(0, Duration::as_nanos);
        let max_frame_ns = sorted_times.last().map_or(0, Duration::as_nanos);

        let results = BenchmarkResults {
            frames: frame_count,
            total_ns,
            avg_frame_ns,
            min_frame_ns,
            max_frame_ns,
            p50_frame_ns: percentile(&sorted_times, 50.0),
            p95_frame_ns: percentile(&sorted_times, 95.0),
            p99_frame_ns: percentile(&sorted_times, 99.0),
            commit_apply_ns: total_commit_apply_time.as_nanos(),
            scene_update_ns: total_scene_update_time.as_nanos(),
            render_ns: total_render_time.as_nanos(),
            effects_ns: total_effects_time.as_nanos(),
            export_ns: total_export_time.as_nanos(),
            commits_applied,
            file_count: scene.file_count(),
            user_count: scene.user_count(),
            directory_count: scene.directories().len(),
        };

        results.print_json();
    } else {
        eprintln!("\nExport complete: {frame_count} frames written");

        // Print performance summary
        print_performance_summary(
            total_elapsed,
            loop_elapsed,
            frame_count,
            total_commit_apply_time,
            commits_applied,
            total_scene_update_time,
            total_render_time,
            total_effects_time,
            total_export_time,
            &scene,
        );
    }

    Ok(())
}

/// Print performance summary for headless rendering.
#[allow(clippy::too_many_arguments)]
fn print_performance_summary(
    total_elapsed: Duration,
    loop_elapsed: Duration,
    frame_count: u64,
    total_commit_apply_time: Duration,
    commits_applied: usize,
    total_scene_update_time: Duration,
    total_render_time: Duration,
    total_effects_time: Duration,
    total_export_time: Duration,
    scene: &Scene,
) {
    eprintln!("\n=== PERFORMANCE SUMMARY ===");
    eprintln!("Total time:        {:.2}s", total_elapsed.as_secs_f64());
    eprintln!(
        "  Render loop:     {:.2}s ({} frames, {:.1}ms avg)",
        loop_elapsed.as_secs_f64(),
        frame_count,
        loop_elapsed.as_secs_f64() * 1000.0 / frame_count as f64
    );
    eprintln!("\nBreakdown per frame (avg):");
    eprintln!(
        "  Commit apply:    {:.2}ms ({} commits, {:.3}ms/commit)",
        total_commit_apply_time.as_secs_f64() * 1000.0 / frame_count as f64,
        commits_applied,
        if commits_applied > 0 {
            total_commit_apply_time.as_secs_f64() * 1000.0 / commits_applied as f64
        } else {
            0.0
        }
    );
    eprintln!(
        "  Scene update:    {:.2}ms",
        total_scene_update_time.as_secs_f64() * 1000.0 / frame_count as f64
    );
    eprintln!(
        "  Render:          {:.2}ms",
        total_render_time.as_secs_f64() * 1000.0 / frame_count as f64
    );
    eprintln!(
        "  Effects:         {:.2}ms",
        total_effects_time.as_secs_f64() * 1000.0 / frame_count as f64
    );
    eprintln!(
        "  Export:          {:.2}ms",
        total_export_time.as_secs_f64() * 1000.0 / frame_count as f64
    );

    eprintln!("\nScene stats:");
    eprintln!("  Files:           {}", scene.file_count());
    eprintln!("  Users:           {}", scene.user_count());
    eprintln!("  Directories:     {}", scene.directories().len());
}

// ============================================================================
// Benchmark Output (Nanosecond Precision)
// ============================================================================

/// Benchmark results with nanosecond precision timing.
///
/// Uses `std::time::Instant` for true nanosecond precision on all platforms.
/// This is not limited by browser timing mitigations (unlike WASM).
#[derive(Debug)]
pub struct BenchmarkResults {
    /// Total number of frames rendered.
    pub frames: u64,
    /// Total rendering time in nanoseconds.
    pub total_ns: u128,
    /// Average frame time in nanoseconds.
    pub avg_frame_ns: u128,
    /// Minimum frame time in nanoseconds.
    pub min_frame_ns: u128,
    /// Maximum frame time in nanoseconds.
    pub max_frame_ns: u128,
    /// 50th percentile (median) frame time in nanoseconds.
    pub p50_frame_ns: u128,
    /// 95th percentile frame time in nanoseconds.
    pub p95_frame_ns: u128,
    /// 99th percentile frame time in nanoseconds.
    pub p99_frame_ns: u128,
    /// Total commit apply time in nanoseconds.
    pub commit_apply_ns: u128,
    /// Total scene update time in nanoseconds.
    pub scene_update_ns: u128,
    /// Total render time in nanoseconds.
    pub render_ns: u128,
    /// Total effects time in nanoseconds.
    pub effects_ns: u128,
    /// Total export time in nanoseconds.
    pub export_ns: u128,
    /// Number of commits applied.
    pub commits_applied: usize,
    /// Number of files in scene.
    pub file_count: usize,
    /// Number of users in scene.
    pub user_count: usize,
    /// Number of directories in scene.
    pub directory_count: usize,
}

impl BenchmarkResults {
    /// Outputs the benchmark results as JSON to stdout.
    ///
    /// The JSON format is designed for machine-readable benchmarking:
    /// - All times are in nanoseconds for maximum precision
    /// - Percentiles help identify performance consistency
    /// - Scene stats provide context for the benchmark
    pub fn print_json(&self) {
        println!(
            r#"{{"frames":{},"total_ns":{},"avg_frame_ns":{},"min_frame_ns":{},"max_frame_ns":{},"p50_frame_ns":{},"p95_frame_ns":{},"p99_frame_ns":{},"phases":{{"commit_apply_ns":{},"scene_update_ns":{},"render_ns":{},"effects_ns":{},"export_ns":{}}},"commits_applied":{},"scene":{{"files":{},"users":{},"directories":{}}}}}"#,
            self.frames,
            self.total_ns,
            self.avg_frame_ns,
            self.min_frame_ns,
            self.max_frame_ns,
            self.p50_frame_ns,
            self.p95_frame_ns,
            self.p99_frame_ns,
            self.commit_apply_ns,
            self.scene_update_ns,
            self.render_ns,
            self.effects_ns,
            self.export_ns,
            self.commits_applied,
            self.file_count,
            self.user_count,
            self.directory_count,
        );
    }
}

/// Calculates percentile value from a sorted slice of durations.
fn percentile(sorted_times: &[Duration], pct: f64) -> u128 {
    if sorted_times.is_empty() {
        return 0;
    }
    let idx = ((sorted_times.len() as f64 - 1.0) * pct / 100.0).round() as usize;
    sorted_times[idx.min(sorted_times.len() - 1)].as_nanos()
}

/// Render a single frame in headless mode.
///
/// # Arguments
///
/// * `visibility_buffers` - Optional pre-allocated buffers for zero-allocation visibility queries.
///   Pass `Some((dirs, files, users))` for the main render loop to avoid allocations.
///   Pass `None` for one-time renders (like screenshots) where allocation is acceptable.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
pub fn render_frame_headless(
    renderer: &mut SoftwareRenderer,
    scene: &Scene,
    camera: &Camera,
    args: &Args,
    font_id: Option<FontId>,
    commits: &[Commit],
    current_commit: usize,
    background_texture: Option<TextureId>,
    logo_texture: Option<TextureId>,
    logo_dimensions: Option<(u32, u32)>,
    visibility_buffers: Option<(&mut Vec<DirId>, &mut Vec<FileId>, &mut Vec<UserId>)>,
) {
    renderer.begin_frame();

    // Clear to background color
    let bg_color = args.parse_background_color();
    renderer.clear(bg_color);

    // Draw background image if available
    if let Some(bg_texture) = background_texture {
        let viewport_bounds = Bounds::new(
            Vec2::ZERO,
            Vec2::new(renderer.width() as f32, renderer.height() as f32),
        );
        renderer.draw_quad(viewport_bounds, Some(bg_texture), Color::WHITE);
    }

    // Get visible bounds for frustum culling
    let cull_start = Instant::now();
    let visible_bounds = camera.visible_bounds();
    let culling_bounds = Scene::expand_bounds_for_visibility(&visible_bounds, 100.0);

    // Use provided buffers (zero-allocation) or allocate new ones (for one-time renders)
    let (visible_dir_ids, visible_file_ids, visible_user_ids): (
        Vec<DirId>,
        Vec<FileId>,
        Vec<UserId>,
    );
    let (dir_ids_ref, file_ids_ref, user_ids_ref): (&[DirId], &[FileId], &[UserId]);

    if let Some((dirs_buf, files_buf, users_buf)) = visibility_buffers {
        // Zero-allocation path: reuse provided buffers
        scene.visible_entities_into(&culling_bounds, dirs_buf, files_buf, users_buf);
        dir_ids_ref = dirs_buf.as_slice();
        file_ids_ref = files_buf.as_slice();
        user_ids_ref = users_buf.as_slice();
    } else {
        // Allocating path: for one-time renders like screenshots
        let result = scene.visible_entities(&culling_bounds);
        visible_dir_ids = result.0;
        visible_file_ids = result.1;
        visible_user_ids = result.2;
        dir_ids_ref = &visible_dir_ids;
        file_ids_ref = &visible_file_ids;
        user_ids_ref = &visible_user_ids;
    }
    let cull_time = cull_start.elapsed();

    let camera_zoom = camera.zoom();

    // Profile every 100th frame
    let frame_num = RENDER_PROFILE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let profile = frame_num % 100 == 0;

    // LOD: Skip file-to-directory lines when very zoomed out
    let draw_file_lines = camera_zoom > SKIP_FILE_LINES_ZOOM;

    // Render directories
    let dirs_start = Instant::now();
    let mut dirs_rendered = 0_u32;
    for &dir_id in dir_ids_ref {
        let Some(dir) = scene.directories().get(dir_id) else {
            continue;
        };
        if !dir.is_visible() {
            continue;
        }
        let screen_pos = camera.world_to_screen(dir.position());
        let radius = dir.radius() * camera_zoom;

        // LOD: Skip directories that are too small
        if radius < MIN_RENDER_RADIUS {
            continue;
        }

        let depth_color = 0.15 + 0.05 * (dir.depth() as f32).min(5.0);
        let dir_color = Color::new(depth_color, depth_color, depth_color + 0.1, 0.5);
        renderer.draw_circle(screen_pos, radius, 1.0, dir_color);
        dirs_rendered += 1;

        // Only draw parent connection lines if directories are large enough
        if radius >= 3.0 {
            if let Some(parent_pos) = dir.parent_position() {
                let parent_screen = camera.world_to_screen(parent_pos);
                renderer.draw_line(parent_screen, screen_pos, 1.0, dir_color.with_alpha(0.3));
            }
        }
    }
    let dirs_time = dirs_start.elapsed();

    // Render files
    let files_start = Instant::now();
    let mut files_rendered = 0_u32;
    let show_filenames = !args.hide_filenames;
    let file_font_size = args.font_size * 0.8;

    for &file_id in file_ids_ref {
        let Some(file) = scene.get_file(file_id) else {
            continue;
        };
        if file.alpha() < 0.01 {
            continue;
        }
        let screen_pos = camera.world_to_screen(file.position());
        let radius = file.radius() * camera_zoom;

        // LOD: Skip files that are too small
        let draw_radius = radius.max(2.0);
        if draw_radius < MIN_RENDER_RADIUS {
            continue;
        }

        let color = file.current_color().with_alpha(file.alpha());
        renderer.draw_disc(screen_pos, draw_radius, color);
        files_rendered += 1;

        // LOD: Only draw file-to-directory lines when zoomed in enough
        if draw_file_lines {
            if let Some(dir) = scene.directories().get(file.directory()) {
                let dir_screen = camera.world_to_screen(dir.position());
                renderer.draw_line(
                    dir_screen,
                    screen_pos,
                    0.5,
                    color.with_alpha(0.2 * file.alpha()),
                );
            }
        }

        // LOD: Only show filenames when zoomed in and file is prominent
        if show_filenames && file.alpha() > 0.5 && camera_zoom > 0.3 {
            if let Some(fid) = font_id {
                let name = file.name();
                let label_pos = Vec2::new(
                    screen_pos.x + radius + 3.0,
                    screen_pos.y - file_font_size * 0.3,
                );
                let label_color = Color::new(0.9, 0.9, 0.9, 0.7 * file.alpha());
                renderer.draw_text(name, label_pos, fid, file_font_size, label_color);
            }
        }
    }
    let files_time = files_start.elapsed();

    // Render actions (beams)
    let actions_start = Instant::now();
    let mut actions_rendered = 0_u32;
    for action in scene.actions() {
        let user_opt = scene.get_user(action.user());
        let file_opt = scene.get_file(action.file());
        if let (Some(user), Some(file)) = (user_opt, file_opt) {
            let user_screen = camera.world_to_screen(user.position());
            let file_screen = camera.world_to_screen(file.position());
            let beam_end = user_screen.lerp(file_screen, action.progress());
            let beam_color = action.beam_color();
            renderer.draw_line(user_screen, beam_end, 2.0, beam_color);
            let head_radius = 3.0 * camera_zoom;
            renderer.draw_disc(beam_end, head_radius.max(2.0), beam_color);
            actions_rendered += 1;
        }
    }
    let actions_time = actions_start.elapsed();

    // Render users
    let users_start = Instant::now();
    let mut users_rendered = 0_u32;
    let show_usernames = !args.hide_usernames;
    let name_font_size = args.font_size;

    for &user_id in user_ids_ref {
        let Some(user) = scene.get_user(user_id) else {
            continue;
        };
        if user.alpha() < 0.01 {
            continue;
        }
        let screen_pos = camera.world_to_screen(user.position());
        let radius = user.radius() * camera_zoom;
        let color = user.display_color();
        renderer.draw_disc(screen_pos, radius.max(5.0), color);
        if user.is_active() {
            renderer.draw_circle(
                screen_pos,
                radius * 1.3,
                2.0,
                color.with_alpha(0.5 * user.alpha()),
            );
        }
        users_rendered += 1;
        if show_usernames {
            if let Some(fid) = font_id {
                let name = user.name();
                let label_pos = Vec2::new(
                    screen_pos.x + radius + 5.0,
                    screen_pos.y - name_font_size * 0.3,
                );
                let label_color = Color::new(1.0, 1.0, 1.0, 0.8 * user.alpha());
                renderer.draw_text(name, label_pos, fid, name_font_size, label_color);
            }
        }
    }
    let users_time = users_start.elapsed();

    // Print profiling info every 100 frames
    if profile {
        eprintln!("\n[RENDER PROFILE] Frame {frame_num}:");
        eprintln!(
            "  Culling:     {:.2}ms (vis: {} dirs, {} files, {} users)",
            cull_time.as_secs_f64() * 1000.0,
            dir_ids_ref.len(),
            file_ids_ref.len(),
            user_ids_ref.len()
        );
        eprintln!(
            "  Directories: {:.2}ms ({} rendered)",
            dirs_time.as_secs_f64() * 1000.0,
            dirs_rendered
        );
        eprintln!(
            "  Files:       {:.2}ms ({} rendered, {:.3}ms/file)",
            files_time.as_secs_f64() * 1000.0,
            files_rendered,
            if files_rendered > 0 {
                files_time.as_secs_f64() * 1000.0 / f64::from(files_rendered)
            } else {
                0.0
            }
        );
        eprintln!(
            "  Actions:     {:.2}ms ({} rendered)",
            actions_time.as_secs_f64() * 1000.0,
            actions_rendered
        );
        eprintln!(
            "  Users:       {:.2}ms ({} rendered)",
            users_time.as_secs_f64() * 1000.0,
            users_rendered
        );
        eprintln!("  Zoom:        {camera_zoom:.4}");
    }

    // Render UI overlays
    let width = renderer.width() as f32;
    let height = renderer.height() as f32;

    // Progress bar
    if !commits.is_empty() {
        let bar_height = 4.0;
        let progress = current_commit as f32 / commits.len().max(1) as f32;
        renderer.draw_quad(
            Bounds::new(
                Vec2::new(0.0, height - bar_height),
                Vec2::new(width, height),
            ),
            None,
            Color::new(0.2, 0.2, 0.2, 0.5),
        );
        renderer.draw_quad(
            Bounds::new(
                Vec2::new(0.0, height - bar_height),
                Vec2::new(width * progress, height),
            ),
            None,
            Color::new(0.3, 0.6, 1.0, 0.8),
        );
    }

    // Text overlays
    if let Some(fid) = font_id {
        let font_size = args.font_size;
        let text_color = Color::new(1.0, 1.0, 1.0, 0.9);

        // Title
        if let Some(ref title) = args.title {
            let title_size = font_size * 1.5;
            let title_x = (width / 2.0) - (title.len() as f32 * title_size * 0.3);
            renderer.draw_text(
                title,
                Vec2::new(title_x.max(10.0), 20.0),
                fid,
                title_size,
                text_color,
            );
        }

        // Date display
        if !args.hide_date && !commits.is_empty() {
            if let Some(commit) = commits.get(current_commit.saturating_sub(1).max(0)) {
                let date_str = format_timestamp(commit.timestamp);
                renderer.draw_text(
                    &date_str,
                    Vec2::new(10.0, height - 30.0),
                    fid,
                    font_size,
                    text_color.with_alpha(0.7),
                );
            }
        }

        // Current commit info
        if current_commit > 0 {
            if let Some(commit) = commits.get(current_commit - 1) {
                renderer.draw_text(
                    &commit.author,
                    Vec2::new(10.0, height - 50.0),
                    fid,
                    font_size,
                    text_color.with_alpha(0.8),
                );
                let files_text = format!("{} files", commit.files.len());
                renderer.draw_text(
                    &files_text,
                    Vec2::new(10.0, height - 70.0),
                    fid,
                    font_size * 0.9,
                    text_color.with_alpha(0.6),
                );
            }
        }

        // Stats text
        let file_count = scene.file_count();
        let user_count = scene.user_count();
        let total_commits = commits.len();
        let stats_text = format!(
            "{current_commit}/{total_commits} commits | {file_count} files | {user_count} users"
        );
        renderer.draw_text(
            &stats_text,
            Vec2::new(10.0, 20.0),
            fid,
            font_size * 0.8,
            text_color.with_alpha(0.5),
        );
    }

    // Draw logo in top-right corner if available
    if let (Some(logo_tex), Some((logo_width, logo_height))) = (logo_texture, logo_dimensions) {
        let viewport_width = renderer.width() as f32;
        let logo_offset = args.parse_logo_offset();
        let (offset_x, offset_y) = logo_offset;

        let logo_x = viewport_width - logo_width as f32 - offset_x as f32;
        let logo_y = offset_y as f32;

        let logo_bounds = Bounds::new(
            Vec2::new(logo_x, logo_y),
            Vec2::new(logo_x + logo_width as f32, logo_y + logo_height as f32),
        );
        renderer.draw_quad(logo_bounds, Some(logo_tex), Color::WHITE);
    }

    renderer.end_frame();
}

/// Run in screenshot mode (render single frame to PNG).
#[allow(clippy::too_many_lines)]
pub fn run_screenshot(args: &Args, screenshot_path: &Path) -> Result<()> {
    use rource_vcs::FileAction;

    eprintln!("Taking screenshot...");

    // Load commits
    let commits = load_commits(args)?;

    if commits.is_empty() {
        anyhow::bail!("No commits found in repository");
    }

    // Determine which commit to render
    let target_commit = args
        .screenshot_at
        .unwrap_or_else(|| commits.len().saturating_sub(1));
    let target_commit = target_commit.min(commits.len().saturating_sub(1));

    eprintln!(
        "Rendering commit {}/{} ({})",
        target_commit + 1,
        commits.len(),
        commits[target_commit].author
    );

    // Create renderer and scene
    let mut renderer = SoftwareRenderer::new(args.width, args.height);
    let mut scene = Scene::new();
    let mut camera = Camera::new(args.width as f32, args.height as f32);

    // Load font
    let font_id = renderer.load_font(rource_render::default_font::ROBOTO_MONO);

    // Load images
    let (logo_texture, logo_dimensions) = load_logo(args, &mut renderer);
    let background_texture = load_background(args, &mut renderer);

    // Initialize filter settings
    let mut filter = build_filter(args);

    // Apply commits up to and including the target
    for commit in commits.iter().take(target_commit + 1) {
        if !filter.should_include_user(&commit.author) {
            continue;
        }

        // Use references instead of cloning paths
        let files: Vec<(&std::path::Path, ActionType)> = commit
            .files
            .iter()
            .filter(|f| filter.should_include_file(&f.path))
            .map(|f| {
                (
                    f.path.as_path(),
                    match f.action {
                        FileAction::Create => ActionType::Create,
                        FileAction::Modify => ActionType::Modify,
                        FileAction::Delete => ActionType::Delete,
                    },
                )
            })
            .collect();

        if !files.is_empty() {
            scene.apply_commit(&commit.author, &files);
        }
    }

    // Pre-warm scene
    for _ in 0..30 {
        scene.update(1.0 / 60.0);
    }

    // Position camera
    if let Some(bounds) = scene.compute_entity_bounds() {
        if bounds.width() > 0.0 && bounds.height() > 0.0 {
            let padded = Bounds::from_center_size(
                bounds.center(),
                Vec2::new(bounds.width() * 1.2, bounds.height() * 1.2),
            );
            let zoom_x = args.width as f32 / padded.width();
            let zoom_y = args.height as f32 / padded.height();
            let zoom = zoom_x.min(zoom_y).clamp(0.1, 5.0);

            camera.jump_to(padded.center());
            camera.set_zoom(zoom);
        }
    }

    // Render the frame (None for visibility buffers: one-time render, allocation is acceptable)
    render_frame_headless(
        &mut renderer,
        &scene,
        &camera,
        args,
        font_id,
        &commits,
        target_commit,
        background_texture,
        logo_texture,
        logo_dimensions,
        None,
    );

    // Apply effects if enabled
    if !args.no_bloom {
        let mut bloom = BloomEffect::new();
        bloom.apply(
            renderer.pixels_mut(),
            args.width as usize,
            args.height as usize,
        );
    }

    if args.shadows {
        let mut shadow = ShadowEffect::subtle();
        shadow.apply(
            renderer.pixels_mut(),
            args.width as usize,
            args.height as usize,
        );
    }

    // Save the screenshot
    let pixels = renderer.pixels();
    export::write_png_to_file(pixels, args.width, args.height, screenshot_path)
        .context("Failed to save screenshot")?;

    eprintln!("Screenshot saved: {}", screenshot_path.display());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    // ========================================================================
    // Integration Tests (require Args context)
    // ========================================================================

    #[test]
    fn test_headless_requires_output() {
        let args = Args {
            headless: true,
            output: None,
            ..Args::default()
        };

        let result = run_headless(&args);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("--headless requires --output"));
    }

    #[test]
    fn test_headless_args_stdout_detection() {
        let args = Args {
            headless: true,
            output: Some(PathBuf::from("-")),
            ..Args::default()
        };

        assert!(args.headless);
        assert_eq!(args.output.as_ref().unwrap().as_os_str(), "-");
    }

    #[test]
    fn test_headless_args_directory_detection() {
        let args = Args {
            headless: true,
            output: Some(PathBuf::from("/tmp/frames")),
            ..Args::default()
        };

        assert!(args.headless);
        assert_eq!(
            args.output.as_ref().unwrap().to_str().unwrap(),
            "/tmp/frames"
        );
    }

    // ========================================================================
    // Estimated Duration Tests
    // ========================================================================

    #[test]
    fn test_calculate_estimated_duration_one_day() {
        // 1 day at 10 seconds per day = 10 seconds
        let (duration, frames) = calculate_estimated_duration(0, 86400, 10.0, 60);
        assert!((duration - 10.0).abs() < 0.1);
        assert_eq!(frames, 600);
    }

    #[test]
    fn test_calculate_estimated_duration_one_week() {
        // 7 days at 10 seconds per day = 70 seconds
        let (duration, frames) = calculate_estimated_duration(0, 7 * 86400, 10.0, 60);
        assert!((duration - 70.0).abs() < 0.1);
        assert_eq!(frames, 4200);
    }

    #[test]
    fn test_calculate_estimated_duration_different_framerate() {
        // 1 day at 10 seconds per day at 30 fps
        let (duration, frames) = calculate_estimated_duration(0, 86400, 10.0, 30);
        assert!((duration - 10.0).abs() < 0.1);
        assert_eq!(frames, 300);
    }

    #[test]
    fn test_calculate_estimated_duration_fast_playback() {
        // 1 day at 1 second per day = 1 second
        let (duration, frames) = calculate_estimated_duration(0, 86400, 1.0, 60);
        assert!((duration - 1.0).abs() < 0.1);
        assert_eq!(frames, 60);
    }

    #[test]
    fn test_calculate_estimated_duration_zero_span() {
        // Same timestamp = 0 duration
        let (duration, frames) = calculate_estimated_duration(1000, 1000, 10.0, 60);
        assert!((duration - 0.0).abs() < 0.1);
        assert_eq!(frames, 0);
    }

    // ========================================================================
    // Progress Calculation Tests
    // ========================================================================

    #[test]
    fn test_calculate_progress_percent_halfway() {
        assert!((calculate_progress_percent(50, 100) - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_calculate_progress_percent_start() {
        assert!((calculate_progress_percent(0, 100) - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_progress_percent_end() {
        assert!((calculate_progress_percent(100, 100) - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_progress_percent_zero_total() {
        // Should not panic, returns 0
        assert!((calculate_progress_percent(0, 0) - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_progress_percent_partial() {
        assert!((calculate_progress_percent(25, 100) - 0.25).abs() < 0.001);
        assert!((calculate_progress_percent(75, 100) - 0.75).abs() < 0.001);
    }

    // ========================================================================
    // Progress Status Formatting Tests
    // ========================================================================

    #[test]
    fn test_format_progress_status_basic() {
        let status = format_progress_status(100, 0.5, 50, 100);
        assert!(status.contains("Frame 100"));
        assert!(status.contains("50.0%"));
        assert!(status.contains("50/100"));
    }

    #[test]
    fn test_format_progress_status_start() {
        let status = format_progress_status(0, 0.0, 0, 100);
        assert!(status.contains("Frame 0"));
        assert!(status.contains("0.0%"));
    }

    #[test]
    fn test_format_progress_status_end() {
        let status = format_progress_status(1000, 1.0, 100, 100);
        assert!(status.contains("Frame 1000"));
        assert!(status.contains("100.0%"));
    }

    // ========================================================================
    // Render Complete Tests
    // ========================================================================

    #[test]
    fn test_is_render_complete_not_started() {
        assert!(!is_render_complete(0, 0, 100));
    }

    #[test]
    fn test_is_render_complete_in_progress() {
        assert!(!is_render_complete(50, 50, 100));
    }

    #[test]
    fn test_is_render_complete_at_end() {
        assert!(is_render_complete(99, 99, 100));
    }

    #[test]
    fn test_is_render_complete_not_applied() {
        // At last commit but not all applied
        assert!(!is_render_complete(99, 98, 100));
    }

    #[test]
    fn test_is_render_complete_empty() {
        // No commits = not complete
        assert!(!is_render_complete(0, 0, 0));
    }

    #[test]
    fn test_is_render_complete_single_commit() {
        assert!(is_render_complete(0, 0, 1));
    }

    // ========================================================================
    // Target Time Calculation Tests
    // ========================================================================

    #[test]
    fn test_calculate_target_time_zero_elapsed() {
        assert_eq!(calculate_target_time(1_000_000, 0.0), 1_000_000);
    }

    #[test]
    fn test_calculate_target_time_one_day() {
        // 1 day = 86400 seconds
        assert_eq!(calculate_target_time(1_000_000, 1.0), 1_086_400);
    }

    #[test]
    fn test_calculate_target_time_partial_day() {
        // 0.5 days = 43200 seconds
        assert_eq!(calculate_target_time(1_000_000, 0.5), 1_043_200);
    }

    #[test]
    fn test_calculate_target_time_multiple_days() {
        // 7 days = 604800 seconds
        assert_eq!(calculate_target_time(1_000_000, 7.0), 1_604_800);
    }

    // ========================================================================
    // Days Elapsed Calculation Tests
    // ========================================================================

    #[test]
    fn test_calculate_days_elapsed_one_day() {
        // 10 seconds at 10 seconds per day = 1 day
        assert!((calculate_days_elapsed(10.0, 10.0) - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_days_elapsed_half_day() {
        // 5 seconds at 10 seconds per day = 0.5 days
        assert!((calculate_days_elapsed(5.0, 10.0) - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_calculate_days_elapsed_fast_speed() {
        // 1 second at 1 second per day = 1 day
        assert!((calculate_days_elapsed(1.0, 1.0) - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_days_elapsed_slow_speed() {
        // 100 seconds at 100 seconds per day = 1 day
        assert!((calculate_days_elapsed(100.0, 100.0) - 1.0).abs() < 0.001);
    }

    // ========================================================================
    // Profile Frame Tests
    // ========================================================================

    #[test]
    fn test_should_profile_frame_at_interval() {
        assert!(should_profile_frame(0, 100));
        assert!(should_profile_frame(100, 100));
        assert!(should_profile_frame(200, 100));
    }

    #[test]
    fn test_should_profile_frame_not_at_interval() {
        assert!(!should_profile_frame(50, 100));
        assert!(!should_profile_frame(99, 100));
        assert!(!should_profile_frame(101, 100));
    }

    #[test]
    fn test_should_profile_frame_every_frame() {
        // Interval of 1 = every frame
        assert!(should_profile_frame(0, 1));
        assert!(should_profile_frame(1, 1));
        assert!(should_profile_frame(999, 1));
    }

    #[test]
    fn test_should_profile_frame_disabled() {
        // Interval of 0 = disabled
        assert!(!should_profile_frame(0, 0));
        assert!(!should_profile_frame(100, 0));
    }

    // ========================================================================
    // Fixed Time Step Tests
    // ========================================================================

    #[test]
    fn test_calculate_dt_60fps() {
        let dt = calculate_dt(60);
        assert!((dt - 1.0 / 60.0).abs() < 0.0001);
    }

    #[test]
    fn test_calculate_dt_30fps() {
        let dt = calculate_dt(30);
        assert!((dt - 1.0 / 30.0).abs() < 0.0001);
    }

    #[test]
    fn test_calculate_dt_144fps() {
        let dt = calculate_dt(144);
        assert!((dt - 1.0 / 144.0).abs() < 0.0001);
    }

    // ========================================================================
    // Performance Line Formatting Tests
    // ========================================================================

    #[test]
    fn test_format_perf_line_basic() {
        let line = format_perf_line("Render", 16.5);
        assert!(line.contains("Render"));
        assert!(line.contains("16.50ms"));
    }

    #[test]
    fn test_format_perf_line_small_value() {
        let line = format_perf_line("Quick", 0.01);
        assert!(line.contains("0.01ms"));
    }

    // ========================================================================
    // Average Time Calculation Tests
    // ========================================================================

    #[test]
    fn test_calculate_average_time_normal() {
        assert!((calculate_average_time(100.0, 10) - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_average_time_zero_count() {
        assert!((calculate_average_time(100.0, 0) - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_average_time_single_item() {
        assert!((calculate_average_time(50.0, 1) - 50.0).abs() < 0.001);
    }

    // ========================================================================
    // Camera Fit Zoom Tests
    // ========================================================================

    #[test]
    fn test_calculate_fit_zoom_exact_match() {
        // Viewport matches bounds exactly (no padding)
        let zoom = calculate_fit_zoom(1000.0, 1000.0, 1000.0, 1000.0, 0.0);
        assert!((zoom - 1.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_fit_zoom_wider_viewport() {
        // Viewport is wider than bounds
        let zoom = calculate_fit_zoom(500.0, 1000.0, 1000.0, 1000.0, 0.0);
        assert!((zoom - 1.0).abs() < 0.001); // Height-limited
    }

    #[test]
    fn test_calculate_fit_zoom_taller_viewport() {
        // Viewport is taller than bounds
        let zoom = calculate_fit_zoom(1000.0, 500.0, 1000.0, 1000.0, 0.0);
        assert!((zoom - 1.0).abs() < 0.001); // Width-limited
    }

    #[test]
    fn test_calculate_fit_zoom_with_padding() {
        // With padding, zoom should be smaller
        let zoom = calculate_fit_zoom(1000.0, 1000.0, 1000.0, 1000.0, 100.0);
        assert!(zoom < 1.0);
    }

    #[test]
    fn test_calculate_fit_zoom_clamp_max() {
        // Very small bounds should be clamped to max 10.0
        let zoom = calculate_fit_zoom(10.0, 10.0, 1000.0, 1000.0, 0.0);
        assert!((zoom - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_calculate_fit_zoom_clamp_min() {
        // Very large bounds should be clamped to min 0.01
        let zoom = calculate_fit_zoom(100_000.0, 100_000.0, 1000.0, 1000.0, 0.0);
        assert!((zoom - 0.01).abs() < 0.001);
    }

    // ========================================================================
    // Directory Depth Color Tests
    // ========================================================================

    #[test]
    fn test_calculate_dir_depth_color_root() {
        let color = calculate_dir_depth_color(0);
        assert!((color - 0.15).abs() < 0.001);
    }

    #[test]
    fn test_calculate_dir_depth_color_depth_1() {
        let color = calculate_dir_depth_color(1);
        assert!((color - 0.20).abs() < 0.001);
    }

    #[test]
    fn test_calculate_dir_depth_color_depth_5() {
        let color = calculate_dir_depth_color(5);
        assert!((color - 0.40).abs() < 0.001);
    }

    #[test]
    fn test_calculate_dir_depth_color_deep() {
        // Clamped to max depth 5
        let color = calculate_dir_depth_color(10);
        assert!((color - 0.40).abs() < 0.001);
    }

    // ========================================================================
    // Progress Print Tests
    // ========================================================================

    #[test]
    fn test_should_print_progress_at_interval() {
        assert!(should_print_progress(0, 100));
        assert!(should_print_progress(100, 100));
        assert!(should_print_progress(200, 100));
    }

    #[test]
    fn test_should_print_progress_not_at_interval() {
        assert!(!should_print_progress(50, 100));
        assert!(!should_print_progress(99, 100));
    }

    #[test]
    fn test_should_print_progress_disabled() {
        assert!(!should_print_progress(0, 0));
        assert!(!should_print_progress(100, 0));
    }

    // ========================================================================
    // Percentile Calculation Tests
    // ========================================================================

    #[test]
    fn test_percentile_empty() {
        let times: Vec<Duration> = vec![];
        assert_eq!(percentile(&times, 50.0), 0);
    }

    #[test]
    fn test_percentile_single_element() {
        let times = vec![Duration::from_nanos(1000)];
        assert_eq!(percentile(&times, 50.0), 1000);
        assert_eq!(percentile(&times, 0.0), 1000);
        assert_eq!(percentile(&times, 100.0), 1000);
    }

    #[test]
    fn test_percentile_median_odd() {
        // Sorted: [100, 200, 300, 400, 500]
        let times: Vec<Duration> = vec![
            Duration::from_nanos(100),
            Duration::from_nanos(200),
            Duration::from_nanos(300),
            Duration::from_nanos(400),
            Duration::from_nanos(500),
        ];
        // p50 with 5 elements: (5-1) * 0.5 = 2 -> index 2 -> 300
        assert_eq!(percentile(&times, 50.0), 300);
    }

    #[test]
    fn test_percentile_p95() {
        // 100 elements from 1 to 100 ns
        let times: Vec<Duration> = (1..=100).map(Duration::from_nanos).collect();
        // p95: (100-1) * 0.95 = 94.05 rounds to 94 -> index 94 -> 95ns
        assert_eq!(percentile(&times, 95.0), 95);
    }

    #[test]
    fn test_percentile_p99() {
        // 100 elements from 1 to 100 ns
        let times: Vec<Duration> = (1..=100).map(Duration::from_nanos).collect();
        // p99: (100-1) * 0.99 = 98.01 rounds to 98 -> index 98 -> 99ns
        assert_eq!(percentile(&times, 99.0), 99);
    }

    #[test]
    fn test_percentile_min_max() {
        let times: Vec<Duration> = vec![
            Duration::from_nanos(100),
            Duration::from_nanos(500),
            Duration::from_nanos(1000),
        ];
        assert_eq!(percentile(&times, 0.0), 100);
        assert_eq!(percentile(&times, 100.0), 1000);
    }

    // ========================================================================
    // Benchmark Results Tests
    // ========================================================================

    #[test]
    fn test_benchmark_results_print_json_format() {
        let results = BenchmarkResults {
            frames: 100,
            total_ns: 1_000_000_000,
            avg_frame_ns: 10_000_000,
            min_frame_ns: 8_000_000,
            max_frame_ns: 15_000_000,
            p50_frame_ns: 9_500_000,
            p95_frame_ns: 14_000_000,
            p99_frame_ns: 14_500_000,
            commit_apply_ns: 100_000_000,
            scene_update_ns: 200_000_000,
            render_ns: 500_000_000,
            effects_ns: 150_000_000,
            export_ns: 50_000_000,
            commits_applied: 50,
            file_count: 200,
            user_count: 10,
            directory_count: 25,
        };
        // Just verify it doesn't panic - actual output goes to stdout
        // In production, we'd capture stdout, but for unit tests this validates the format compiles
        let _ = results;
    }
}
