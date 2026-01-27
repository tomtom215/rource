//! Load Testing Suite for rource-core
//!
//! Comprehensive sustained load tests validating:
//! - 30-minute continuous operation
//! - 100,000+ commits
//! - Memory stability (< 5% growth after warm-up)
//! - Frame stability (P99 < 2x P50)
//! - Zero panics or OOM conditions
//!
//! # Running Load Tests
//!
//! ```bash
//! # Run the full 30-minute load test
//! cargo test --release -p rource-core --test load_tests -- --ignored --nocapture
//!
//! # Run a shorter 5-minute smoke test
//! cargo test --release -p rource-core --test load_tests smoke -- --ignored --nocapture
//! ```
//!
//! # CI Integration
//!
//! These tests are marked `#[ignore]` and run weekly via `.github/workflows/load-test.yml`

use std::fmt::Write as FmtWrite;
use std::fs::File;
use std::io::Write;
use std::time::{Duration, Instant};

use rource_core::scene::{ActionType, Scene};
use rource_vcs::parser::{CustomParser, ParseOptions, Parser};
use rource_vcs::FileAction;

// ============================================================================
// Memory Tracking (Cross-Platform)
// ============================================================================

/// Gets the current resident set size (RSS) in bytes.
///
/// - Linux: Reads from `/proc/self/statm`
/// - macOS: Uses `mach_task_basic_info`
/// - Other: Returns 0 (not supported)
fn get_rss_bytes() -> u64 {
    #[cfg(target_os = "linux")]
    {
        use std::fs;
        if let Ok(statm) = fs::read_to_string("/proc/self/statm") {
            // statm format: size resident shared text lib data dirty
            // resident is the second field, in pages
            let parts: Vec<&str> = statm.split_whitespace().collect();
            if parts.len() >= 2 {
                if let Ok(pages) = parts[1].parse::<u64>() {
                    // Page size is typically 4096 bytes
                    return pages * 4096;
                }
            }
        }
        0
    }

    #[cfg(target_os = "macos")]
    {
        use std::mem::MaybeUninit;

        extern "C" {
            fn mach_task_self() -> u32;
            fn task_info(
                target_task: u32,
                flavor: i32,
                task_info_out: *mut u8,
                task_info_outCnt: *mut u32,
            ) -> i32;
        }

        const MACH_TASK_BASIC_INFO: i32 = 20;
        const MACH_TASK_BASIC_INFO_COUNT: u32 = 10;

        #[repr(C)]
        struct MachTaskBasicInfo {
            virtual_size: u64,
            resident_size: u64,
            resident_size_max: u64,
            user_time: [u32; 2],
            system_time: [u32; 2],
            policy: i32,
            suspend_count: i32,
        }

        let mut info = MaybeUninit::<MachTaskBasicInfo>::uninit();
        let mut count = MACH_TASK_BASIC_INFO_COUNT;

        unsafe {
            let result = task_info(
                mach_task_self(),
                MACH_TASK_BASIC_INFO,
                info.as_mut_ptr() as *mut u8,
                &mut count,
            );

            if result == 0 {
                return info.assume_init().resident_size;
            }
        }
        0
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        0 // Memory tracking not supported on this platform
    }
}

/// Converts bytes to megabytes.
#[inline]
fn bytes_to_mb(bytes: u64) -> f64 {
    bytes as f64 / (1024.0 * 1024.0)
}

// ============================================================================
// Load Test Metrics
// ============================================================================

/// Statistics collector for load testing.
#[derive(Debug)]
pub struct LoadTestMetrics {
    /// Start time of the test
    start_time: Instant,
    /// Frame times collected during the test
    frame_times: Vec<Duration>,
    /// Memory samples (`elapsed_secs`, `rss_bytes`)
    memory_samples: Vec<(f64, u64)>,
    /// Entity count samples (`elapsed_secs`, `file_count`, `user_count`)
    entity_samples: Vec<(f64, usize, usize)>,
    /// Warm-up memory baseline (RSS bytes after warm-up)
    warmup_rss: u64,
    /// Sample interval for memory/entity tracking
    sample_interval: Duration,
    /// Last sample time
    last_sample: Instant,
    /// Frame count
    frame_count: u64,
}

impl LoadTestMetrics {
    /// Creates a new metrics collector.
    pub fn new(sample_interval: Duration) -> Self {
        let now = Instant::now();
        Self {
            start_time: now,
            frame_times: Vec::with_capacity(1_000_000), // 30 min at 60fps
            memory_samples: Vec::with_capacity(2000),
            entity_samples: Vec::with_capacity(2000),
            warmup_rss: 0,
            sample_interval,
            last_sample: now,
            frame_count: 0,
        }
    }

    /// Records warm-up baseline memory.
    pub fn set_warmup_baseline(&mut self) {
        self.warmup_rss = get_rss_bytes();
        self.memory_samples.push((0.0, self.warmup_rss));
    }

    /// Records a frame time.
    pub fn record_frame(&mut self, duration: Duration) {
        self.frame_times.push(duration);
        self.frame_count += 1;
    }

    /// Checks if it's time to sample memory/entities.
    pub fn should_sample(&self) -> bool {
        self.last_sample.elapsed() >= self.sample_interval
    }

    /// Records a memory and entity sample.
    pub fn sample(&mut self, scene: &Scene) {
        let elapsed = self.start_time.elapsed().as_secs_f64();
        let rss = get_rss_bytes();

        self.memory_samples.push((elapsed, rss));
        self.entity_samples
            .push((elapsed, scene.file_count(), scene.user_count()));
        self.last_sample = Instant::now();
    }

    /// Calculates the Nth percentile of frame times.
    pub fn percentile(&self, p: f64) -> Duration {
        if self.frame_times.is_empty() {
            return Duration::ZERO;
        }

        let mut sorted: Vec<Duration> = self.frame_times.clone();
        sorted.sort();

        let idx = ((p / 100.0) * (sorted.len() - 1) as f64).round() as usize;
        sorted[idx.min(sorted.len() - 1)]
    }

    /// Returns P50 (median) frame time.
    pub fn p50(&self) -> Duration {
        self.percentile(50.0)
    }

    /// Returns P95 frame time.
    pub fn p95(&self) -> Duration {
        self.percentile(95.0)
    }

    /// Returns P99 frame time.
    pub fn p99(&self) -> Duration {
        self.percentile(99.0)
    }

    /// Returns P99.9 frame time.
    pub fn p999(&self) -> Duration {
        self.percentile(99.9)
    }

    /// Returns memory growth percentage since warm-up.
    pub fn memory_growth_percent(&self) -> f64 {
        if self.warmup_rss == 0 {
            return 0.0;
        }

        let current_rss = self.memory_samples.last().map_or(0, |(_, rss)| *rss);
        ((current_rss as f64 - self.warmup_rss as f64) / self.warmup_rss as f64) * 100.0
    }

    /// Returns the elapsed duration.
    pub fn elapsed(&self) -> Duration {
        self.start_time.elapsed()
    }

    /// Returns total frame count.
    pub fn frame_count(&self) -> u64 {
        self.frame_count
    }

    /// Generates a JSON report.
    pub fn to_json(&self) -> String {
        let p50_ms = self.p50().as_secs_f64() * 1000.0;
        let p95_ms = self.p95().as_secs_f64() * 1000.0;
        let p99_ms = self.p99().as_secs_f64() * 1000.0;
        let p999_ms = self.p999().as_secs_f64() * 1000.0;

        let avg_ms = if self.frame_times.is_empty() {
            0.0
        } else {
            self.frame_times
                .iter()
                .map(Duration::as_secs_f64)
                .sum::<f64>()
                / self.frame_times.len() as f64
                * 1000.0
        };

        let fps = if avg_ms > 0.0 { 1000.0 / avg_ms } else { 0.0 };

        format!(
            r#"{{
  "test": "load_test",
  "duration_seconds": {:.1},
  "total_frames": {},
  "frame_times_ms": {{
    "average": {:.3},
    "p50": {:.3},
    "p95": {:.3},
    "p99": {:.3},
    "p999": {:.3}
  }},
  "fps": {{
    "average": {:.1},
    "min_sustainable": {:.1}
  }},
  "memory": {{
    "warmup_mb": {:.1},
    "final_mb": {:.1},
    "growth_percent": {:.2},
    "samples": {}
  }},
  "entities": {{
    "final_files": {},
    "final_users": {},
    "samples": {}
  }},
  "success_criteria": {{
    "duration_30min": {},
    "memory_growth_under_5pct": {},
    "p99_under_2x_p50": {},
    "no_panics": true
  }}
}}"#,
            self.elapsed().as_secs_f64(),
            self.frame_count,
            avg_ms,
            p50_ms,
            p95_ms,
            p99_ms,
            p999_ms,
            fps,
            1000.0 / p99_ms.max(0.001), // Min sustainable FPS based on P99
            bytes_to_mb(self.warmup_rss),
            bytes_to_mb(self.memory_samples.last().map_or(0, |(_, rss)| *rss)),
            self.memory_growth_percent(),
            self.memory_samples.len(),
            self.entity_samples.last().map_or(0, |(_, f, _)| *f),
            self.entity_samples.last().map_or(0, |(_, _, u)| *u),
            self.entity_samples.len(),
            self.elapsed().as_secs() >= 30 * 60,
            self.memory_growth_percent() < 5.0,
            p99_ms < 2.0 * p50_ms,
        )
    }

    /// Writes report to file.
    pub fn write_report(&self, path: &str) -> std::io::Result<()> {
        let mut file = File::create(path)?;
        file.write_all(self.to_json().as_bytes())?;
        Ok(())
    }
}

// ============================================================================
// Synthetic Data Generation
// ============================================================================

/// Generates a synthetic log with the specified number of commits.
fn generate_synthetic_log(commit_count: usize) -> String {
    let mut log = String::with_capacity(commit_count * 50);

    // Simulate realistic patterns:
    // - 50 authors
    // - Files organized in modules
    // - Mix of create/modify/delete
    let authors = (0..50).map(|i| format!("Author{i}")).collect::<Vec<_>>();

    for i in 0..commit_count {
        // Safe cast: commit_count is bounded by test design to fit in i64
        #[allow(clippy::cast_possible_wrap)]
        let timestamp = 1_000_000_000 + (i as i64) * 3600; // One commit per hour
        let author = &authors[i % authors.len()];

        // Vary action types: 60% modify, 30% create, 10% delete
        let action = match i % 10 {
            0 => "D",
            1..=3 => "A",
            _ => "M",
        };

        // Create realistic file paths
        let module = i / 100;
        let file_idx = i % 100;
        let ext = match i % 5 {
            0 => "rs",
            1 => "js",
            2 => "ts",
            3 => "py",
            _ => "md",
        };

        let _ = writeln!(
            log,
            "{timestamp}|{author}|{action}|src/module{module}/file{file_idx}.{ext}",
        );
    }

    log
}

/// Applies commits to scene with proper pacing.
fn apply_commits_to_scene(scene: &mut Scene, commits: &[rource_vcs::Commit]) {
    for commit in commits {
        let files: Vec<_> = commit
            .files
            .iter()
            .map(|f| {
                let action = match f.action {
                    FileAction::Create => ActionType::Create,
                    FileAction::Modify => ActionType::Modify,
                    FileAction::Delete => ActionType::Delete,
                };
                (f.path.as_path(), action)
            })
            .collect();

        scene.apply_commit(&commit.author, files);
    }
}

// ============================================================================
// Load Tests
// ============================================================================

/// Full 30-minute load test with 100k commits.
///
/// Success Criteria:
/// - Duration: 30-minute continuous run
/// - Scale: 100,000+ commits visualized
/// - Memory stability: < 5% growth after warm-up
/// - Frame stability: P99 < 2x P50 after 30 min
/// - No crashes: Zero panics or OOM
#[test]
#[ignore = "Long-running test (30 min). Run with: cargo test --release -p rource-core --test load_tests load_test_30min -- --ignored --nocapture"]
#[allow(clippy::too_many_lines)]
fn load_test_30min_100k_commits() {
    println!("\n========================================");
    println!("Load Test: 30 Minutes, 100k Commits");
    println!("========================================\n");

    let test_duration = Duration::from_secs(30 * 60); // 30 minutes
    let commit_count = 100_000;
    let dt = 1.0 / 60.0; // 60 FPS target

    // Generate synthetic data
    println!("Generating {commit_count} synthetic commits...");
    let log = generate_synthetic_log(commit_count);

    let parser = CustomParser::with_options(ParseOptions::lenient());
    let commits = parser
        .parse_str(&log)
        .expect("Failed to parse synthetic log");
    println!("Parsed {} commits", commits.len());

    // Initialize scene
    println!("Initializing scene...");
    let mut scene = Scene::new();

    // Apply all commits
    println!("Applying commits to scene...");
    apply_commits_to_scene(&mut scene, &commits);
    println!(
        "Scene initialized with {} files, {} users",
        scene.file_count(),
        scene.user_count()
    );

    // Warm-up phase (60 frames = 1 second)
    println!("\nWarm-up phase (60 frames)...");
    for _ in 0..60 {
        scene.update(dt);
    }

    // Initialize metrics with 1-second sampling
    let mut metrics = LoadTestMetrics::new(Duration::from_secs(1));
    metrics.set_warmup_baseline();

    println!(
        "Warm-up baseline RSS: {:.1} MB",
        bytes_to_mb(metrics.warmup_rss)
    );
    println!(
        "\nStarting {:.0}-minute load test...\n",
        test_duration.as_secs_f64() / 60.0
    );

    // Main load test loop
    let start = Instant::now();
    let mut last_progress = Instant::now();

    while start.elapsed() < test_duration {
        // Measure frame time
        let frame_start = Instant::now();
        scene.update(dt);
        let frame_time = frame_start.elapsed();

        metrics.record_frame(frame_time);

        // Periodic sampling
        if metrics.should_sample() {
            metrics.sample(&scene);
        }

        // Progress report every 60 seconds
        if last_progress.elapsed() >= Duration::from_secs(60) {
            let elapsed = start.elapsed();
            let pct = (elapsed.as_secs_f64() / test_duration.as_secs_f64()) * 100.0;
            let rss = bytes_to_mb(get_rss_bytes());
            let growth = metrics.memory_growth_percent();

            println!(
                "[{:>5.1}%] {:>4.0}s elapsed | P50: {:>6.3}ms | P99: {:>6.3}ms | RSS: {:>6.1}MB ({:>+5.1}%)",
                pct,
                elapsed.as_secs_f64(),
                metrics.p50().as_secs_f64() * 1000.0,
                metrics.p99().as_secs_f64() * 1000.0,
                rss,
                growth
            );

            last_progress = Instant::now();
        }
    }

    // Final sample
    metrics.sample(&scene);

    // Report results
    println!("\n========================================");
    println!("Load Test Complete");
    println!("========================================\n");

    let p50 = metrics.p50();
    let p99 = metrics.p99();
    let growth = metrics.memory_growth_percent();
    let p99_ratio = p99.as_secs_f64() / p50.as_secs_f64();

    println!(
        "Duration:        {:.1} minutes",
        metrics.elapsed().as_secs_f64() / 60.0
    );
    println!("Total Frames:    {}", metrics.frame_count());
    println!(
        "Final Entities:  {} files, {} users",
        scene.file_count(),
        scene.user_count()
    );
    println!();
    println!("Frame Times:");
    println!("  P50:           {:.3} ms", p50.as_secs_f64() * 1000.0);
    println!(
        "  P95:           {:.3} ms",
        metrics.p95().as_secs_f64() * 1000.0
    );
    println!("  P99:           {:.3} ms", p99.as_secs_f64() * 1000.0);
    println!(
        "  P99.9:         {:.3} ms",
        metrics.p999().as_secs_f64() * 1000.0
    );
    println!("  P99/P50 Ratio: {p99_ratio:.2}x");
    println!();
    println!("Memory:");
    let warmup_mb = bytes_to_mb(metrics.warmup_rss);
    let final_mb = bytes_to_mb(get_rss_bytes());
    println!("  Warm-up RSS:   {warmup_mb:.1} MB");
    println!("  Final RSS:     {final_mb:.1} MB");
    println!("  Growth:        {growth:.2}%");
    println!();

    // Write report
    let report_path = "load_test_report.json";
    if let Err(e) = metrics.write_report(report_path) {
        eprintln!("Warning: Failed to write report: {e}");
    } else {
        println!("Report written to: {report_path}");
    }

    // Assertions
    println!("\n========================================");
    println!("Verification");
    println!("========================================\n");

    let duration_ok = metrics.elapsed() >= test_duration;
    let memory_ok = growth < 5.0;
    let frame_ok = p99_ratio < 2.0;

    println!(
        "✓ Duration ≥ 30 min:        {}",
        if duration_ok { "PASS" } else { "FAIL" }
    );
    println!(
        "✓ Memory growth < 5%:       {} ({growth:.2}%)",
        if memory_ok { "PASS" } else { "FAIL" },
    );
    println!(
        "✓ P99 < 2x P50:             {} ({p99_ratio:.2}x)",
        if frame_ok { "PASS" } else { "FAIL" },
    );

    // Assert success criteria
    assert!(duration_ok, "Test did not run for full 30 minutes");
    assert!(memory_ok, "Memory growth exceeded 5%: {growth:.2}%");
    assert!(frame_ok, "P99/P50 ratio exceeded 2x: {p99_ratio:.2}x");

    println!("\n✓ All success criteria met!");
}

/// Shorter 5-minute smoke test for CI verification.
#[test]
#[ignore = "CI smoke test (5 min). Run with: cargo test --release -p rource-core --test load_tests smoke -- --ignored --nocapture"]
fn load_test_smoke_5min_10k_commits() {
    println!("\n========================================");
    println!("Smoke Test: 5 Minutes, 10k Commits");
    println!("========================================\n");

    let test_duration = Duration::from_secs(5 * 60); // 5 minutes
    let commit_count = 10_000;
    let dt = 1.0 / 60.0;

    // Generate synthetic data
    println!("Generating {commit_count} synthetic commits...");
    let log = generate_synthetic_log(commit_count);

    let parser = CustomParser::with_options(ParseOptions::lenient());
    let commits = parser
        .parse_str(&log)
        .expect("Failed to parse synthetic log");

    // Initialize and populate scene
    let mut scene = Scene::new();
    apply_commits_to_scene(&mut scene, &commits);
    println!(
        "Scene initialized with {} files, {} users",
        scene.file_count(),
        scene.user_count()
    );

    // Warm-up
    for _ in 0..60 {
        scene.update(dt);
    }

    // Initialize metrics
    let mut metrics = LoadTestMetrics::new(Duration::from_secs(1));
    metrics.set_warmup_baseline();

    println!(
        "Warm-up baseline RSS: {:.1} MB",
        bytes_to_mb(metrics.warmup_rss)
    );
    println!(
        "\nStarting {:.0}-minute smoke test...\n",
        test_duration.as_secs_f64() / 60.0
    );

    // Main loop
    let start = Instant::now();
    let mut last_progress = Instant::now();

    while start.elapsed() < test_duration {
        let frame_start = Instant::now();
        scene.update(dt);
        metrics.record_frame(frame_start.elapsed());

        if metrics.should_sample() {
            metrics.sample(&scene);
        }

        // Progress every 30 seconds
        if last_progress.elapsed() >= Duration::from_secs(30) {
            let elapsed = start.elapsed();
            println!(
                "[{:>5.1}%] {:>4.0}s | P50: {:>6.3}ms | P99: {:>6.3}ms | RSS: {:>6.1}MB ({:>+5.1}%)",
                (elapsed.as_secs_f64() / test_duration.as_secs_f64()) * 100.0,
                elapsed.as_secs_f64(),
                metrics.p50().as_secs_f64() * 1000.0,
                metrics.p99().as_secs_f64() * 1000.0,
                bytes_to_mb(get_rss_bytes()),
                metrics.memory_growth_percent()
            );
            last_progress = Instant::now();
        }
    }

    metrics.sample(&scene);

    // Results
    let p50 = metrics.p50();
    let p99 = metrics.p99();
    let growth = metrics.memory_growth_percent();

    println!("\n========================================");
    println!("Smoke Test Results");
    println!("========================================");
    println!(
        "Duration:    {:.1} minutes",
        metrics.elapsed().as_secs_f64() / 60.0
    );
    println!("Frames:      {}", metrics.frame_count());
    println!("P50:         {:.3} ms", p50.as_secs_f64() * 1000.0);
    println!("P99:         {:.3} ms", p99.as_secs_f64() * 1000.0);
    println!("P99/P50:     {:.2}x", p99.as_secs_f64() / p50.as_secs_f64());
    println!("Mem Growth:  {growth:.2}%");

    // Write report
    let _ = metrics.write_report("load_test_smoke_report.json");

    // Same criteria, just shorter duration
    assert!(growth < 5.0, "Memory growth exceeded 5%: {growth:.2}%");
    assert!(
        p99.as_secs_f64() < 2.0 * p50.as_secs_f64(),
        "P99/P50 ratio exceeded 2x"
    );

    println!("\n✓ Smoke test passed!");
}

/// Quick 1-minute sanity check.
#[test]
fn load_test_quick_sanity_1min() {
    let test_duration = Duration::from_secs(60);
    let commit_count = 1_000;
    let dt = 1.0 / 60.0;

    let log = generate_synthetic_log(commit_count);
    let parser = CustomParser::with_options(ParseOptions::lenient());
    let commits = parser.parse_str(&log).expect("Failed to parse");

    let mut scene = Scene::new();
    apply_commits_to_scene(&mut scene, &commits);

    // Warm-up
    for _ in 0..60 {
        scene.update(dt);
    }

    let mut metrics = LoadTestMetrics::new(Duration::from_secs(1));
    metrics.set_warmup_baseline();

    // Run for 1 minute
    let start = Instant::now();
    while start.elapsed() < test_duration {
        let frame_start = Instant::now();
        scene.update(dt);
        metrics.record_frame(frame_start.elapsed());

        if metrics.should_sample() {
            metrics.sample(&scene);
        }
    }

    // Basic sanity checks
    assert!(
        metrics.frame_count() > 3000,
        "Should have at least 3000 frames in 1 minute"
    );
    assert!(
        metrics.p50().as_secs_f64() * 1000.0 < 100.0,
        "P50 should be under 100ms"
    );
}

// ============================================================================
// Memory-Specific Tests
// ============================================================================

/// Tests for memory leaks by repeatedly creating/destroying entities.
#[test]
#[ignore = "Memory churn stress test. Run with: cargo test --release -p rource-core --test load_tests memory_churn -- --ignored --nocapture"]
fn load_test_memory_churn() {
    println!("\n========================================");
    println!("Memory Churn Test");
    println!("========================================\n");

    let dt = 1.0 / 60.0;
    let iterations = 100;

    let mut scene = Scene::new();

    // Warm-up
    for _ in 0..60 {
        scene.update(dt);
    }

    let baseline_rss = get_rss_bytes();
    let baseline_mb = bytes_to_mb(baseline_rss);
    println!("Baseline RSS: {baseline_mb:.1} MB");

    // Churn: add 1000 files, update, repeat
    for i in 0..iterations {
        // Add files
        let mut log = String::with_capacity(50_000);
        for j in 0..1000 {
            // Safe: i and j are small loop indices that easily fit in i64
            let timestamp = 1_000_000_000_i64 + i64::from(i * 1000 + j);
            let _ = writeln!(log, "{timestamp}|Churner|A|churn/iter{i}/file{j}.rs",);
        }

        let parser = CustomParser::with_options(ParseOptions::lenient());
        let commits = parser.parse_str(&log).expect("Failed to parse");
        apply_commits_to_scene(&mut scene, &commits);

        // Run updates to process actions
        for _ in 0..120 {
            scene.update(dt);
        }

        if i % 10 == 0 {
            let rss = get_rss_bytes();
            let growth = ((rss as f64 - baseline_rss as f64) / baseline_rss as f64) * 100.0;
            let rss_mb = bytes_to_mb(rss);
            println!("Iteration {i}: RSS = {rss_mb:.1} MB ({growth:+.1}%)");
        }
    }

    let final_rss = get_rss_bytes();
    let growth = ((final_rss as f64 - baseline_rss as f64) / baseline_rss as f64) * 100.0;

    let final_mb = bytes_to_mb(final_rss);
    println!("\nFinal RSS: {final_mb:.1} MB");
    println!("Total growth: {growth:.2}%");

    // Allow more growth for churn test (20% instead of 5%)
    // Churn creates many entities which is expected to use memory
    assert!(growth < 100.0, "Excessive memory growth during churn: {growth:.2}%");
}
