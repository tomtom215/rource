//! API Boundary Chaos Tests
//!
//! Tests every public WASM API method with edge case inputs to ensure
//! the API boundary is robust against any JavaScript input.

use rource_core::camera::Camera;
use rource_core::config::Settings;
use rource_core::scene::Scene;
use rource_math::Vec2;
use rource_vcs::parser::{CustomParser, ParseOptions, Parser};

use super::{malformed_log_line, random_chaos_string, ChaosContext};

// ============================================================================
// Log Parsing Edge Cases
// ============================================================================

#[test]
fn chaos_parse_empty_log() {
    let parser = CustomParser::with_options(ParseOptions::lenient());
    let result = parser.parse_str("");
    assert!(result.is_ok());
    assert_eq!(result.unwrap().len(), 0);
}

#[test]
fn chaos_parse_whitespace_only_log() {
    let parser = CustomParser::with_options(ParseOptions::lenient());
    let inputs = ["   ", "\t\t\t", "\n\n\n", "  \n  \t  \n  ", "\r\n\r\n"];

    for input in &inputs {
        let result = parser.parse_str(input);
        assert!(result.is_ok(), "Failed on whitespace input: {:?}", input);
    }
}

#[test]
fn chaos_parse_malformed_lines() {
    let mut ctx = ChaosContext::new();
    let parser = CustomParser::with_options(ParseOptions::lenient());

    for i in 0..100 {
        ctx.record_iteration();
        let line = malformed_log_line(i);
        let result = parser.parse_str(&line);
        // Lenient parsing should never panic or error fatally
        assert!(
            result.is_ok(),
            "Parse failed on variant {}: {:?}",
            i,
            result
        );
    }

    assert!(ctx.metrics().iterations >= 100);
}

#[test]
fn chaos_parse_unicode_chaos() {
    let parser = CustomParser::with_options(ParseOptions::lenient());

    let chaos_logs = [
        "1234567890|🦀|A|src/main.rs",                       // Emoji author
        "1234567890|Author|A|🔥/fire.rs",                    // Emoji path
        "1234567890|مؤلف|A|path.rs",                         // Arabic author
        "1234567890|作者|A|源代码.rs",                       // Chinese
        "1234567890|著者|A|ソース.rs",                       // Japanese
        "1234567890|저자|A|소스.rs",                         // Korean
        "1234567890|Авт\u{0301}ор|A|path.rs",                // Combining accent
        "1234567890|\u{202E}rotcuA|A|path.rs",               // RTL override
        "1234567890|Author\u{200B}Name|A|path.rs",           // Zero-width space
        "1234567890|Author|A|path\u{FEFF}.rs",               // BOM in path
    ];

    for log in &chaos_logs {
        let result = parser.parse_str(log);
        assert!(result.is_ok(), "Failed on unicode input: {}", log);
    }
}

#[test]
fn chaos_parse_injection_attempts() {
    let parser = CustomParser::with_options(ParseOptions::lenient());

    let injection_logs = [
        "1234567890|<script>alert('xss')</script>|A|path.rs",
        "1234567890|Author|A|../../../etc/passwd",
        "1234567890|'; DROP TABLE commits; --|A|path.rs",
        "1234567890|Author|A|path\"; rm -rf /; echo \"",
        "1234567890|Author|A|path${{7*7}}",
        "1234567890|Author|A|path{{constructor.constructor('return this')()}}",
        "1234567890|Author|A|path%00.rs",
        "1234567890|Author|A|path\x00.rs",
    ];

    for log in &injection_logs {
        let result = parser.parse_str(log);
        // Should parse without executing anything dangerous
        assert!(result.is_ok(), "Failed on injection attempt: {}", log);
    }
}

#[test]
fn chaos_parse_oversized_log() {
    let parser = CustomParser::with_options(ParseOptions::lenient());

    // Generate a massive log
    let mut log = String::with_capacity(10_000_000);
    for i in 0..100_000 {
        log.push_str(&format!("{}|Author{}|A|path/to/file{}.rs\n", 1000000000 + i, i, i));
    }

    let result = parser.parse_str(&log);
    assert!(result.is_ok());
    // Should have parsed all commits
    assert_eq!(result.unwrap().len(), 100_000);
}

#[test]
fn chaos_parse_deeply_nested_paths() {
    let parser = CustomParser::with_options(ParseOptions::lenient());

    // Very deep directory nesting
    let deep_path = (0..100).map(|i| format!("dir{}", i)).collect::<Vec<_>>().join("/");
    let log = format!("1234567890|Author|A|{}/file.rs", deep_path);

    let result = parser.parse_str(&log);
    assert!(result.is_ok());
}

#[test]
fn chaos_parse_mixed_valid_invalid() {
    let parser = CustomParser::with_options(ParseOptions::lenient());

    let log = r#"
1234567890|ValidAuthor|A|valid/path.rs
invalid line here
1234567891|AnotherValid|M|another.rs
||||
1234567892|ThirdValid|D|deleted.rs
    "#;

    let result = parser.parse_str(log);
    assert!(result.is_ok());
    let commits = result.unwrap();
    // Should have parsed at least the valid lines
    assert!(commits.len() >= 3);
}

// ============================================================================
// Scene State Edge Cases
// ============================================================================

#[test]
fn chaos_scene_empty_operations() {
    let mut scene = Scene::new();

    // Operations on empty scene should not panic
    scene.update(0.016);
    scene.update(0.0);
    scene.update(-1.0); // Negative dt
    scene.update(f32::MAX);
    scene.update(f32::MIN);
    scene.update(f32::NAN);
    scene.update(f32::INFINITY);
    scene.update(f32::NEG_INFINITY);

    assert_eq!(scene.file_count(), 0);
    assert_eq!(scene.user_count(), 0);
}

#[test]
fn chaos_scene_bounds_empty() {
    let scene = Scene::new();
    let bounds = scene.compute_entity_bounds();
    assert!(bounds.is_none());
}

#[test]
fn chaos_scene_rapid_updates() {
    let mut ctx = ChaosContext::new();
    let parser = CustomParser::with_options(ParseOptions::lenient());
    let commits = parser
        .parse_str("1234567890|Author|A|src/main.rs")
        .unwrap();

    let mut scene = Scene::new();

    // Apply commit
    for file in &commits[0].files {
        scene.add_file(&file.path, commits[0].author.clone());
    }

    // Rapid updates with varying dt
    for i in 0..10_000 {
        ctx.record_iteration();
        let dt = match i % 10 {
            0 => 0.0,
            1 => 0.001,
            2 => 0.016,
            3 => 0.1,
            4 => 1.0,
            5 => -0.016,
            6 => f32::EPSILON,
            7 => f32::MIN_POSITIVE,
            8 => 1000.0,
            _ => 0.016,
        };
        scene.update(dt);
    }

    assert!(ctx.metrics().iterations == 10_000);
}

// ============================================================================
// Camera Edge Cases
// ============================================================================

#[test]
fn chaos_camera_extreme_zoom() {
    let mut camera = Camera::new(800.0, 600.0);

    let extreme_zooms = [
        0.0,
        -1.0,
        0.00001,
        0.001,
        0.01,
        0.1,
        1.0,
        10.0,
        100.0,
        1000.0,
        10000.0,
        100000.0,
        f32::MAX,
        f32::MIN,
        f32::EPSILON,
        f32::MIN_POSITIVE,
    ];

    for zoom in &extreme_zooms {
        camera.set_zoom(*zoom);
        // Should not panic, may clamp
        let actual = camera.zoom();
        assert!(actual.is_finite(), "Zoom became non-finite for input {}", zoom);
    }
}

#[test]
fn chaos_camera_nan_infinity() {
    let mut camera = Camera::new(800.0, 600.0);

    // NaN zoom
    camera.set_zoom(f32::NAN);
    let zoom = camera.zoom();
    assert!(zoom.is_finite(), "Camera allowed NaN zoom");

    // Infinity zoom
    camera.set_zoom(f32::INFINITY);
    let zoom = camera.zoom();
    assert!(zoom.is_finite(), "Camera allowed infinite zoom");

    // NaN position
    camera.jump_to(Vec2::new(f32::NAN, f32::NAN));
    let pos = camera.position();
    // Position handling depends on implementation
    // Just ensure we don't panic

    // Infinity position
    camera.jump_to(Vec2::new(f32::INFINITY, f32::NEG_INFINITY));
    let _pos = camera.position();
}

#[test]
fn chaos_camera_extreme_positions() {
    let mut camera = Camera::new(800.0, 600.0);

    let extreme_positions = [
        Vec2::ZERO,
        Vec2::new(1.0, 1.0),
        Vec2::new(-1.0, -1.0),
        Vec2::new(1e10, 1e10),
        Vec2::new(-1e10, -1e10),
        Vec2::new(f32::MAX, f32::MAX),
        Vec2::new(f32::MIN, f32::MIN),
        Vec2::new(f32::MAX, f32::MIN),
        Vec2::new(0.0, f32::MAX),
    ];

    for pos in &extreme_positions {
        camera.jump_to(*pos);
        let actual = camera.position();
        // Should not panic
        assert!(!actual.x.is_nan() || !pos.x.is_finite());
        assert!(!actual.y.is_nan() || !pos.y.is_finite());
    }
}

#[test]
fn chaos_camera_resize_edge_cases() {
    let mut camera = Camera::new(800.0, 600.0);

    let sizes = [
        (0.0, 0.0),
        (1.0, 1.0),
        (0.0, 600.0),
        (800.0, 0.0),
        (-100.0, 600.0),
        (800.0, -100.0),
        (f32::MAX, f32::MAX),
        (f32::MIN_POSITIVE, f32::MIN_POSITIVE),
        (10000.0, 10000.0),
        (0.001, 0.001),
    ];

    for (w, h) in &sizes {
        camera.resize(*w, *h);
        // Should not panic
    }
}

#[test]
fn chaos_camera_rapid_operations() {
    let mut ctx = ChaosContext::new();
    let mut camera = Camera::new(800.0, 600.0);

    for i in 0..10_000 {
        ctx.record_iteration();
        match i % 5 {
            0 => camera.set_zoom((i as f32 / 1000.0).clamp(0.01, 100.0)),
            1 => camera.jump_to(Vec2::new(i as f32, (i * 2) as f32)),
            2 => camera.resize((i % 2000) as f32 + 100.0, (i % 1500) as f32 + 100.0),
            3 => camera.update(0.016),
            _ => {
                let _ = camera.visible_bounds();
            }
        }
    }

    assert!(ctx.metrics().iterations == 10_000);
}

// ============================================================================
// Settings Edge Cases
// ============================================================================

#[test]
fn chaos_settings_extreme_values() {
    let mut settings = Settings::default();

    // Extreme display sizes
    settings.display.width = 0;
    settings.display.height = 0;
    settings.display.width = u32::MAX;
    settings.display.height = u32::MAX;

    // Extreme playback speeds
    settings.playback.seconds_per_day = 0.0;
    settings.playback.seconds_per_day = -1.0;
    settings.playback.seconds_per_day = f32::MAX;
    settings.playback.seconds_per_day = f32::NAN;
    settings.playback.seconds_per_day = f32::INFINITY;

    // Extreme font size
    settings.display.font_size = 0.0;
    settings.display.font_size = -10.0;
    settings.display.font_size = 10000.0;

    // Should not panic during any of this
}

// ============================================================================
// Numeric Edge Cases
// ============================================================================

#[test]
fn chaos_frame_timing_edge_cases() {
    use rource_wasm::{clamp_dt, compute_frame_dt, MAX_FRAME_DT};

    let test_cases = [
        (0.0, 0.0),
        (1000.0, 1000.0),
        (1000.0, 0.0),
        (0.0, 1000.0),
        (f64::MAX, 0.0),
        (0.0, f64::MAX),
        (f64::NAN, 0.0),
        (0.0, f64::NAN),
        (f64::INFINITY, 0.0),
        (f64::NEG_INFINITY, 0.0),
        (-1000.0, 0.0),
        (1e100, 1e99),
    ];

    for (timestamp, last_frame) in &test_cases {
        let dt = compute_frame_dt(*timestamp, *last_frame);
        let clamped = clamp_dt(dt, MAX_FRAME_DT);
        // Should not panic, result should be finite or default
        assert!(clamped.is_finite() || dt.is_nan());
    }
}

#[test]
fn chaos_zoom_calculation_edge_cases() {
    use rource_wasm::compute_target_zoom;

    let test_cases = [
        (0.0, 0.0, 800.0, 600.0),
        (1000.0, 500.0, 0.0, 0.0),
        (-100.0, 500.0, 800.0, 600.0),
        (1000.0, -500.0, 800.0, 600.0),
        (f32::MAX, f32::MAX, 800.0, 600.0),
        (1000.0, 500.0, f32::MAX, f32::MAX),
        (f32::MIN_POSITIVE, f32::MIN_POSITIVE, 800.0, 600.0),
        (1e10, 1e10, 1e-10, 1e-10),
    ];

    for (bw, bh, sw, sh) in &test_cases {
        let zoom = compute_target_zoom(*bw, *bh, *sw, *sh, 0.01, 10.0);
        assert!(zoom.is_finite(), "Zoom not finite for inputs: {:?}", (bw, bh, sw, sh));
        assert!(zoom >= 0.01);
        assert!(zoom <= 10.0);
    }
}

// ============================================================================
// Concurrent Operation Simulation
// ============================================================================

#[test]
fn chaos_simulated_concurrent_operations() {
    let mut ctx = ChaosContext::new();
    let parser = CustomParser::with_options(ParseOptions::lenient());

    // Simulate what might happen with concurrent JS calls
    let mut scene = Scene::new();
    let mut camera = Camera::new(800.0, 600.0);

    for i in 0..1000 {
        ctx.record_iteration();

        // Simulate interleaved operations
        let log = format!("{}|Author{}|A|path{}.rs", 1000000000 + i, i, i);
        if let Ok(commits) = parser.parse_str(&log) {
            for commit in &commits {
                for file in &commit.files {
                    scene.add_file(&file.path, commit.author.clone());
                }
            }
        }

        scene.update(0.016);
        camera.update(0.016);

        // Random camera ops
        match i % 4 {
            0 => camera.set_zoom((i as f32 / 100.0).clamp(0.1, 10.0)),
            1 => camera.jump_to(Vec2::new((i * 10) as f32, (i * 5) as f32)),
            2 => camera.resize(800.0 + (i % 200) as f32, 600.0 + (i % 150) as f32),
            _ => {}
        }
    }

    assert!(scene.file_count() == 1000);
}

// ============================================================================
// Fuzzing with Random Inputs
// ============================================================================

#[test]
fn chaos_fuzz_log_parsing() {
    let mut ctx = ChaosContext::new();
    let parser = CustomParser::with_options(ParseOptions::lenient());

    for seed in 0..100 {
        ctx.record_iteration();
        let chaos = random_chaos_string(200, seed);
        let result = parser.parse_str(&chaos);
        // Should not panic
        assert!(result.is_ok() || result.is_err());
    }
}

#[test]
fn chaos_fuzz_scene_file_paths() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    for seed in 0..100 {
        ctx.record_iteration();
        let chaos_path = random_chaos_string(50, seed);
        let chaos_author = random_chaos_string(20, seed + 1000);

        scene.add_file(&chaos_path, chaos_author);
    }

    // Should have added files without panic
    assert_eq!(scene.file_count(), 100);
}

#[cfg(test)]
mod edge_case_tests {
    use super::*;

    #[test]
    fn test_empty_author() {
        let mut scene = Scene::new();
        scene.add_file("path.rs", String::new());
        assert_eq!(scene.file_count(), 1);
    }

    #[test]
    fn test_empty_path() {
        let mut scene = Scene::new();
        scene.add_file("", "Author".to_string());
        // Behavior depends on implementation
    }

    #[test]
    fn test_whitespace_path() {
        let mut scene = Scene::new();
        scene.add_file("   ", "Author".to_string());
    }

    #[test]
    fn test_unicode_normalization() {
        let mut scene = Scene::new();
        // These look the same but are different unicode
        scene.add_file("café", "Author".to_string()); // precomposed
        scene.add_file("cafe\u{0301}", "Author".to_string()); // decomposed
        // May or may not be treated as same file
    }
}
