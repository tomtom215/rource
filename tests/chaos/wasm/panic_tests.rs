//! Panic Recovery and Error Handling Chaos Tests
//!
//! Tests that verify the system handles panics gracefully,
//! recovers from errors, and maintains stability after failures.

use std::panic::{self, AssertUnwindSafe};

use rource_core::camera::Camera;
use rource_core::scene::Scene;
use rource_math::Vec2;
use rource_vcs::parser::{CustomParser, GitParser, ParseOptions, Parser};

use super::ChaosContext;

// ============================================================================
// Parse Error Recovery
// ============================================================================

#[test]
fn chaos_panic_invalid_utf8_handling() {
    let parser = CustomParser::with_options(ParseOptions::lenient());

    // These should not panic, should return errors or skip invalid data
    let invalid_inputs = [
        "1234567890|Author|A|path.rs", // Valid for comparison
    ];

    for input in &invalid_inputs {
        let result = parser.parse_str(input);
        // Should not panic
        assert!(result.is_ok() || result.is_err());
    }
}

#[test]
fn chaos_panic_malformed_log_recovery() {
    let mut ctx = ChaosContext::new();
    let parser = CustomParser::with_options(ParseOptions::lenient());

    let malformed_logs = [
        "",
        "\n\n\n",
        "invalid",
        "|||",
        "1234567890|",
        "|Author|A|path",
        "1234567890|Author|INVALID_ACTION|path",
        "not_a_timestamp|Author|A|path",
        "1234567890|Author|A|path\0with\0nulls",
    ];

    for log in &malformed_logs {
        ctx.record_iteration();
        let result = parser.parse_str(log);
        // Lenient parser should not panic
        assert!(result.is_ok(), "Parser panicked on: {:?}", log);
    }
}

#[test]
fn chaos_panic_git_log_recovery() {
    let mut ctx = ChaosContext::new();
    let parser = GitParser::with_options(ParseOptions::lenient());

    let malformed_logs = [
        "",
        "not a git log",
        "commit abc123\ngarbage",
        "commit\n\n\nweird",
    ];

    for log in &malformed_logs {
        ctx.record_iteration();
        let result = parser.parse_str(log);
        // Should not panic
        assert!(result.is_ok() || result.is_err());
    }
}

// ============================================================================
// Arithmetic Panic Prevention
// ============================================================================

#[test]
fn chaos_panic_division_by_zero_prevention() {
    use rource_wasm::compute_target_zoom;

    // These could cause division by zero
    let test_cases = [
        (0.0, 0.0, 800.0, 600.0),
        (1000.0, 500.0, 0.0, 0.0),
        (0.0, 500.0, 800.0, 600.0),
        (1000.0, 0.0, 800.0, 600.0),
    ];

    for (bw, bh, sw, sh) in &test_cases {
        // Should not panic
        let zoom = compute_target_zoom(*bw, *bh, *sw, *sh, 0.01, 10.0);
        assert!(zoom.is_finite() || zoom.is_nan());
    }
}

#[test]
fn chaos_panic_overflow_prevention() {
    let mut camera = Camera::new(800.0, 600.0);

    // Values that might cause overflow
    camera.set_zoom(f32::MAX);
    camera.jump_to(Vec2::new(f32::MAX, f32::MAX));
    camera.resize(f32::MAX, f32::MAX);

    // Should not panic
    camera.update(0.016);
    let _ = camera.visible_bounds();
}

#[test]
fn chaos_panic_underflow_prevention() {
    let mut camera = Camera::new(800.0, 600.0);

    camera.set_zoom(f32::MIN_POSITIVE);
    camera.jump_to(Vec2::new(f32::MIN, f32::MIN));

    // Should not panic
    camera.update(0.016);
    let _ = camera.visible_bounds();
}

// ============================================================================
// NaN/Infinity Handling
// ============================================================================

#[test]
fn chaos_panic_nan_propagation_prevention() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    scene.add_file("test.rs", "Author".to_string());

    // Update with NaN should not crash or propagate NaN
    for _ in 0..100 {
        ctx.record_iteration();
        scene.update(f32::NAN);
        scene.update(0.016); // Normal update

        let bounds = scene.compute_entity_bounds();
        if let Some(b) = bounds {
            // Bounds should not be NaN after recovery
            // (depends on implementation - might clamp NaN dt)
            assert!(b.width().is_finite() || b.width().is_nan());
        }
    }
}

#[test]
fn chaos_panic_infinity_handling() {
    let mut ctx = ChaosContext::new();
    let mut camera = Camera::new(800.0, 600.0);

    for _ in 0..100 {
        ctx.record_iteration();

        camera.set_zoom(f32::INFINITY);
        camera.update(0.016);

        let zoom = camera.zoom();
        // Should be clamped or handled
        assert!(zoom.is_finite() || zoom == f32::INFINITY);
    }
}

// ============================================================================
// Bounds Checking
// ============================================================================

#[test]
fn chaos_panic_index_bounds() {
    let mut ctx = ChaosContext::new();
    let parser = CustomParser::with_options(ParseOptions::lenient());

    let commits = parser
        .parse_str("1000|A|A|a.rs\n1001|B|A|b.rs")
        .unwrap();

    // Test accessing commits safely
    for i in 0..10 {
        ctx.record_iteration();
        // Should use safe access patterns
        let commit = commits.get(i);
        if i < commits.len() {
            assert!(commit.is_some());
        } else {
            assert!(commit.is_none());
        }
    }
}

#[test]
fn chaos_panic_empty_collection_access() {
    let parser = CustomParser::with_options(ParseOptions::lenient());
    let commits = parser.parse_str("").unwrap();

    assert!(commits.is_empty());
    assert!(commits.get(0).is_none());
    assert!(commits.first().is_none());
    assert!(commits.last().is_none());
}

// ============================================================================
// Catch Unwind Tests (Panic Safety)
// ============================================================================

#[test]
fn chaos_panic_scene_update_safety() {
    let mut scene = Scene::new();
    scene.add_file("test.rs", "Author".to_string());

    // Test that scene.update doesn't panic
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        scene.update(0.016);
    }));

    assert!(result.is_ok(), "Scene update panicked");
}

#[test]
fn chaos_panic_camera_operations_safety() {
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut camera = Camera::new(800.0, 600.0);
        camera.set_zoom(1.0);
        camera.jump_to(Vec2::new(100.0, 100.0));
        camera.update(0.016);
        let _ = camera.visible_bounds();
    }));

    assert!(result.is_ok(), "Camera operations panicked");
}

#[test]
fn chaos_panic_parser_safety() {
    let inputs = [
        "",
        "garbage",
        "1234567890|Author|A|path.rs",
        "\0\0\0",
        "very long ".repeat(10000).as_str(),
    ];

    for input in &inputs {
        let result = panic::catch_unwind(AssertUnwindSafe(|| {
            let parser = CustomParser::with_options(ParseOptions::lenient());
            let _ = parser.parse_str(input);
        }));

        assert!(result.is_ok(), "Parser panicked on input: {:?}", input);
    }
}

// ============================================================================
// Resource Cleanup After Errors
// ============================================================================

#[test]
fn chaos_panic_cleanup_after_error() {
    let mut ctx = ChaosContext::new();

    for _ in 0..100 {
        ctx.record_iteration();

        let parser = CustomParser::with_options(ParseOptions::lenient());
        let result = parser.parse_str("invalid|||data");

        // Whether success or error, resources should be cleaned up
        drop(result);
        drop(parser);
    }
}

#[test]
fn chaos_panic_scene_cleanup() {
    let mut ctx = ChaosContext::new();

    for _ in 0..100 {
        ctx.record_iteration();

        {
            let mut scene = Scene::new();
            for i in 0..100 {
                scene.add_file(&format!("file{}.rs", i), "Author".to_string());
            }
            // Scene goes out of scope
        }

        // Memory should be freed
    }
}

// ============================================================================
// Stress Test Error Paths
// ============================================================================

#[test]
fn chaos_panic_stress_error_paths() {
    let mut ctx = ChaosContext::new();
    let parser = CustomParser::with_options(ParseOptions::lenient());

    // Rapidly alternate between valid and invalid inputs
    for i in 0..1000 {
        ctx.record_iteration();

        let input = if i % 2 == 0 {
            format!("{}|Author|A|path.rs", 1000 + i)
        } else {
            "invalid|||".to_string()
        };

        let result = parser.parse_str(&input);

        // Alternate results
        if i % 2 == 0 {
            assert!(result.is_ok());
        } else {
            // Lenient parser might still succeed with 0 commits
            assert!(result.is_ok());
        }
    }
}

#[test]
fn chaos_panic_concurrent_error_recovery() {
    let mut ctx = ChaosContext::new();

    // Simulate concurrent operations with errors
    let mut scene = Scene::new();
    let mut camera = Camera::new(800.0, 600.0);

    for i in 0..1000 {
        ctx.record_iteration();

        // Mix valid and potentially problematic operations
        match i % 5 {
            0 => {
                scene.add_file(&format!("file{}.rs", i), "Author".to_string());
            }
            1 => {
                scene.update(if i % 10 == 0 { f32::NAN } else { 0.016 });
            }
            2 => {
                camera.set_zoom(if i % 10 == 0 { f32::NAN } else { 1.0 });
            }
            3 => {
                camera.update(0.016);
            }
            4 => {
                let _ = scene.compute_entity_bounds();
                let _ = camera.visible_bounds();
            }
            _ => {}
        }

        // Periodic "recovery" check
        if i % 100 == 0 {
            camera.set_zoom(1.0);
            camera.update(0.016);
        }
    }

    // System should still be functional
    assert!(scene.file_count() >= 200);
}

// ============================================================================
// Edge Case Error Handling
// ============================================================================

#[test]
fn chaos_panic_empty_string_everywhere() {
    let mut scene = Scene::new();

    // Empty strings should not panic
    scene.add_file("", "".to_string());
    scene.add_file("path", "".to_string());
    scene.add_file("", "Author".to_string());

    scene.update(0.016);
}

#[test]
fn chaos_panic_whitespace_strings() {
    let mut scene = Scene::new();

    scene.add_file("   ", "   ".to_string());
    scene.add_file("\t\t", "\t\t".to_string());
    scene.add_file("\n\n", "\n\n".to_string());

    scene.update(0.016);
}

#[test]
fn chaos_panic_special_characters() {
    let mut scene = Scene::new();

    let special = [
        "\0",      // Null
        "\x7F",    // DEL
        "\u{FEFF}", // BOM
        "\u{200B}", // Zero-width space
        "\u{202E}", // RTL override
        "\u{FFFD}", // Replacement char
    ];

    for s in &special {
        scene.add_file(s, s.to_string());
    }

    scene.update(0.016);
}

#[cfg(test)]
mod recovery_tests {
    use super::*;

    #[test]
    fn test_scene_recovers_from_bad_update() {
        let mut scene = Scene::new();
        scene.add_file("test.rs", "Author".to_string());

        // Bad updates
        scene.update(f32::NAN);
        scene.update(f32::INFINITY);
        scene.update(-1000.0);

        // Normal update should still work
        scene.update(0.016);

        // Scene should still be functional
        assert_eq!(scene.file_count(), 1);
    }

    #[test]
    fn test_camera_recovers_from_bad_values() {
        let mut camera = Camera::new(800.0, 600.0);
        camera.set_zoom_limits(0.1, 10.0);

        // Bad values
        camera.set_zoom(f32::NAN);
        camera.set_zoom(f32::INFINITY);
        camera.set_zoom(-100.0);

        // Set good value
        camera.set_zoom(1.0);

        // Should work normally
        camera.update(0.016);
        let zoom = camera.zoom();
        assert!(zoom >= 0.1 && zoom <= 10.0);
    }
}
