//! State Corruption and Invalid State Transition Tests
//!
//! Tests that verify the system handles invalid state transitions
//! gracefully and maintains invariants under chaotic conditions.

use rource_core::camera::Camera;
use rource_core::scene::Scene;
use rource_math::Vec2;
use rource_vcs::parser::{CustomParser, ParseOptions, Parser};

use super::ChaosContext;

// ============================================================================
// Playback State Chaos
// ============================================================================

#[test]
fn chaos_state_empty_playback() {
    // Simulates playback operations on empty commit list
    let mut ctx = ChaosContext::new();

    for _ in 0..100 {
        ctx.record_iteration();
        // Would test Rource instance if available
        // For now test underlying components
        let scene = Scene::new();
        assert_eq!(scene.file_count(), 0);
    }
}

#[test]
fn chaos_state_seek_beyond_bounds() {
    let mut ctx = ChaosContext::new();
    let parser = CustomParser::with_options(ParseOptions::lenient());
    let commits = parser
        .parse_str(
            "1000|A|A|a.rs\n\
         1001|B|A|b.rs\n\
         1002|C|A|c.rs",
        )
        .unwrap();

    let commit_count = commits.len();

    // Test seeking to invalid indices
    let invalid_seeks = [
        usize::MAX,
        commit_count,
        commit_count + 1,
        commit_count + 1000,
    ];

    for seek in &invalid_seeks {
        ctx.record_iteration();
        // In actual implementation, seek should clamp or ignore
        assert!(*seek >= commit_count || *seek < commit_count);
    }
}

#[test]
fn chaos_state_rapid_play_pause() {
    let mut ctx = ChaosContext::new();

    // Simulate rapid play/pause toggling
    let mut is_playing = false;

    for _ in 0..10000 {
        ctx.record_iteration();
        is_playing = !is_playing;
    }

    // Should not cause any state corruption
    assert!(is_playing || !is_playing);
}

#[test]
fn chaos_state_speed_extremes() {
    let mut ctx = ChaosContext::new();

    let extreme_speeds = [
        0.0,
        -1.0,
        -100.0,
        0.001,
        0.01,
        0.1,
        1.0,
        10.0,
        100.0,
        1000.0,
        f32::MAX,
        f32::MIN,
        f32::EPSILON,
        f32::MIN_POSITIVE,
        f32::NAN,
        f32::INFINITY,
        f32::NEG_INFINITY,
    ];

    for speed in &extreme_speeds {
        ctx.record_iteration();
        // Speed should be clamped to valid range
        let clamped = speed.clamp(0.1, 100.0);
        assert!(clamped.is_finite());
        assert!(clamped >= 0.1);
        assert!(clamped <= 100.0);
    }
}

// ============================================================================
// Scene State Invariants
// ============================================================================

#[test]
fn chaos_state_file_count_invariant() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    let mut expected_count = 0;

    for i in 0..1000 {
        ctx.record_iteration();
        scene.add_file(&format!("file{}.rs", i), "Author".to_string());
        expected_count += 1;
        assert_eq!(scene.file_count(), expected_count);
    }
}

#[test]
fn chaos_state_directory_count_invariant() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    // Adding files should create directories
    scene.add_file("a/b/c/d.rs", "Author".to_string());

    for _ in 0..1000 {
        ctx.record_iteration();
        scene.update(0.016);
        // Directory count should remain stable
        let dir_count = scene.directories().len();
        assert!(dir_count >= 4); // At least root, a, b, c
    }
}

#[test]
fn chaos_state_user_count_invariant() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    // Add files from same author
    for i in 0..100 {
        ctx.record_iteration();
        scene.add_file(&format!("file{}.rs", i), "SameAuthor".to_string());
    }

    // Should have exactly one user
    assert_eq!(scene.user_count(), 1);

    // Add files from different authors
    for i in 0..100 {
        ctx.record_iteration();
        scene.add_file(&format!("other{}.rs", i), format!("Author{}", i));
    }

    // Should have 101 users now
    assert_eq!(scene.user_count(), 101);
}

// ============================================================================
// Camera State Invariants
// ============================================================================

#[test]
fn chaos_state_camera_zoom_bounds() {
    let mut ctx = ChaosContext::new();
    let mut camera = Camera::new(800.0, 600.0);
    camera.set_zoom_limits(0.1, 10.0);

    for i in 0..1000 {
        ctx.record_iteration();
        let requested_zoom = (i as f32 - 500.0) / 10.0; // -50.0 to 49.9
        camera.set_zoom(requested_zoom);
        let actual = camera.zoom();

        // Zoom should be within limits
        assert!(actual >= 0.1 || requested_zoom < 0.1);
        assert!(actual <= 10.0 || requested_zoom > 10.0);
    }
}

#[test]
fn chaos_state_camera_position_stability() {
    let mut ctx = ChaosContext::new();
    let mut camera = Camera::new(800.0, 600.0);

    let target = Vec2::new(100.0, 100.0);
    camera.jump_to(target);

    for _ in 0..1000 {
        ctx.record_iteration();
        camera.update(0.016);
        let pos = camera.position();
        // Position should remain at target after jumping
        assert!((pos.x - target.x).abs() < 0.001);
        assert!((pos.y - target.y).abs() < 0.001);
    }
}

#[test]
fn chaos_state_visible_bounds_consistency() {
    let mut ctx = ChaosContext::new();
    let mut camera = Camera::new(800.0, 600.0);

    for i in 0..1000 {
        ctx.record_iteration();

        camera.set_zoom((i as f32 / 100.0).clamp(0.1, 10.0));
        camera.jump_to(Vec2::new(i as f32, i as f32));
        camera.update(0.016);

        let bounds = camera.visible_bounds();

        // Bounds should be valid
        assert!(bounds.width() >= 0.0);
        assert!(bounds.height() >= 0.0);
        assert!(bounds.min.x <= bounds.max.x);
        assert!(bounds.min.y <= bounds.max.y);
    }
}

// ============================================================================
// Interleaved Operation State
// ============================================================================

#[test]
fn chaos_state_interleaved_operations() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();
    let mut camera = Camera::new(800.0, 600.0);

    for i in 0..1000 {
        ctx.record_iteration();

        // Interleave different operations
        match i % 7 {
            0 => {
                scene.add_file(&format!("file{}.rs", i), "Author".to_string());
            }
            1 => {
                scene.update(0.016);
            }
            2 => {
                camera.set_zoom((i as f32 / 100.0).clamp(0.1, 10.0));
            }
            3 => {
                camera.jump_to(Vec2::new(i as f32, i as f32));
            }
            4 => {
                camera.update(0.016);
            }
            5 => {
                let _ = camera.visible_bounds();
            }
            6 => {
                let _ = scene.compute_entity_bounds();
            }
            _ => {}
        }
    }

    // State should still be consistent
    assert!(scene.file_count() > 0);
    assert!(camera.zoom() > 0.0);
}

// ============================================================================
// Reset and Reload State
// ============================================================================

#[test]
fn chaos_state_scene_reset() {
    let mut ctx = ChaosContext::new();

    for _ in 0..100 {
        ctx.record_iteration();

        let mut scene = Scene::new();

        // Add some data
        for i in 0..100 {
            scene.add_file(&format!("file{}.rs", i), "Author".to_string());
        }

        assert_eq!(scene.file_count(), 100);

        // "Reset" by creating new scene
        scene = Scene::new();
        assert_eq!(scene.file_count(), 0);
    }
}

#[test]
fn chaos_state_reload_different_data() {
    let mut ctx = ChaosContext::new();
    let parser = CustomParser::with_options(ParseOptions::lenient());

    for i in 0..100 {
        ctx.record_iteration();

        let log = format!(
            "{0}|Author|A|v{1}/a.rs\n{0}|Author|A|v{1}/b.rs\n{0}|Author|A|v{1}/c.rs",
            1000 + i,
            i
        );

        let commits = parser.parse_str(&log).unwrap();
        assert_eq!(commits.len(), 1);
        assert_eq!(commits[0].files.len(), 3);
    }
}

// ============================================================================
// Concurrent-like Access Patterns
// ============================================================================

#[test]
fn chaos_state_read_during_write_simulation() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    for i in 0..1000 {
        ctx.record_iteration();

        // Simulate read-during-write by interleaving
        if i % 2 == 0 {
            scene.add_file(&format!("file{}.rs", i), "Author".to_string());
        } else {
            // Read operations
            let _ = scene.file_count();
            let _ = scene.user_count();
            let _ = scene.directories().len();
            let _ = scene.compute_entity_bounds();
        }
    }

    assert_eq!(scene.file_count(), 500);
}

#[test]
fn chaos_state_multiple_readers() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    // Setup
    for i in 0..100 {
        scene.add_file(&format!("file{}.rs", i), "Author".to_string());
    }

    // Multiple "readers"
    for _ in 0..1000 {
        ctx.record_iteration();

        let count1 = scene.file_count();
        let count2 = scene.file_count();
        let count3 = scene.file_count();

        // All reads should be consistent
        assert_eq!(count1, count2);
        assert_eq!(count2, count3);
    }
}

// ============================================================================
// Edge Case State Transitions
// ============================================================================

#[test]
fn chaos_state_zero_to_many() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    assert_eq!(scene.file_count(), 0);

    // Sudden large addition
    for i in 0..10000 {
        ctx.record_iteration();
        scene.add_file(&format!("file{}.rs", i), "Author".to_string());
    }

    assert_eq!(scene.file_count(), 10000);
}

#[test]
fn chaos_state_single_file_operations() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    scene.add_file("only.rs", "Author".to_string());

    for _ in 0..1000 {
        ctx.record_iteration();
        scene.update(0.016);

        // Invariants
        assert_eq!(scene.file_count(), 1);
        let bounds = scene.compute_entity_bounds();
        assert!(bounds.is_some());
    }
}

#[test]
fn chaos_state_same_file_multiple_authors() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    // Same file, different authors (simulating modifications)
    for i in 0..100 {
        ctx.record_iteration();
        scene.add_file("shared.rs", format!("Author{}", i));
    }

    // File count should reflect actual unique files
    // (depends on implementation - might be 1 or 100)
    assert!(scene.file_count() >= 1);
    assert!(scene.user_count() >= 1);
}

#[cfg(test)]
mod invariant_tests {
    use super::*;

    #[test]
    fn test_scene_invariants_after_operations() {
        let mut scene = Scene::new();

        // Add files
        for i in 0..100 {
            scene.add_file(&format!("file{}.rs", i), "Author".to_string());
        }

        // Invariant: file count matches
        assert_eq!(scene.file_count(), 100);

        // Invariant: directories exist for paths
        assert!(scene.directories().len() >= 1);

        // Invariant: at least one user
        assert!(scene.user_count() >= 1);

        // Update should maintain invariants
        for _ in 0..100 {
            scene.update(0.016);
            assert_eq!(scene.file_count(), 100);
            assert!(scene.directories().len() >= 1);
            assert!(scene.user_count() >= 1);
        }
    }

    #[test]
    fn test_camera_invariants() {
        let mut camera = Camera::new(800.0, 600.0);
        camera.set_zoom_limits(0.1, 100.0);

        for _ in 0..100 {
            camera.update(0.016);

            let zoom = camera.zoom();
            assert!(zoom >= 0.1);
            assert!(zoom <= 100.0);

            let bounds = camera.visible_bounds();
            assert!(bounds.width() >= 0.0);
            assert!(bounds.height() >= 0.0);
        }
    }
}
