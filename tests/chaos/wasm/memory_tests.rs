//! Memory Pressure and Allocation Chaos Tests
//!
//! Tests behavior under memory pressure, large allocations,
//! and allocation patterns that might cause OOM or memory leaks.

use rource_core::camera::Camera;
use rource_core::scene::Scene;
use rource_math::Vec2;
use rource_vcs::parser::{CustomParser, ParseOptions, Parser};

use super::ChaosContext;

// ============================================================================
// Large Allocation Tests
// ============================================================================

#[test]
fn chaos_memory_large_commit_count() {
    let mut ctx = ChaosContext::new();
    let parser = CustomParser::with_options(ParseOptions::lenient());

    // Generate log with many commits
    let mut log = String::with_capacity(50_000_000);
    for i in 0..500_000 {
        log.push_str(&format!("{}|Author|A|src/file{}.rs\n", 1000000000 + i, i));
        ctx.record_iteration();
    }

    let result = parser.parse_str(&log);
    assert!(result.is_ok());
    let commits = result.unwrap();
    assert_eq!(commits.len(), 500_000);
}

#[test]
fn chaos_memory_large_file_count() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    // Add many files
    for i in 0..100_000 {
        ctx.record_iteration();
        scene.add_file(&format!("src/dir{}/file{}.rs", i / 1000, i), format!("Author{}", i % 100));
    }

    assert_eq!(scene.file_count(), 100_000);
}

#[test]
fn chaos_memory_deep_directory_tree() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    // Create deeply nested paths
    for depth in 1..=50 {
        ctx.record_iteration();
        let path: String = (0..depth).map(|d| format!("d{}", d)).collect::<Vec<_>>().join("/");
        scene.add_file(&format!("{}/file.rs", path), "Author".to_string());
    }

    assert!(scene.directories().len() > 50);
}

#[test]
fn chaos_memory_wide_directory_tree() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    // Create wide tree (many siblings)
    for i in 0..10_000 {
        ctx.record_iteration();
        scene.add_file(&format!("src/dir{}/file.rs", i), "Author".to_string());
    }

    // Should have 10,000 directories plus root
    assert!(scene.directories().len() >= 10_000);
}

#[test]
fn chaos_memory_long_file_names() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    // Files with very long names
    for i in 0..1000 {
        ctx.record_iteration();
        let long_name = format!("{}_file.rs", "a".repeat(500));
        scene.add_file(&format!("src/{}", long_name), "Author".to_string());
    }

    assert_eq!(scene.file_count(), 1000);
}

#[test]
fn chaos_memory_long_author_names() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    for i in 0..1000 {
        ctx.record_iteration();
        let long_author = format!("Author{}", "X".repeat(1000));
        scene.add_file(&format!("src/file{}.rs", i), long_author);
    }

    assert_eq!(scene.file_count(), 1000);
}

// ============================================================================
// Allocation Pattern Tests
// ============================================================================

#[test]
fn chaos_memory_allocation_churn() {
    let mut ctx = ChaosContext::new();

    // Rapid allocation/deallocation cycles
    for cycle in 0..100 {
        ctx.record_iteration();

        let mut scene = Scene::new();
        for i in 0..1000 {
            scene.add_file(&format!("cycle{}/file{}.rs", cycle, i), "Author".to_string());
        }

        // Scene goes out of scope, memory freed
        assert_eq!(scene.file_count(), 1000);
    }
}

#[test]
fn chaos_memory_incremental_growth() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    // Incremental growth tests reallocation behavior
    for batch in 0..100 {
        ctx.record_iteration();
        for i in 0..100 {
            scene.add_file(&format!("batch{}/file{}.rs", batch, i), "Author".to_string());
        }
        scene.update(0.016);
    }

    assert_eq!(scene.file_count(), 10_000);
}

#[test]
fn chaos_memory_visibility_buffer_stress() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    // Add many files
    for i in 0..10_000 {
        scene.add_file(&format!("src/file{}.rs", i), "Author".to_string());
    }

    // Stress visibility queries
    let camera = Camera::new(800.0, 600.0);
    for _ in 0..1000 {
        ctx.record_iteration();
        let bounds = camera.visible_bounds();
        // Query entities in bounds
        let mut dirs = Vec::new();
        let mut files = Vec::new();
        let mut users = Vec::new();
        scene.visible_entities_into(&bounds, &mut dirs, &mut files, &mut users);
    }
}

// ============================================================================
// Buffer Reuse Tests
// ============================================================================

#[test]
fn chaos_memory_buffer_reuse() {
    let mut ctx = ChaosContext::new();
    let mut scene = Scene::new();

    // Add files
    for i in 0..1000 {
        scene.add_file(&format!("src/file{}.rs", i), "Author".to_string());
    }

    let camera = Camera::new(800.0, 600.0);
    let bounds = camera.visible_bounds();

    // Reusable buffers
    let mut dirs = Vec::with_capacity(1024);
    let mut files = Vec::with_capacity(4096);
    let mut users = Vec::with_capacity(256);

    for _ in 0..10_000 {
        ctx.record_iteration();
        scene.visible_entities_into(&bounds, &mut dirs, &mut files, &mut users);
        // Buffers should be cleared and reused, not reallocated
    }

    // Capacity should not have grown excessively
    assert!(dirs.capacity() <= 2048);
    assert!(files.capacity() <= 8192);
    assert!(users.capacity() <= 512);
}

// ============================================================================
// Extreme Size Tests
// ============================================================================

#[test]
fn chaos_memory_million_file_simulation() {
    // Simulates behavior with 1M files without actually allocating them all
    let mut ctx = ChaosContext::new();
    let parser = CustomParser::with_options(ParseOptions::lenient());

    // Generate in chunks to avoid massive string allocation
    for chunk in 0..100 {
        ctx.record_iteration();
        let mut log = String::with_capacity(500_000);
        for i in 0..10_000 {
            let file_id = chunk * 10_000 + i;
            log.push_str(&format!("{}|Author|A|src/file{}.rs\n", 1000000000 + file_id, file_id));
        }
        let result = parser.parse_str(&log);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().len(), 10_000);
    }
}

#[test]
fn chaos_memory_concurrent_scene_instances() {
    let mut ctx = ChaosContext::new();

    // Multiple concurrent scene instances
    let mut scenes: Vec<Scene> = Vec::new();

    for i in 0..10 {
        ctx.record_iteration();
        let mut scene = Scene::new();
        for j in 0..1000 {
            scene.add_file(&format!("scene{}/file{}.rs", i, j), "Author".to_string());
        }
        scenes.push(scene);
    }

    // All scenes should be independent
    for (i, scene) in scenes.iter().enumerate() {
        assert_eq!(scene.file_count(), 1000, "Scene {} has wrong count", i);
    }
}

// ============================================================================
// Edge Case Sizes
// ============================================================================

#[test]
fn chaos_memory_single_file() {
    let mut scene = Scene::new();
    scene.add_file("single.rs", "Author".to_string());
    assert_eq!(scene.file_count(), 1);
    scene.update(0.016);
}

#[test]
fn chaos_memory_two_files_same_dir() {
    let mut scene = Scene::new();
    scene.add_file("src/a.rs", "Author".to_string());
    scene.add_file("src/b.rs", "Author".to_string());
    assert_eq!(scene.file_count(), 2);
}

#[test]
fn chaos_memory_zero_width_screen() {
    let camera = Camera::new(0.0, 600.0);
    let bounds = camera.visible_bounds();
    // Should not panic
    assert!(bounds.width() >= 0.0 || bounds.width().is_nan());
}

#[test]
fn chaos_memory_zero_height_screen() {
    let camera = Camera::new(800.0, 0.0);
    let bounds = camera.visible_bounds();
    // Should not panic
    assert!(bounds.height() >= 0.0 || bounds.height().is_nan());
}

// ============================================================================
// Stress Tests
// ============================================================================

#[test]
fn chaos_memory_rapid_scene_recreation() {
    let mut ctx = ChaosContext::new();

    for _ in 0..1000 {
        ctx.record_iteration();
        let mut scene = Scene::new();
        scene.add_file("test.rs", "Author".to_string());
        scene.update(0.016);
        drop(scene);
    }
}

#[test]
fn chaos_memory_camera_state_churn() {
    let mut ctx = ChaosContext::new();

    for _ in 0..1000 {
        ctx.record_iteration();
        let mut camera = Camera::new(800.0, 600.0);
        camera.set_zoom(1.0);
        camera.jump_to(Vec2::new(100.0, 100.0));
        camera.update(0.016);
        let _ = camera.visible_bounds();
        drop(camera);
    }
}

#[test]
fn chaos_memory_string_accumulation() {
    let mut ctx = ChaosContext::new();
    let parser = CustomParser::with_options(ParseOptions::lenient());

    // Test that parsing many logs doesn't accumulate memory
    for i in 0..1000 {
        ctx.record_iteration();
        let log = format!("{}|Author{}|A|path{}.rs", 1000000000 + i, i, i);
        let result = parser.parse_str(&log);
        assert!(result.is_ok());
        // Result goes out of scope, should be freed
    }
}

#[cfg(test)]
mod allocation_tests {
    use super::*;

    #[test]
    fn test_vec_capacity_behavior() {
        let mut v: Vec<i32> = Vec::new();

        // Track capacity growth
        let mut capacities = Vec::new();
        for i in 0..1000 {
            v.push(i);
            if v.capacity() != capacities.last().copied().unwrap_or(0) {
                capacities.push(v.capacity());
            }
        }

        // Capacity should grow in powers of 2 (roughly)
        assert!(capacities.len() < 15, "Too many reallocations: {:?}", capacities);
    }

    #[test]
    fn test_string_capacity_behavior() {
        let mut s = String::new();

        for _ in 0..10000 {
            s.push_str("hello");
        }

        // Should have grown capacity
        assert!(s.capacity() >= s.len());
    }
}
