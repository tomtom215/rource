//! Chaos Tests for rource-core
//!
//! Comprehensive edge case and stress tests for the core library.

use std::path::Path;

use rource_core::camera::Camera;
use rource_core::scene::{ActionType, Scene};
use rource_math::Vec2;
use rource_vcs::parser::{CustomParser, ParseOptions, Parser};

/// Helper to add a file to the scene with an author
fn add_file(scene: &mut Scene, path: &str, author: &str) {
    scene.apply_commit(author, [(Path::new(path), ActionType::Create)]);
}

// ============================================================================
// Parse Edge Cases
// ============================================================================

#[test]
fn chaos_parse_empty_log() {
    let parser = CustomParser::with_options(ParseOptions::lenient());
    // Empty input may return an error or empty vec - both are valid
    // The key is that it should not panic
    let _ = parser.parse_str("");
}

#[test]
fn chaos_parse_whitespace_only() {
    let parser = CustomParser::with_options(ParseOptions::lenient());
    let inputs = ["   ", "\t\t\t", "\n\n\n", "  \n  \t  \n  "];

    for input in &inputs {
        // Whitespace-only input may return an error or empty vec - both are valid
        // The key is that it should not panic
        let _ = parser.parse_str(input);
    }
}

#[test]
fn chaos_parse_unicode() {
    let parser = CustomParser::with_options(ParseOptions::lenient());

    let unicode_logs = [
        "1234567890|作者|A|源代码.rs",
        "1234567890|著者|A|ソース.rs",
        "1234567890|저자|A|소스.rs",
        "1234567890|مؤلف|A|path.rs",
    ];

    for log in &unicode_logs {
        let result = parser.parse_str(log);
        assert!(result.is_ok(), "Failed on unicode input: {}", log);
    }
}

#[test]
fn chaos_parse_malformed_lines() {
    let parser = CustomParser::with_options(ParseOptions::lenient());

    let malformed = [
        "",
        "|",
        "||||",
        "no_delimiters",
        "1234567890|",
        "|Author|A|",
        "abc|Author|A|path",
        "-1|Author|A|path",
        "1234567890||A|path",
        "1234567890|Author|X|path",
    ];

    for line in &malformed {
        // Malformed input may return errors - that's fine
        // The key is that the parser should not panic
        let _ = parser.parse_str(line);
    }
}

#[test]
fn chaos_parse_large_log() {
    let parser = CustomParser::with_options(ParseOptions::lenient());

    let mut log = String::with_capacity(5_000_000);
    for i in 0..50_000 {
        log.push_str(&format!(
            "{}|Author{}|A|path/file{}.rs\n",
            1000000000 + i,
            i,
            i
        ));
    }

    let result = parser.parse_str(&log);
    assert!(result.is_ok());
    assert_eq!(result.unwrap().len(), 50_000);
}

// ============================================================================
// Scene Edge Cases
// ============================================================================

#[test]
fn chaos_scene_empty_operations() {
    let mut scene = Scene::new();

    // Operations on empty scene should not panic
    scene.update(0.016);
    scene.update(0.0);

    assert_eq!(scene.file_count(), 0);
    assert_eq!(scene.user_count(), 0);
    // Empty scene still has root directory, so bounds exist
    assert!(scene.compute_entity_bounds().is_some());
}

#[test]
fn chaos_scene_large_file_count() {
    let mut scene = Scene::new();

    for i in 0..10_000 {
        let path = format!("src/dir{}/file{}.rs", i / 100, i);
        let author = format!("Author{}", i % 50);
        add_file(&mut scene, &path, &author);
    }

    assert_eq!(scene.file_count(), 10_000);
    assert!(scene.user_count() <= 50);

    // Update should not panic
    for _ in 0..10 {
        scene.update(0.016);
    }
}

#[test]
fn chaos_scene_deep_directories() {
    let mut scene = Scene::new();

    // 50-level deep path
    let path: String =
        (0..50).map(|d| format!("d{}", d)).collect::<Vec<_>>().join("/") + "/file.rs";
    add_file(&mut scene, &path, "Author");

    assert_eq!(scene.file_count(), 1);
    assert!(scene.directories().len() >= 50);

    scene.update(0.016);
}

#[test]
fn chaos_scene_wide_directories() {
    let mut scene = Scene::new();

    // 1000 sibling directories
    for i in 0..1000 {
        let path = format!("src/component{}/main.rs", i);
        add_file(&mut scene, &path, "Author");
    }

    assert_eq!(scene.file_count(), 1000);
    assert!(scene.directories().len() >= 1000);

    scene.update(0.016);
}

#[test]
fn chaos_scene_rapid_updates() {
    let mut scene = Scene::new();
    add_file(&mut scene, "test.rs", "Author");

    // 1000 rapid updates with varying dt
    for i in 0..1000 {
        let dt = match i % 5 {
            0 => 0.0,
            1 => 0.001,
            2 => 0.016,
            3 => 0.1,
            _ => 1.0,
        };
        scene.update(dt);
    }

    assert_eq!(scene.file_count(), 1);
}

// ============================================================================
// Camera Edge Cases
// ============================================================================

#[test]
fn chaos_camera_extreme_zoom() {
    let mut camera = Camera::new(800.0, 600.0);

    let zooms = [0.001, 0.01, 0.1, 1.0, 10.0, 100.0, 1000.0];

    for zoom in &zooms {
        camera.set_zoom(*zoom);
        let actual = camera.zoom();
        assert!(actual.is_finite(), "Zoom became non-finite for {}", zoom);
    }
}

#[test]
fn chaos_camera_extreme_positions() {
    let mut camera = Camera::new(800.0, 600.0);

    let positions = [
        Vec2::ZERO,
        Vec2::new(1e6, 1e6),
        Vec2::new(-1e6, -1e6),
        Vec2::new(1e6, -1e6),
    ];

    for pos in &positions {
        camera.jump_to(*pos);
        let actual = camera.position();
        assert!(actual.x.is_finite());
        assert!(actual.y.is_finite());
    }
}

#[test]
fn chaos_camera_resize() {
    let mut camera = Camera::new(800.0, 600.0);

    let sizes = [
        (1.0, 1.0),
        (100.0, 100.0),
        (1920.0, 1080.0),
        (3840.0, 2160.0),
    ];

    for (w, h) in &sizes {
        camera.set_viewport_size(*w, *h);
        // Should not panic
    }
}

#[test]
fn chaos_camera_rapid_operations() {
    let mut camera = Camera::new(800.0, 600.0);

    for i in 0..1000 {
        match i % 4 {
            0 => camera.set_zoom((i as f32 / 100.0).clamp(0.1, 10.0)),
            1 => camera.jump_to(Vec2::new(i as f32, (i * 2) as f32)),
            2 => camera.set_viewport_size((i % 1000 + 100) as f32, (i % 800 + 100) as f32),
            _ => camera.update(0.016),
        }
    }

    let _ = camera.visible_bounds();
}

// ============================================================================
// Bounds Edge Cases
// ============================================================================

#[test]
fn chaos_bounds_empty_scene() {
    let mut scene = Scene::new();
    // Empty scene still has root directory, so bounds exist
    assert!(scene.compute_entity_bounds().is_some());
}

#[test]
fn chaos_bounds_single_file() {
    let mut scene = Scene::new();
    add_file(&mut scene, "only.rs", "Author");
    scene.update(0.016);

    let bounds = scene.compute_entity_bounds();
    assert!(bounds.is_some());

    let b = bounds.unwrap();
    assert!(b.width() > 0.0);
    assert!(b.height() > 0.0);
}

// ============================================================================
// Visibility Edge Cases
// ============================================================================

#[test]
fn chaos_visibility_queries() {
    let mut scene = Scene::new();

    for i in 0..100 {
        let path = format!("file{}.rs", i);
        add_file(&mut scene, &path, "Author");
    }
    scene.update(0.016);

    let camera = Camera::new(800.0, 600.0);
    let bounds = camera.visible_bounds();

    let mut dirs = Vec::new();
    let mut files = Vec::new();
    let mut users = Vec::new();

    // Should not panic
    scene.visible_entities_into(&bounds, &mut dirs, &mut files, &mut users);
}

// ============================================================================
// User Edge Cases
// ============================================================================

#[test]
fn chaos_same_author_many_files() {
    let mut scene = Scene::new();

    for i in 0..1000 {
        let path = format!("file{}.rs", i);
        add_file(&mut scene, &path, "SameAuthor");
    }

    assert_eq!(scene.file_count(), 1000);
    assert_eq!(scene.user_count(), 1);
}

#[test]
fn chaos_many_authors() {
    let mut scene = Scene::new();

    for i in 0..100 {
        let path = format!("file{}.rs", i);
        let author = format!("Author{}", i);
        add_file(&mut scene, &path, &author);
    }

    assert_eq!(scene.file_count(), 100);
    assert_eq!(scene.user_count(), 100);
}

// ============================================================================
// Interleaved Operations
// ============================================================================

#[test]
fn chaos_interleaved_operations() {
    let parser = CustomParser::with_options(ParseOptions::lenient());
    let mut scene = Scene::new();
    let mut camera = Camera::new(800.0, 600.0);

    for i in 0..500 {
        let log = format!("{}|Author{}|A|path{}.rs", 1000000000 + i, i, i);
        if let Ok(commits) = parser.parse_str(&log) {
            for commit in &commits {
                for file in &commit.files {
                    scene.apply_commit(
                        &commit.author,
                        [(file.path.as_path(), ActionType::Create)],
                    );
                }
            }
        }

        scene.update(0.016);
        camera.update(0.016);

        if i % 10 == 0 {
            camera.set_zoom((i as f32 / 50.0).clamp(0.1, 5.0));
        }
    }

    assert!(scene.file_count() >= 500);
}

// ============================================================================
// Memory Pattern Tests
// ============================================================================

#[test]
fn chaos_memory_scene_recreation() {
    for _ in 0..100 {
        let mut scene = Scene::new();
        for i in 0..100 {
            let path = format!("file{}.rs", i);
            add_file(&mut scene, &path, "Author");
        }
        scene.update(0.016);
        // Scene goes out of scope
    }
}

#[test]
fn chaos_memory_buffer_reuse() {
    let mut scene = Scene::new();
    for i in 0..100 {
        let path = format!("file{}.rs", i);
        add_file(&mut scene, &path, "Author");
    }
    scene.update(0.016);

    let camera = Camera::new(800.0, 600.0);
    let bounds = camera.visible_bounds();

    let mut dirs = Vec::with_capacity(64);
    let mut files = Vec::with_capacity(256);
    let mut users = Vec::with_capacity(32);

    // Reuse buffers many times
    for _ in 0..1000 {
        scene.visible_entities_into(&bounds, &mut dirs, &mut files, &mut users);
    }

    // Capacity should not have grown excessively
    assert!(dirs.capacity() <= 256);
    assert!(files.capacity() <= 1024);
    assert!(users.capacity() <= 128);
}

// ============================================================================
// Numeric Edge Cases
// ============================================================================

#[test]
fn chaos_numeric_dt_edge_cases() {
    let mut scene = Scene::new();
    add_file(&mut scene, "test.rs", "Author");

    // Various edge case dt values
    let edge_cases = [
        0.0,
        f32::EPSILON,
        f32::MIN_POSITIVE,
        0.0001,
        0.001,
        0.01,
        0.1,
        1.0,
        10.0,
        100.0,
    ];

    for dt in &edge_cases {
        scene.update(*dt);
        // Should not panic
    }
}

#[test]
fn chaos_numeric_camera_edge_cases() {
    let mut camera = Camera::new(800.0, 600.0);

    // Edge case values
    camera.set_zoom(f32::EPSILON);
    assert!(camera.zoom().is_finite());

    camera.set_zoom(f32::MIN_POSITIVE);
    assert!(camera.zoom().is_finite());
}

// ============================================================================
// Path Edge Cases
// ============================================================================

#[test]
fn chaos_path_with_dots() {
    let mut scene = Scene::new();

    let paths = [
        "file.rs",
        "file.test.rs",
        "file...rs",
        ".hidden",
        "...",
        "a/b/c.d.e.f",
    ];

    for path in &paths {
        add_file(&mut scene, path, "Author");
    }

    assert_eq!(scene.file_count(), paths.len());
}

#[test]
fn chaos_path_unicode() {
    let mut scene = Scene::new();

    let paths = ["日本語.rs", "中文.rs", "한국어.rs", "кириллица.rs"];

    for path in &paths {
        add_file(&mut scene, path, "Author");
    }

    assert_eq!(scene.file_count(), paths.len());
}

#[test]
fn chaos_path_special_chars() {
    let mut scene = Scene::new();

    let paths = [
        "file with spaces.rs",
        "file-with-dashes.rs",
        "file_with_underscores.rs",
        "UPPERCASE.RS",
        "MixedCase.Rs",
    ];

    for path in &paths {
        add_file(&mut scene, path, "Author");
    }

    assert_eq!(scene.file_count(), paths.len());
}
