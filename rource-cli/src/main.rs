// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Rource CLI - Native application entry point.
//!
//! This is the main entry point for the native Rource application.
//! It sets up the window using winit and displays the rendered output
//! using softbuffer.
//!
//! # Module Structure
//!
//! - `app`: Application state and playback management
//! - `args`: Command-line argument parsing
//! - `avatar`: User avatar loading and management
//! - `export`: Video and image export utilities
//! - `headless`: Headless rendering mode
//! - `helpers`: Utility functions
//! - `input`: Keyboard and mouse input handling
//! - `rendering`: Frame rendering for windowed mode
//! - `window`: Window management and event handling

// Allow multiple versions of dependencies from winit/softbuffer ecosystem
#![allow(clippy::multiple_crate_versions)]

mod app;
mod args;
mod avatar;
mod export;
mod headless;
mod helpers;
mod input;
mod rendering;
mod window;

use anyhow::Result;

use args::Args;
use headless::{run_headless, run_screenshot};
use window::run_windowed;

fn main() -> Result<()> {
    let mut args = Args::parse_args();

    // Handle --sample-config
    if args.sample_config {
        println!("{}", Args::sample_config());
        return Ok(());
    }

    // Handle --env-help
    if args.env_help {
        println!("{}", Args::env_help());
        return Ok(());
    }

    // Apply environment variables (priority: CLI > Env > Config)
    args.apply_env();

    // Apply config file if specified
    if let Err(e) = args.apply_config_file() {
        eprintln!("Warning: {e}");
    }

    // Validate all arguments after all sources have been applied
    if let Err(e) = args.validate() {
        anyhow::bail!("{e}");
    }

    // Handle --save-config
    if let Some(ref config_path) = args.save_config {
        let settings = args.to_settings();
        if let Err(e) = settings.save_to_file(config_path) {
            anyhow::bail!("Failed to save config to {}: {}", config_path.display(), e);
        }
        eprintln!("Configuration saved to: {}", config_path.display());
        return Ok(());
    }

    eprintln!("Rource - Software version control visualization");
    eprintln!("Repository: {}", args.path.display());
    eprintln!("Resolution: {}x{}", args.width, args.height);

    // Check for headless mode
    if args.headless {
        return run_headless(&args);
    }

    // Check for screenshot mode
    if let Some(ref screenshot_path) = args.screenshot {
        return run_screenshot(&args, screenshot_path);
    }

    // Run windowed mode
    run_windowed(args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::app::{App, PlaybackState};
    use crate::helpers::{format_timestamp, get_initials};
    use crate::input::{file_action_to_action_type, MouseState};
    use rource_core::scene::ActionType;
    use rource_math::Vec2;
    use rource_vcs::FileAction;
    use std::path::PathBuf;
    use winit::event::{ElementState, MouseButton, MouseScrollDelta};

    // =========================================================================
    // Helper function tests
    // =========================================================================

    #[test]
    fn test_format_timestamp() {
        // Jan 1, 2020 00:00:00 UTC
        #[allow(clippy::unreadable_literal)]
        let ts = 1577836800;
        let formatted = format_timestamp(ts);
        assert!(formatted.starts_with("20"));
    }

    #[test]
    fn test_get_initials() {
        assert_eq!(get_initials("John Doe"), "JD");
        assert_eq!(get_initials("Alice Smith"), "AS");
        assert_eq!(get_initials("Alice"), "A");
        assert_eq!(get_initials("bob"), "B");
        assert_eq!(get_initials("John Q Public"), "JP");
        assert_eq!(get_initials("Mary Jane Watson"), "MW");
        assert_eq!(get_initials("<john@example.com>"), "J");
        assert_eq!(get_initials("John Doe <john@example.com>"), "JD");
        assert_eq!(get_initials("  Alice  "), "A");
        assert_eq!(get_initials("  Bob Smith  "), "BS");
    }

    // =========================================================================
    // App state tests
    // =========================================================================

    #[test]
    fn test_playback_state_default() {
        let state = PlaybackState::default();
        assert!(!state.paused);
        assert!((state.speed - 1.0).abs() < 0.001);
        assert!((state.seconds_per_day - 10.0).abs() < 0.001);
    }

    #[test]
    fn test_file_action_to_action_type() {
        assert!(matches!(
            file_action_to_action_type(FileAction::Create),
            ActionType::Create
        ));
        assert!(matches!(
            file_action_to_action_type(FileAction::Modify),
            ActionType::Modify
        ));
        assert!(matches!(
            file_action_to_action_type(FileAction::Delete),
            ActionType::Delete
        ));
    }

    // =========================================================================
    // Screen visibility tests
    // =========================================================================

    #[inline]
    fn is_screen_visible(screen_pos: Vec2, viewport: (f32, f32)) -> bool {
        let margin = 50.0;
        let (w, h) = viewport;
        screen_pos.x >= -margin
            && screen_pos.x <= w + margin
            && screen_pos.y >= -margin
            && screen_pos.y <= h + margin
    }

    #[test]
    fn test_is_screen_visible() {
        let viewport = (800.0, 600.0);

        // Center should be visible
        assert!(is_screen_visible(Vec2::new(400.0, 300.0), viewport));

        // Corner should be visible
        assert!(is_screen_visible(Vec2::new(0.0, 0.0), viewport));

        // Just outside should still be visible (within margin)
        assert!(is_screen_visible(Vec2::new(-30.0, -30.0), viewport));

        // Far outside should not be visible
        assert!(!is_screen_visible(Vec2::new(-100.0, -100.0), viewport));
        assert!(!is_screen_visible(Vec2::new(1000.0, 1000.0), viewport));
    }

    // =========================================================================
    // Mouse state tests
    // =========================================================================

    #[test]
    fn test_mouse_state_initial() {
        let args = Args::default();
        let app = App::new(args);

        assert_eq!(app.mouse.position, Vec2::ZERO);
        assert!(!app.mouse.dragging);
        assert_eq!(app.mouse.last_position, Vec2::ZERO);
    }

    #[test]
    fn test_mouse_move_updates_position() {
        let mut mouse = MouseState::new();
        mouse.set_position(100.0, 200.0);

        assert_eq!(mouse.position.x, 100.0);
        assert_eq!(mouse.position.y, 200.0);
    }

    #[test]
    fn test_mouse_drag_pans_camera() {
        let args = Args::default();
        let mut app = App::new(args);

        // Start at origin
        app.camera.jump_to(Vec2::ZERO);
        let initial_pos = app.camera.target_position();

        // Start drag
        crate::input::handle_mouse_move(100.0, 100.0, &mut app.mouse, &mut app.camera, None, false);
        crate::input::handle_mouse_button(
            MouseButton::Left,
            ElementState::Pressed,
            &mut app.mouse,
            &mut app.camera,
            None,
            (800.0, 600.0),
            100,
            false,
        );
        assert!(app.mouse.dragging);

        // Move mouse (should pan)
        crate::input::handle_mouse_move(150.0, 150.0, &mut app.mouse, &mut app.camera, None, false);

        // Camera should have moved (pan inverts direction)
        assert_ne!(app.camera.target_position(), initial_pos);

        // End drag
        crate::input::handle_mouse_button(
            MouseButton::Left,
            ElementState::Released,
            &mut app.mouse,
            &mut app.camera,
            None,
            (800.0, 600.0),
            100,
            false,
        );
        assert!(!app.mouse.dragging);
    }

    #[test]
    fn test_mouse_scroll_zooms() {
        let args = Args::default();
        let mut app = App::new(args);

        app.camera.set_zoom(1.0);
        let initial_zoom = app.camera.target_zoom();

        // Scroll up (zoom in)
        crate::input::handle_mouse_scroll(
            MouseScrollDelta::LineDelta(0.0, 1.0),
            &app.mouse,
            &mut app.camera,
            None,
            false,
        );

        // Zoom should have increased
        assert!(app.camera.target_zoom() > initial_zoom);
    }

    #[test]
    fn test_mouse_input_disabled() {
        let args = Args {
            disable_input: true,
            ..Args::default()
        };
        let mut app = App::new(args);

        // Set initial state
        app.camera.jump_to(Vec2::ZERO);
        app.camera.set_zoom(1.0);
        let initial_pos = app.camera.target_position();
        let initial_zoom = app.camera.target_zoom();

        // Try to drag
        crate::input::handle_mouse_move(100.0, 100.0, &mut app.mouse, &mut app.camera, None, true);
        crate::input::handle_mouse_button(
            MouseButton::Left,
            ElementState::Pressed,
            &mut app.mouse,
            &mut app.camera,
            None,
            (800.0, 600.0),
            100,
            true,
        );
        crate::input::handle_mouse_move(200.0, 200.0, &mut app.mouse, &mut app.camera, None, true);

        // Camera should not have moved (input disabled)
        assert_eq!(app.camera.target_position(), initial_pos);
        assert!(!app.mouse.dragging);

        // Try to scroll
        crate::input::handle_mouse_scroll(
            MouseScrollDelta::LineDelta(0.0, 5.0),
            &app.mouse,
            &mut app.camera,
            None,
            true,
        );
        assert_eq!(app.camera.target_zoom(), initial_zoom);
    }

    #[test]
    fn test_middle_click_resets_camera() {
        let args = Args::default();
        let mut app = App::new(args);

        // Move camera
        app.camera.jump_to(Vec2::new(500.0, 500.0));
        app.camera.set_zoom(3.0);

        // Middle click
        crate::input::handle_mouse_button(
            MouseButton::Middle,
            ElementState::Pressed,
            &mut app.mouse,
            &mut app.camera,
            None,
            (800.0, 600.0),
            100,
            false,
        );

        // Camera should reset
        assert_eq!(app.camera.position(), Vec2::ZERO);
        assert!((app.camera.zoom() - 1.0).abs() < 0.01);
    }

    // =========================================================================
    // Headless mode tests
    // =========================================================================

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

    // =========================================================================
    // Frame exporter tests
    // =========================================================================

    #[test]
    fn test_frame_exporter_initialized_for_headless() {
        let args = Args {
            output: Some(PathBuf::from("-")),
            ..Args::default()
        };
        let app = App::new(args);
        assert!(app.frame_exporter.is_some());
    }

    #[test]
    fn test_frame_exporter_not_initialized_without_output() {
        let args = Args::default();
        let app = App::new(args);
        assert!(app.frame_exporter.is_none());
    }
}
