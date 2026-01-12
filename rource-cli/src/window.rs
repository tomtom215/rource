//! Window management and event handling for Rource CLI.
//!
//! This module provides the `ApplicationHandler` implementation for winit,
//! handling window creation, event processing, and the main render loop.

use std::num::NonZeroU32;
use std::rc::Rc;
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use rource_core::scene::{ActionType, Scene};
use rource_render::{Renderer, SoftwareRenderer};
use rource_vcs::{Commit, CustomParser, GitParser, Parser};
use winit::application::ApplicationHandler;
use winit::dpi::{LogicalSize, PhysicalSize};
use winit::event::WindowEvent;
use winit::event_loop::{ActiveEventLoop, ControlFlow, EventLoop};
use winit::keyboard::{Key, NamedKey};
use winit::window::{Window, WindowId};

use crate::app::App;
use crate::args::Args;
use crate::export;
use crate::input::{
    cycle_to_next_user, file_action_to_action_type, handle_key, handle_mouse_button,
    handle_mouse_move, handle_mouse_scroll,
};
use crate::rendering::{present_frame, render_frame};

/// Load commits from the repository or log file.
pub fn load_commits(args: &Args) -> Result<Vec<Commit>> {
    use std::process::Command;

    let path = &args.path;

    if args.custom_log {
        let content = std::fs::read_to_string(path).context("Failed to read custom log file")?;
        let parser = CustomParser::new();
        parser
            .parse_str(&content)
            .context("Failed to parse custom log")
    } else {
        let output = Command::new("git")
            .arg("-C")
            .arg(path)
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

/// Handle window resize event.
pub fn handle_resize(app: &mut App, size: PhysicalSize<u32>) {
    if size.width == 0 || size.height == 0 {
        return;
    }

    // Resize the softbuffer surface
    if let Some(surface) = &mut app.surface {
        let _ = surface.resize(
            NonZeroU32::new(size.width).unwrap(),
            NonZeroU32::new(size.height).unwrap(),
        );
    }

    // Resize the renderer
    if let Some(renderer) = &mut app.renderer {
        renderer.resize(size.width, size.height);
    }

    // Resize camera viewport
    app.camera
        .set_viewport_size(size.width as f32, size.height as f32);

    // Resize 3D camera if enabled
    if let Some(ref mut camera_3d) = app.camera_3d {
        camera_3d.set_viewport_size(size.width as f32, size.height as f32);
    }
}

/// Apply pending commits from `last_applied_commit` to `current_commit`.
pub fn apply_pending_commits(app: &mut App) {
    while app.last_applied_commit < app.current_commit {
        let commit = &app.commits[app.last_applied_commit];

        // Skip commits from filtered-out users
        if !app.filter.should_include_user(&commit.author) {
            app.last_applied_commit += 1;
            continue;
        }

        // Convert commit files to scene format, filtering out hidden files
        let files: Vec<(std::path::PathBuf, ActionType)> = commit
            .files
            .iter()
            .filter(|f| app.filter.should_include_file(&f.path))
            .map(|f| (f.path.clone(), file_action_to_action_type(f.action)))
            .collect();

        // Only apply commit if there are files left after filtering
        if !files.is_empty() {
            app.scene.apply_commit(&commit.author, &files);
        }

        app.last_applied_commit += 1;
    }
}

/// Seek to a specific commit index.
///
/// Resets the scene and re-applies commits if seeking backwards.
pub fn seek_to_commit(app: &mut App, target: usize) {
    let target = target.min(app.commits.len());

    // If seeking backwards, reset scene and re-apply
    if target < app.current_commit {
        app.scene = Scene::new();
        app.last_applied_commit = 0;
        app.accumulated_time = 0.0;

        // Apply commits up to target
        for (i, commit) in app.commits.iter().take(target).enumerate() {
            let files: Vec<(std::path::PathBuf, ActionType)> = commit
                .files
                .iter()
                .map(|f| (f.path.clone(), file_action_to_action_type(f.action)))
                .collect();

            app.scene.apply_commit(&commit.author, &files);
            app.last_applied_commit = i + 1;
        }

        // Update scene to let things settle
        for _ in 0..5 {
            app.scene.update(0.1);
        }
    }

    app.current_commit = target;

    // Calculate appropriate accumulated time
    if !app.commits.is_empty() && target > 0 && target <= app.commits.len() {
        let first_timestamp = app.commits[0].timestamp;
        let target_timestamp = app.commits[target.saturating_sub(1)].timestamp;
        let days = (target_timestamp - first_timestamp) as f64 / 86400.0;
        app.accumulated_time = days * f64::from(app.playback.seconds_per_day);
    }

    // Fit camera to content
    if let Some(bounds) = app.scene.compute_entity_bounds() {
        if bounds.is_valid() && bounds.width() > 0.0 && bounds.height() > 0.0 {
            app.camera.fit_to_bounds(&bounds, 100.0);
        }
    }
}

/// Update user highlight states based on settings.
fn update_user_highlights(app: &mut App) {
    let user_ids: Vec<_> = app
        .scene
        .users()
        .values()
        .map(rource_core::scene::User::id)
        .collect();
    for user_id in user_ids {
        if let Some(user) = app.scene.get_user_mut(user_id) {
            let should_highlight = if app.highlight_all_users {
                true
            } else if !app.highlight_users.is_empty() {
                app.highlight_users.iter().any(|name| name == user.name())
            } else {
                false
            };
            user.set_highlighted(should_highlight);
        }
    }
}

/// Update the visualization state.
pub fn update(app: &mut App, dt: f64) {
    // Always update scene and camera
    let dt_f32 = dt as f32;
    app.scene.update(dt_f32);
    app.camera.update(dt_f32);

    // Update 3D camera if enabled
    if let Some(ref mut camera_3d) = app.camera_3d {
        camera_3d.update(dt_f32);
    }

    // Track elapsed real time
    app.playback.elapsed_time += dt_f32;

    // Check stop_at_time
    if let Some(stop_time) = app.playback.stop_at_time {
        if app.playback.elapsed_time >= stop_time {
            app.should_exit = true;
            return;
        }
    }

    // Update user highlighting
    update_user_highlights(app);

    if app.playback.paused || app.commits.is_empty() {
        return;
    }

    // Apply time_scale multiplier to speed
    let effective_speed = app.playback.speed * app.playback.time_scale;
    app.accumulated_time += dt * f64::from(effective_speed);

    // Calculate how many days have passed
    let days_per_second = if app.playback.realtime {
        1.0 / 86400.0
    } else {
        1.0 / f64::from(app.playback.seconds_per_day)
    };
    let days_elapsed = app.accumulated_time * days_per_second;

    // Find the current commit based on elapsed time
    if let Some(first) = app.commits.first() {
        let first_time = first.timestamp;
        let target_time = first_time + (days_elapsed * 86400.0) as i64;

        while app.current_commit + 1 < app.commits.len() {
            if app.commits[app.current_commit + 1].timestamp <= target_time {
                app.current_commit += 1;
            } else {
                break;
            }
        }
    }

    // Apply any commits we've reached
    apply_pending_commits(app);

    // Camera behavior based on follow_user setting
    if let Some(ref follow_name) = app.follow_user {
        let target_pos = app
            .scene
            .users()
            .values()
            .find(|u| u.name() == follow_name)
            .map(rource_core::scene::User::position);
        if let Some(pos) = target_pos {
            app.camera.jump_to(pos);
        }
    } else {
        // Auto-fit camera to scene content
        if let Some(entity_bounds) = app.scene.compute_entity_bounds() {
            app.camera.fit_to_bounds(&entity_bounds, 100.0);
        }
    }

    // Loop if enabled
    if app.args.loop_playback && app.current_commit >= app.commits.len().saturating_sub(1) {
        app.current_commit = 0;
        app.last_applied_commit = 0;
        app.accumulated_time = 0.0;
        app.scene = Scene::new();
    }
}

impl ApplicationHandler for App {
    #[allow(clippy::too_many_lines)]
    fn resumed(&mut self, event_loop: &ActiveEventLoop) {
        // Create window
        let window_attrs = Window::default_attributes()
            .with_title("Rource")
            .with_inner_size(LogicalSize::new(self.args.width, self.args.height));

        let window = match event_loop.create_window(window_attrs) {
            Ok(w) => Rc::new(w),
            Err(e) => {
                eprintln!("Failed to create window: {e}");
                event_loop.exit();
                return;
            }
        };

        // Create softbuffer surface
        let context = match softbuffer::Context::new(window.clone()) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Failed to create softbuffer context: {e}");
                event_loop.exit();
                return;
            }
        };

        let mut surface = match softbuffer::Surface::new(&context, window.clone()) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Failed to create softbuffer surface: {e}");
                event_loop.exit();
                return;
            }
        };

        // Initialize surface size
        let size = window.inner_size();
        if size.width > 0 && size.height > 0 {
            let _ = surface.resize(
                NonZeroU32::new(size.width).unwrap(),
                NonZeroU32::new(size.height).unwrap(),
            );
        }

        // Create renderer
        let mut renderer = SoftwareRenderer::new(size.width.max(1), size.height.max(1));

        // Load default font for text rendering
        let font_id = renderer.load_font(rource_render::default_font::ROBOTO_MONO);
        if font_id.is_none() {
            eprintln!("Warning: Failed to load default font");
        }

        // Register avatars with renderer
        if let Some(manager) = self.avatar_manager.take() {
            self.avatar_registry = manager.register_with_renderer(&mut renderer);
        }

        // Load logo image if specified
        if let Some(ref logo_path) = self.logo_path {
            match rource_render::image::Image::load_file(logo_path) {
                Ok(image) => {
                    let width = image.width();
                    let height = image.height();
                    let texture_id = renderer.load_texture(width, height, image.data());
                    self.logo_texture = Some(texture_id);
                    self.logo_dimensions = Some((width, height));
                    eprintln!(
                        "Loaded logo: {}x{} from {}",
                        width,
                        height,
                        logo_path.display()
                    );
                }
                Err(e) => {
                    eprintln!(
                        "Warning: Failed to load logo image '{}': {}",
                        logo_path.display(),
                        e
                    );
                }
            }
        }

        // Load background image if specified
        if let Some(ref bg_path) = self.background_image_path {
            match rource_render::image::Image::load_file(bg_path) {
                Ok(image) => {
                    let width = image.width();
                    let height = image.height();
                    let texture_id = renderer.load_texture(width, height, image.data());
                    self.background_texture = Some(texture_id);
                    eprintln!(
                        "Loaded background: {}x{} from {}",
                        width,
                        height,
                        bg_path.display()
                    );
                }
                Err(e) => {
                    eprintln!(
                        "Warning: Failed to load background image '{}': {}",
                        bg_path.display(),
                        e
                    );
                }
            }
        }

        self.window = Some(window);
        self.surface = Some(surface);
        self.renderer = Some(renderer);
        self.default_font = font_id;
        self.last_frame = Instant::now();

        // Load commits
        match load_commits(&self.args) {
            Ok(mut commits) => {
                commits.sort_by_key(|c| c.timestamp);
                self.commits = commits;
                if !self.commits.is_empty() {
                    eprintln!(
                        "Loaded {} commits from {}",
                        self.commits.len(),
                        self.args.path.display()
                    );
                }
            }
            Err(e) => {
                eprintln!("Warning: {e}");
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn window_event(&mut self, event_loop: &ActiveEventLoop, _id: WindowId, event: WindowEvent) {
        match event {
            WindowEvent::CloseRequested => {
                event_loop.exit();
            }
            WindowEvent::Resized(size) => {
                handle_resize(self, size);
            }
            WindowEvent::KeyboardInput { event, .. } => {
                // Handle Tab key for user cycling
                if event.state == winit::event::ElementState::Pressed
                    && matches!(&event.logical_key, Key::Named(NamedKey::Tab))
                    && !self.args.disable_input
                {
                    self.current_user_index =
                        cycle_to_next_user(&self.scene, &mut self.camera, self.current_user_index);
                    return;
                }

                let should_exit = handle_key(
                    &event,
                    &mut self.playback,
                    &mut self.scene,
                    &mut self.camera,
                    self.camera_3d.as_mut(),
                    &mut self.current_commit,
                    &mut self.last_applied_commit,
                    &mut self.accumulated_time,
                    self.commits.len(),
                    &mut self.screenshot_pending,
                    self.args.disable_input,
                );
                if should_exit {
                    self.should_exit = true;
                    event_loop.exit();
                }
            }
            WindowEvent::MouseInput { state, button, .. } => {
                let viewport = self.viewport_size().unwrap_or((800.0, 600.0));
                let seek_target = handle_mouse_button(
                    button,
                    state,
                    &mut self.mouse,
                    &mut self.camera,
                    self.camera_3d.as_mut(),
                    viewport,
                    self.commits.len(),
                    self.args.disable_input,
                );
                if let Some(target) = seek_target {
                    seek_to_commit(self, target);
                }
            }
            WindowEvent::CursorMoved { position, .. } => {
                handle_mouse_move(
                    position.x,
                    position.y,
                    &mut self.mouse,
                    &mut self.camera,
                    self.camera_3d.as_mut(),
                    self.args.disable_input,
                );
            }
            WindowEvent::MouseWheel { delta, .. } => {
                handle_mouse_scroll(
                    delta,
                    &self.mouse,
                    &mut self.camera,
                    self.camera_3d.as_mut(),
                    self.args.disable_input,
                );
            }
            WindowEvent::RedrawRequested => {
                // Calculate delta time
                let now = Instant::now();
                let dt = now.duration_since(self.last_frame).as_secs_f64();
                self.last_frame = now;

                // Update and render
                update(self, dt);
                render_frame(self);

                // Save screenshot if pending
                if let Some(path) = self.screenshot_pending.take() {
                    if let Some(renderer) = &self.renderer {
                        let pixels = renderer.pixels();
                        let width = renderer.width();
                        let height = renderer.height();

                        match export::write_png_to_file(pixels, width, height, &path) {
                            Ok(()) => {
                                eprintln!("Screenshot saved: {}", path.display());
                            }
                            Err(e) => {
                                eprintln!("Failed to save screenshot: {e}");
                            }
                        }
                    }
                }

                // Export frame if in export mode
                if self.frame_exporter.is_some() {
                    if let Some(renderer) = &self.renderer {
                        let pixels = renderer.pixels();
                        let width = renderer.width();
                        let height = renderer.height();
                        let export_result = self
                            .frame_exporter
                            .as_mut()
                            .unwrap()
                            .export_frame(pixels, width, height, dt);

                        if let Err(e) = export_result {
                            eprintln!("Frame export error: {e}");
                            event_loop.exit();
                            return;
                        }
                    }

                    // Check if visualization is complete
                    let is_complete = self.is_complete();
                    if is_complete {
                        let frame_count = self.frame_exporter.as_ref().unwrap().frame_count();
                        eprintln!("Export complete: {frame_count} frames written");
                        event_loop.exit();
                        return;
                    }
                }

                present_frame(self);

                // Request next frame
                if let Some(window) = &self.window {
                    window.request_redraw();
                }
            }
            _ => {}
        }
    }

    fn about_to_wait(&mut self, event_loop: &ActiveEventLoop) {
        // Request redraw to keep animation running
        if let Some(window) = &self.window {
            window.request_redraw();
        }

        // Set frame rate limit
        event_loop.set_control_flow(ControlFlow::WaitUntil(
            Instant::now() + Duration::from_millis(16), // ~60 FPS
        ));
    }
}

/// Run the windowed application.
pub fn run_windowed(args: Args) -> Result<()> {
    let event_loop = EventLoop::new().context("Failed to create event loop")?;
    let mut app = App::new(args);
    event_loop.run_app(&mut app)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use rource_math::Vec2;
    use winit::event::{ElementState, MouseButton, MouseScrollDelta};

    #[test]
    fn test_app_mouse_state() {
        let args = Args::default();
        let app = App::new(args);
        assert_eq!(app.mouse.position, Vec2::ZERO);
        assert!(!app.mouse.dragging);
    }

    #[test]
    fn test_mouse_drag_interaction() {
        let args = Args::default();
        let mut app = App::new(args);

        // Start at origin
        app.camera.jump_to(Vec2::ZERO);
        let initial_pos = app.camera.target_position();

        // Start drag
        handle_mouse_move(100.0, 100.0, &mut app.mouse, &mut app.camera, None, false);
        let _ = handle_mouse_button(
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
        handle_mouse_move(150.0, 150.0, &mut app.mouse, &mut app.camera, None, false);

        // Camera should have moved
        assert_ne!(app.camera.target_position(), initial_pos);

        // End drag
        let _ = handle_mouse_button(
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
    fn test_mouse_scroll_zoom() {
        let args = Args::default();
        let mut app = App::new(args);

        app.camera.set_zoom(1.0);
        let initial_zoom = app.camera.target_zoom();

        // Scroll up (zoom in)
        handle_mouse_scroll(
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
    fn test_input_disabled() {
        let args = Args {
            disable_input: true,
            ..Args::default()
        };
        let mut app = App::new(args);

        app.camera.jump_to(Vec2::ZERO);
        app.camera.set_zoom(1.0);
        let initial_pos = app.camera.target_position();
        let initial_zoom = app.camera.target_zoom();

        // Try to drag (should be ignored)
        handle_mouse_move(100.0, 100.0, &mut app.mouse, &mut app.camera, None, true);
        let _ = handle_mouse_button(
            MouseButton::Left,
            ElementState::Pressed,
            &mut app.mouse,
            &mut app.camera,
            None,
            (800.0, 600.0),
            100,
            true,
        );
        handle_mouse_move(200.0, 200.0, &mut app.mouse, &mut app.camera, None, true);

        // Camera should not have moved
        assert_eq!(app.camera.target_position(), initial_pos);
        assert!(!app.mouse.dragging);

        // Try to scroll (should be ignored)
        handle_mouse_scroll(
            MouseScrollDelta::LineDelta(0.0, 5.0),
            &app.mouse,
            &mut app.camera,
            None,
            true,
        );
        assert_eq!(app.camera.target_zoom(), initial_zoom);
    }

    #[test]
    fn test_middle_click_reset() {
        let args = Args::default();
        let mut app = App::new(args);

        // Move camera
        app.camera.jump_to(Vec2::new(500.0, 500.0));
        app.camera.set_zoom(3.0);

        // Middle click
        let _ = handle_mouse_button(
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
}
