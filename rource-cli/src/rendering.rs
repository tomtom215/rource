//! Rendering logic for the Rource CLI windowed mode.
//!
//! This module provides frame rendering for the interactive windowed
//! visualization mode.

use rource_core::camera::Camera;
use rource_core::scene::{FileNode, Scene};
use rource_core::{DirId, FileId, UserId};
use rource_math::{Bounds, Color, Vec2};
use rource_render::effects::{BloomEffect, ShadowEffect};
use rource_render::{FontId, Renderer, SoftwareRenderer, TextureId};
use rource_vcs::Commit;

use crate::app::{App, PlaybackState};
use crate::args::Args;
use crate::avatar::AvatarRegistry;
use crate::helpers::get_initials;

/// Render a frame in windowed mode.
///
/// This function renders all scene entities, UI overlays, and applies
/// post-processing effects.
#[allow(clippy::too_many_lines)]
pub fn render_frame(app: &mut App) {
    let Some(renderer) = &mut app.renderer else {
        return;
    };

    renderer.begin_frame();

    // Clear to background color
    let bg_color = app.args.parse_background_color();
    renderer.clear(bg_color);

    // Draw background image if available
    if let Some(bg_texture) = app.background_texture {
        let viewport_bounds = Bounds::new(
            Vec2::ZERO,
            Vec2::new(renderer.width() as f32, renderer.height() as f32),
        );
        renderer.draw_quad(viewport_bounds, Some(bg_texture), Color::WHITE);
    }

    // Get camera's visible bounds for frustum culling
    let visible_bounds = app.camera.visible_bounds();
    let culling_bounds = Scene::expand_bounds_for_visibility(&visible_bounds, 100.0);

    // Query visible entities using spatial index
    let (visible_dir_ids, visible_file_ids, visible_user_ids) =
        app.scene.visible_entities(&culling_bounds);

    // Render directories
    render_directories(
        renderer,
        &app.scene,
        &app.camera,
        &visible_dir_ids,
        &app.args,
        app.default_font,
        app.dir_name_depth,
    );

    // Render files
    render_files(
        renderer,
        &app.scene,
        &app.camera,
        &visible_file_ids,
        &app.args,
        app.default_font,
    );

    // Render actions (beams)
    render_actions(renderer, &app.scene, &app.camera);

    // Render users
    render_users(
        renderer,
        &app.scene,
        &app.camera,
        &visible_user_ids,
        &app.args,
        app.default_font,
        &app.avatar_registry,
    );

    // Render UI overlays
    render_overlays(
        renderer,
        &app.playback,
        &app.args,
        app.default_font,
        &app.commits,
        app.current_commit,
        &app.scene,
        app.logo_texture,
        app.logo_dimensions,
        app.logo_offset,
    );

    renderer.end_frame();

    // Apply post-processing effects
    apply_effects(
        renderer,
        app.shadow.as_ref(),
        app.bloom.as_ref(),
        app.args.hide_bloom,
    );
}

/// Render directory entities.
fn render_directories(
    renderer: &mut SoftwareRenderer,
    scene: &Scene,
    camera: &Camera,
    visible_ids: &[DirId],
    args: &Args,
    font_id: Option<FontId>,
    dir_name_depth: u32,
) {
    let hide_root = args.hide_root;
    let hide_tree = args.hide_tree;
    let hide_dirnames = args.hide_dirnames;
    let dir_font_size = args.font_size * 0.75;

    for &dir_id in visible_ids {
        let Some(dir) = scene.directories().get(dir_id) else {
            continue;
        };

        if !dir.is_visible() {
            continue;
        }

        // Skip root directory if hide_root is set
        if hide_root && dir.depth() == 0 {
            continue;
        }

        let screen_pos = camera.world_to_screen(dir.position());
        let radius = dir.radius() * camera.zoom();

        // Draw directory as a hollow circle
        let depth_color = 0.15 + 0.05 * (dir.depth() as f32).min(5.0);
        let dir_color = Color::new(depth_color, depth_color, depth_color + 0.1, 0.5);
        renderer.draw_circle(screen_pos, radius, 1.0, dir_color);

        // Draw connection to parent (unless hide_tree is set)
        if !hide_tree {
            if let Some(parent_pos) = dir.parent_position() {
                let parent_screen = camera.world_to_screen(parent_pos);
                renderer.draw_line(parent_screen, screen_pos, 1.0, dir_color.with_alpha(0.3));
            }
        }

        // Draw directory name label if enabled and within depth limit
        if !hide_dirnames && dir.depth() <= dir_name_depth {
            if let Some(fid) = font_id {
                let name = dir.name();
                let label_pos = Vec2::new(
                    screen_pos.x + radius + 3.0,
                    screen_pos.y - dir_font_size * 0.3,
                );
                let label_color = Color::new(0.7, 0.7, 0.8, 0.6);
                renderer.draw_text(name, label_pos, fid, dir_font_size, label_color);
            }
        }
    }
}

/// Render file entities.
fn render_files(
    renderer: &mut SoftwareRenderer,
    scene: &Scene,
    camera: &Camera,
    visible_ids: &[FileId],
    args: &Args,
    font_id: Option<FontId>,
) {
    let show_filenames = !args.hide_filenames;
    let hide_tree = args.hide_tree;
    let file_font_size = args.font_size * 0.8;
    let camera_zoom = camera.zoom();

    for &file_id in visible_ids {
        let Some(file) = scene.get_file(file_id) else {
            continue;
        };

        if file.alpha() < 0.01 {
            continue;
        }

        let screen_pos = camera.world_to_screen(file.position());
        let radius = file.radius() * camera_zoom;
        let color = file.current_color().with_alpha(file.alpha());

        // Draw file as a filled disc
        renderer.draw_disc(screen_pos, radius.max(2.0), color);

        // Draw connection to parent directory
        if !hide_tree {
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

        // Draw filename label for prominent files when zoomed in
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
}

/// Render action beams (user to file connections).
fn render_actions(renderer: &mut SoftwareRenderer, scene: &Scene, camera: &Camera) {
    for action in scene.actions() {
        let user_opt = scene.get_user(action.user());
        let file_opt = scene.get_file(action.file());

        if let (Some(user), Some(file)) = (user_opt, file_opt) {
            let user_screen = camera.world_to_screen(user.position());
            let file_screen = camera.world_to_screen(file.position());
            let beam_end = user_screen.lerp(file_screen, action.progress());

            let beam_color = action.beam_color();
            renderer.draw_line(user_screen, beam_end, 2.0, beam_color);

            // Draw beam head
            let head_radius = 3.0 * camera.zoom();
            renderer.draw_disc(beam_end, head_radius.max(2.0), beam_color);
        }
    }
}

/// Render user entities.
#[allow(clippy::too_many_arguments)]
fn render_users(
    renderer: &mut SoftwareRenderer,
    scene: &Scene,
    camera: &Camera,
    visible_ids: &[UserId],
    args: &Args,
    font_id: Option<FontId>,
    avatar_registry: &AvatarRegistry,
) {
    let show_usernames = !args.hide_usernames;
    let name_font_size = args.font_size;

    for &user_id in visible_ids {
        let Some(user) = scene.get_user(user_id) else {
            continue;
        };

        if user.alpha() < 0.01 {
            continue;
        }

        let screen_pos = camera.world_to_screen(user.position());
        let radius = user.radius() * camera.zoom();
        let color = user.display_color();
        let effective_radius = radius.max(5.0);

        // Draw border/outline
        let border_color = Color::new(color.r * 0.4, color.g * 0.4, color.b * 0.4, color.a);
        renderer.draw_disc(screen_pos, effective_radius + 2.0, border_color);

        // Check for avatar texture
        if let Some(avatar_id) = avatar_registry.get_avatar_id(user.name()) {
            let half_size = effective_radius * 0.9;
            let bounds = Bounds::from_center_half_extents(screen_pos, Vec2::splat(half_size));
            let tint = Color::new(1.0, 1.0, 1.0, user.alpha());
            renderer.draw_quad(bounds, Some(avatar_id), tint);
        } else {
            // Draw user as a filled disc (no avatar)
            renderer.draw_disc(screen_pos, effective_radius, color);

            // Draw initials if the disc is large enough
            if effective_radius > 12.0 {
                if let Some(fid) = font_id {
                    let initials = get_initials(user.name());
                    let initial_font_size = (effective_radius * 0.8).clamp(8.0, 20.0);
                    let text_width = initials.len() as f32 * initial_font_size * 0.5;
                    let initial_pos = Vec2::new(
                        screen_pos.x - text_width * 0.5,
                        screen_pos.y - initial_font_size * 0.35,
                    );
                    let initial_color = Color::new(1.0, 1.0, 1.0, 0.9 * user.alpha());
                    renderer.draw_text(
                        &initials,
                        initial_pos,
                        fid,
                        initial_font_size,
                        initial_color,
                    );
                }
            }
        }

        // Draw highlight ring if active
        if user.is_active() {
            renderer.draw_circle(
                screen_pos,
                effective_radius * 1.3,
                2.0,
                color.with_alpha(0.5 * user.alpha()),
            );
        }

        // Draw username label
        if show_usernames {
            if let Some(fid) = font_id {
                let name = user.name();
                let label_pos = Vec2::new(
                    screen_pos.x + effective_radius + 5.0,
                    screen_pos.y - name_font_size * 0.3,
                );
                let label_color = Color::new(1.0, 1.0, 1.0, 0.8 * user.alpha());
                renderer.draw_text(name, label_pos, fid, name_font_size, label_color);
            }
        }
    }
}

/// Render UI overlays (progress bar, stats, legend, etc.).
#[allow(clippy::too_many_arguments)]
fn render_overlays(
    renderer: &mut SoftwareRenderer,
    playback: &PlaybackState,
    args: &Args,
    font_id: Option<FontId>,
    commits: &[Commit],
    current_commit: usize,
    scene: &Scene,
    logo_texture: Option<TextureId>,
    logo_dimensions: Option<(u32, u32)>,
    logo_offset: (i32, i32),
) {
    let width = renderer.width() as f32;
    let height = renderer.height() as f32;

    // Draw pause indicator
    if playback.paused {
        let pause_color = Color::new(1.0, 1.0, 1.0, 0.7);
        renderer.draw_quad(
            Bounds::new(Vec2::new(20.0, 20.0), Vec2::new(28.0, 40.0)),
            None,
            pause_color,
        );
        renderer.draw_quad(
            Bounds::new(Vec2::new(34.0, 20.0), Vec2::new(42.0, 40.0)),
            None,
            pause_color,
        );
    }

    // Draw progress bar
    if !args.hide_progress && !commits.is_empty() {
        render_progress_bar(renderer, current_commit, commits.len(), width, height);
    }

    // Draw stats indicators
    render_stats_indicators(renderer, scene, current_commit, commits.len());

    // Draw text overlays
    if let Some(fid) = font_id {
        render_text_overlays(
            renderer,
            playback,
            args,
            fid,
            commits,
            current_commit,
            scene,
        );
    }

    // Draw file extension legend
    if !args.hide_legend {
        if let Some(fid) = font_id {
            render_legend(renderer, scene, fid, args.font_size, width, height);
        }
    }

    // Draw logo
    if let (Some(logo_tex), Some((logo_w, logo_h))) = (logo_texture, logo_dimensions) {
        render_logo(renderer, logo_tex, logo_w, logo_h, logo_offset, width);
    }
}

/// Render progress bar at bottom of screen.
fn render_progress_bar(
    renderer: &mut SoftwareRenderer,
    current_commit: usize,
    total_commits: usize,
    width: f32,
    height: f32,
) {
    let bar_height = 4.0;
    let progress = current_commit as f32 / total_commits.max(1) as f32;

    // Background bar
    renderer.draw_quad(
        Bounds::new(
            Vec2::new(0.0, height - bar_height),
            Vec2::new(width, height),
        ),
        None,
        Color::new(0.2, 0.2, 0.2, 0.5),
    );

    // Progress bar
    renderer.draw_quad(
        Bounds::new(
            Vec2::new(0.0, height - bar_height),
            Vec2::new(width * progress, height),
        ),
        None,
        Color::new(0.3, 0.6, 1.0, 0.8),
    );
}

/// Render stats indicators in corner.
fn render_stats_indicators(
    renderer: &mut SoftwareRenderer,
    scene: &Scene,
    current_commit: usize,
    total_commits: usize,
) {
    let stats_color = Color::new(1.0, 1.0, 1.0, 0.6);
    let file_count = scene.file_count();
    let user_count = scene.user_count();

    let indicator_height = 8.0;
    let max_width = 100.0;

    // Commit progress indicator
    if total_commits > 0 {
        let progress = current_commit as f32 / total_commits as f32;
        renderer.draw_quad(
            Bounds::new(
                Vec2::new(10.0, 50.0),
                Vec2::new(10.0 + max_width * progress, 50.0 + indicator_height),
            ),
            None,
            stats_color,
        );
    }

    // File count indicator (logarithmic scale)
    if file_count > 0 {
        let file_bar = ((file_count as f32).ln() / 10.0).min(1.0);
        renderer.draw_quad(
            Bounds::new(
                Vec2::new(10.0, 62.0),
                Vec2::new(10.0 + max_width * file_bar, 62.0 + indicator_height),
            ),
            None,
            Color::new(0.3, 1.0, 0.3, 0.6),
        );
    }

    // User count indicator
    if user_count > 0 {
        let user_bar = ((user_count as f32).ln() / 5.0).min(1.0);
        renderer.draw_quad(
            Bounds::new(
                Vec2::new(10.0, 74.0),
                Vec2::new(10.0 + max_width * user_bar, 74.0 + indicator_height),
            ),
            None,
            Color::new(1.0, 0.6, 0.3, 0.6),
        );
    }
}

/// Render text overlays (title, date, stats).
#[allow(clippy::too_many_arguments)]
fn render_text_overlays(
    renderer: &mut SoftwareRenderer,
    playback: &PlaybackState,
    args: &Args,
    font_id: FontId,
    commits: &[Commit],
    current_commit: usize,
    scene: &Scene,
) {
    let font_size = args.font_size;
    let text_color = Color::new(1.0, 1.0, 1.0, 0.9);
    let height = renderer.height() as f32;
    let width = renderer.width() as f32;

    // Title (top-center)
    if let Some(ref title) = args.title {
        let title_size = font_size * 1.5;
        let title_x = (width / 2.0) - (title.len() as f32 * title_size * 0.3);
        renderer.draw_text(
            title,
            Vec2::new(title_x.max(10.0), 20.0),
            font_id,
            title_size,
            text_color,
        );
    }

    // Date display (bottom-left, above progress bar)
    if !args.hide_date && !commits.is_empty() {
        if let Some(commit) = commits.get(current_commit.saturating_sub(1).max(0)) {
            let date_str = crate::helpers::format_timestamp(commit.timestamp);
            renderer.draw_text(
                &date_str,
                Vec2::new(10.0, height - 30.0),
                font_id,
                font_size,
                text_color.with_alpha(0.7),
            );
        }
    }

    // Current commit info (bottom-left, above date)
    if current_commit > 0 {
        if let Some(commit) = commits.get(current_commit - 1) {
            // Author name
            renderer.draw_text(
                &commit.author,
                Vec2::new(10.0, height - 50.0),
                font_id,
                font_size,
                text_color.with_alpha(0.8),
            );

            // File count in commit
            let files_text = format!("{} files", commit.files.len());
            renderer.draw_text(
                &files_text,
                Vec2::new(10.0, height - 70.0),
                font_id,
                font_size * 0.9,
                text_color.with_alpha(0.6),
            );
        }
    }

    // Speed indicator (top-right, only if not 1.0x)
    if (playback.speed - 1.0).abs() > 0.01 {
        let speed_text = format!("{:.1}x", playback.speed);
        renderer.draw_text(
            &speed_text,
            Vec2::new(width - 60.0, 20.0),
            font_id,
            font_size,
            text_color.with_alpha(0.7),
        );
    }

    // Pause indicator text
    if playback.paused {
        renderer.draw_text(
            "PAUSED",
            Vec2::new(50.0, 24.0),
            font_id,
            font_size,
            text_color.with_alpha(0.7),
        );
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
        Vec2::new(120.0, 54.0),
        font_id,
        font_size * 0.8,
        text_color.with_alpha(0.5),
    );
}

/// Render file extension legend.
fn render_legend(
    renderer: &mut SoftwareRenderer,
    scene: &Scene,
    font_id: FontId,
    font_size: f32,
    width: f32,
    height: f32,
) {
    let text_color = Color::new(1.0, 1.0, 1.0, 0.9);
    let legend_font_size = font_size * 0.8;
    let legend_padding = 10.0;
    let legend_entry_height = legend_font_size + 4.0;
    let legend_color_size = legend_font_size * 0.7;

    // Get file extension stats (limited to top 10)
    let stats = scene.file_extension_stats();
    let max_legend_entries = 10;
    let legend_entries: Vec<_> = stats.into_iter().take(max_legend_entries).collect();

    if legend_entries.is_empty() {
        return;
    }

    let legend_height = legend_entries.len() as f32 * legend_entry_height + legend_padding * 2.0;
    let legend_width = 120.0;
    let legend_x = width - legend_width - legend_padding;
    let legend_y = height - legend_height - 20.0;

    // Background
    renderer.draw_quad(
        Bounds::new(
            Vec2::new(legend_x, legend_y),
            Vec2::new(legend_x + legend_width, legend_y + legend_height),
        ),
        None,
        Color::new(0.0, 0.0, 0.0, 0.5),
    );

    // Title
    renderer.draw_text(
        "File Types",
        Vec2::new(legend_x + legend_padding, legend_y + legend_padding),
        font_id,
        legend_font_size,
        text_color.with_alpha(0.8),
    );

    // Entries
    for (i, (ext, count)) in legend_entries.iter().enumerate() {
        let entry_y = legend_y + legend_padding + legend_entry_height * (i as f32 + 1.0);

        // Color swatch
        let ext_color = FileNode::color_from_extension(ext);
        renderer.draw_quad(
            Bounds::new(
                Vec2::new(legend_x + legend_padding, entry_y + 2.0),
                Vec2::new(
                    legend_x + legend_padding + legend_color_size,
                    entry_y + 2.0 + legend_color_size,
                ),
            ),
            None,
            ext_color,
        );

        // Extension name and count
        let ext_display = if ext.len() > 8 {
            format!("{}..", &ext[..6])
        } else {
            ext.clone()
        };
        let entry_text = format!("{ext_display} ({count})");
        renderer.draw_text(
            &entry_text,
            Vec2::new(legend_x + legend_padding + legend_color_size + 4.0, entry_y),
            font_id,
            legend_font_size * 0.9,
            text_color.with_alpha(0.7),
        );
    }
}

/// Render logo in top-right corner.
fn render_logo(
    renderer: &mut SoftwareRenderer,
    texture: TextureId,
    logo_width: u32,
    logo_height: u32,
    offset: (i32, i32),
    viewport_width: f32,
) {
    let (offset_x, offset_y) = offset;
    let logo_x = viewport_width - logo_width as f32 - offset_x as f32;
    let logo_y = offset_y as f32;

    let logo_bounds = Bounds::new(
        Vec2::new(logo_x, logo_y),
        Vec2::new(logo_x + logo_width as f32, logo_y + logo_height as f32),
    );
    renderer.draw_quad(logo_bounds, Some(texture), Color::WHITE);
}

/// Apply post-processing effects.
fn apply_effects(
    renderer: &mut SoftwareRenderer,
    shadow: Option<&ShadowEffect>,
    bloom: Option<&BloomEffect>,
    hide_bloom: bool,
) {
    let w = renderer.width() as usize;
    let h = renderer.height() as usize;

    // Apply shadow effect if enabled
    if let Some(shadow_effect) = shadow {
        shadow_effect.apply(renderer.pixels_mut(), w, h);
    }

    // Apply bloom effect if enabled
    if !hide_bloom {
        if let Some(bloom_effect) = bloom {
            bloom_effect.apply(renderer.pixels_mut(), w, h);
        }
    }
}

/// Present the rendered frame to the window.
pub fn present_frame(app: &mut App) {
    let Some(renderer) = &app.renderer else {
        return;
    };
    let Some(surface) = &mut app.surface else {
        return;
    };

    let width = renderer.width();
    let height = renderer.height();

    // Get the softbuffer buffer
    let mut buffer = match surface.buffer_mut() {
        Ok(b) => b,
        Err(e) => {
            eprintln!("Failed to get surface buffer: {e}");
            return;
        }
    };

    // Copy renderer pixels to softbuffer
    let pixels = renderer.pixels();
    let buffer_len = (width * height) as usize;

    if buffer.len() >= buffer_len && pixels.len() >= buffer_len {
        buffer[..buffer_len].copy_from_slice(&pixels[..buffer_len]);
    }

    // Present the buffer
    if let Err(e) = buffer.present() {
        eprintln!("Failed to present buffer: {e}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_initials() {
        assert_eq!(get_initials("John Doe"), "JD");
        assert_eq!(get_initials("Alice"), "A");
    }
}
