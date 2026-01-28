// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Watermark rendering phase.
//!
//! Renders configurable watermark overlay on the visualization.

use rource_core::config::WatermarkSettings;
use rource_math::{Color, Vec2};
use rource_render::{FontId, Renderer};

use super::estimate_text_width;
use super::helpers::{compute_watermark_height, compute_watermark_position};

/// Renders the watermark overlay.
///
/// The watermark is positioned based on the `WatermarkSettings` and rendered
/// with the specified opacity and font size. It supports primary and secondary
/// text lines and can be placed in any corner of the screen.
#[inline(never)]
pub fn render_watermark<R: Renderer + ?Sized>(
    renderer: &mut R,
    watermark: &WatermarkSettings,
    font_id: Option<FontId>,
    width: f32,
    height: f32,
) {
    // Early out if watermark is disabled or has no text
    if !watermark.enabled || !watermark.has_text() {
        return;
    }

    let Some(font_id) = font_id else { return };

    let font_size = watermark.font_size;
    let margin = watermark.margin;
    let color = watermark.effective_color();

    // Estimate text widths for positioning
    let text_width = estimate_text_width(&watermark.text, font_size);
    let subtext_width = watermark
        .subtext
        .as_ref()
        .map_or(0.0, |s| estimate_text_width(s, font_size * 0.85));
    let max_text_width = text_width.max(subtext_width);

    // Calculate total height using pure function
    let has_subtext = watermark.subtext.is_some();
    let total_height = compute_watermark_height(font_size, has_subtext);
    let line_height = font_size * 1.2;
    let subtext_size = font_size * 0.85;

    // Calculate base position using pure function
    let (base_x, base_y) = compute_watermark_position(
        watermark.position,
        margin,
        max_text_width,
        total_height,
        width,
        height,
    );

    // Draw shadow for better readability
    let shadow_color = Color::new(0.0, 0.0, 0.0, color.a * 0.5);
    let shadow_offset = Vec2::new(1.0, 1.0);

    // Draw primary text
    if !watermark.text.is_empty() {
        let text_pos = Vec2::new(base_x, base_y);

        // Shadow
        renderer.draw_text(
            &watermark.text,
            text_pos + shadow_offset,
            font_id,
            font_size,
            shadow_color,
        );

        // Main text
        renderer.draw_text(&watermark.text, text_pos, font_id, font_size, color);
    }

    // Draw subtext if present
    if let Some(subtext) = &watermark.subtext {
        let subtext_y = base_y + line_height;
        let subtext_pos = Vec2::new(base_x, subtext_y);
        let subtext_color = color.with_alpha(color.a * 0.85);
        let subtext_shadow = shadow_color.with_alpha(shadow_color.a * 0.85);

        // Shadow
        renderer.draw_text(
            subtext,
            subtext_pos + shadow_offset,
            font_id,
            subtext_size,
            subtext_shadow,
        );

        // Main text
        renderer.draw_text(subtext, subtext_pos, font_id, subtext_size, subtext_color);
    }
}
