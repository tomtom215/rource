// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Watermark overlay settings.

use rource_math::Color;

/// Position for the watermark on screen.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum WatermarkPosition {
    /// Top-left corner.
    TopLeft,
    /// Top-right corner.
    TopRight,
    /// Bottom-left corner.
    BottomLeft,
    /// Bottom-right corner (default).
    #[default]
    BottomRight,
}

impl WatermarkPosition {
    /// Parse position from string.
    #[allow(clippy::should_implement_trait)]
    #[must_use]
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "top-left" | "topleft" | "tl" => Some(Self::TopLeft),
            "top-right" | "topright" | "tr" => Some(Self::TopRight),
            "bottom-left" | "bottomleft" | "bl" => Some(Self::BottomLeft),
            "bottom-right" | "bottomright" | "br" => Some(Self::BottomRight),
            _ => None,
        }
    }

    /// Convert to string representation.
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::TopLeft => "top-left",
            Self::TopRight => "top-right",
            Self::BottomLeft => "bottom-left",
            Self::BottomRight => "bottom-right",
        }
    }
}

/// Watermark configuration for branding and attribution.
///
/// The watermark can display text (such as project name and copyright)
/// overlaid on the visualization. It's designed to be non-invasive
/// while still being visible in screenshots and recordings.
#[derive(Debug, Clone)]
pub struct WatermarkSettings {
    /// Whether the watermark is enabled.
    pub enabled: bool,
    /// Primary text (e.g., "Rource").
    pub text: String,
    /// Secondary text, displayed on second line (e.g., "© Tom F").
    pub subtext: Option<String>,
    /// Position on screen.
    pub position: WatermarkPosition,
    /// Font size for primary text.
    pub font_size: f32,
    /// Opacity (0.0 = invisible, 1.0 = fully opaque).
    pub opacity: f32,
    /// Text color.
    pub color: Color,
    /// Margin from screen edge in pixels.
    pub margin: f32,
}

impl Default for WatermarkSettings {
    fn default() -> Self {
        Self {
            enabled: false,
            text: String::new(),
            subtext: None,
            position: WatermarkPosition::BottomRight,
            font_size: 14.0,
            opacity: 0.5,
            color: Color::WHITE,
            margin: 15.0,
        }
    }
}

impl WatermarkSettings {
    /// Creates a new watermark with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a simple watermark with just text.
    #[must_use]
    pub fn simple(text: impl Into<String>) -> Self {
        Self {
            enabled: true,
            text: text.into(),
            ..Default::default()
        }
    }

    /// Creates a watermark with primary and secondary text.
    #[must_use]
    pub fn with_subtext(text: impl Into<String>, subtext: impl Into<String>) -> Self {
        Self {
            enabled: true,
            text: text.into(),
            subtext: Some(subtext.into()),
            ..Default::default()
        }
    }

    /// Creates a branded watermark preset for Rource.
    #[must_use]
    pub fn rource_brand() -> Self {
        Self {
            enabled: true,
            text: "Rource".to_string(),
            subtext: Some("© Tom F".to_string()),
            position: WatermarkPosition::BottomRight,
            font_size: 14.0,
            opacity: 0.4,
            color: Color::WHITE,
            margin: 15.0,
        }
    }

    /// Builder: set enabled state.
    #[must_use]
    pub fn enabled(mut self, enabled: bool) -> Self {
        self.enabled = enabled;
        self
    }

    /// Builder: set primary text.
    #[must_use]
    pub fn text(mut self, text: impl Into<String>) -> Self {
        self.text = text.into();
        self
    }

    /// Builder: set secondary text.
    #[must_use]
    pub fn subtext(mut self, subtext: impl Into<String>) -> Self {
        self.subtext = Some(subtext.into());
        self
    }

    /// Builder: set position.
    #[must_use]
    pub fn position(mut self, position: WatermarkPosition) -> Self {
        self.position = position;
        self
    }

    /// Builder: set font size.
    #[must_use]
    pub fn font_size(mut self, size: f32) -> Self {
        self.font_size = size;
        self
    }

    /// Builder: set opacity.
    #[must_use]
    pub fn opacity(mut self, opacity: f32) -> Self {
        self.opacity = opacity.clamp(0.0, 1.0);
        self
    }

    /// Builder: set color.
    #[must_use]
    pub fn color(mut self, color: Color) -> Self {
        self.color = color;
        self
    }

    /// Builder: set margin.
    #[must_use]
    pub fn margin(mut self, margin: f32) -> Self {
        self.margin = margin;
        self
    }

    /// Returns the effective color with opacity applied.
    #[must_use]
    pub fn effective_color(&self) -> Color {
        self.color.with_alpha(self.opacity)
    }

    /// Returns whether there's any text to display.
    #[must_use]
    pub fn has_text(&self) -> bool {
        !self.text.is_empty() || self.subtext.is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_watermark_default() {
        let wm = WatermarkSettings::default();
        assert!(!wm.enabled);
        assert!(wm.text.is_empty());
        assert!(wm.subtext.is_none());
        assert_eq!(wm.position, WatermarkPosition::BottomRight);
    }

    #[test]
    fn test_watermark_simple() {
        let wm = WatermarkSettings::simple("Test");
        assert!(wm.enabled);
        assert_eq!(wm.text, "Test");
    }

    #[test]
    fn test_watermark_with_subtext() {
        let wm = WatermarkSettings::with_subtext("Rource", "© Tom F");
        assert!(wm.enabled);
        assert_eq!(wm.text, "Rource");
        assert_eq!(wm.subtext, Some("© Tom F".to_string()));
    }

    #[test]
    fn test_watermark_rource_brand() {
        let wm = WatermarkSettings::rource_brand();
        assert!(wm.enabled);
        assert_eq!(wm.text, "Rource");
        assert_eq!(wm.subtext, Some("© Tom F".to_string()));
        assert_eq!(wm.position, WatermarkPosition::BottomRight);
    }

    #[test]
    fn test_watermark_builder() {
        let wm = WatermarkSettings::new()
            .enabled(true)
            .text("Custom")
            .subtext("Text")
            .position(WatermarkPosition::TopLeft)
            .font_size(20.0)
            .opacity(0.8)
            .margin(25.0);

        assert!(wm.enabled);
        assert_eq!(wm.text, "Custom");
        assert_eq!(wm.subtext, Some("Text".to_string()));
        assert_eq!(wm.position, WatermarkPosition::TopLeft);
        assert!((wm.font_size - 20.0).abs() < 0.01);
        assert!((wm.opacity - 0.8).abs() < 0.01);
        assert!((wm.margin - 25.0).abs() < 0.01);
    }

    #[test]
    fn test_watermark_position_from_str() {
        assert_eq!(
            WatermarkPosition::from_str("bottom-right"),
            Some(WatermarkPosition::BottomRight)
        );
        assert_eq!(
            WatermarkPosition::from_str("BR"),
            Some(WatermarkPosition::BottomRight)
        );
        assert_eq!(
            WatermarkPosition::from_str("TopLeft"),
            Some(WatermarkPosition::TopLeft)
        );
        assert_eq!(WatermarkPosition::from_str("invalid"), None);
    }

    #[test]
    fn test_watermark_position_as_str() {
        assert_eq!(WatermarkPosition::BottomRight.as_str(), "bottom-right");
        assert_eq!(WatermarkPosition::TopLeft.as_str(), "top-left");
    }

    #[test]
    fn test_effective_color() {
        let wm = WatermarkSettings::new().opacity(0.5);
        let color = wm.effective_color();
        assert!((color.a - 0.5).abs() < 0.01);
    }

    #[test]
    fn test_has_text() {
        let empty = WatermarkSettings::default();
        assert!(!empty.has_text());

        let with_text = WatermarkSettings::simple("Test");
        assert!(with_text.has_text());

        let with_subtext_only = WatermarkSettings {
            subtext: Some("Sub".to_string()),
            ..Default::default()
        };
        assert!(with_subtext_only.has_text());
    }
}
