//! Title and caption settings.

use rource_math::Color;

/// Title and caption settings.
#[derive(Debug, Clone)]
pub struct TitleSettings {
    /// Main title to display.
    pub title: Option<String>,
    /// Font size for the title.
    pub title_font_size: f32,
    /// Title color.
    pub title_color: Color,
}

impl Default for TitleSettings {
    fn default() -> Self {
        Self {
            title: None,
            title_font_size: 24.0,
            title_color: Color::WHITE,
        }
    }
}
