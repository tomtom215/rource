//! Video/screenshot export settings.

/// Export settings for video/screenshot output.
#[derive(Debug, Clone)]
pub struct ExportSettings {
    /// Output path for video frames.
    pub output_path: Option<String>,
    /// Frame rate for video export.
    pub framerate: u32,
    /// Screenshot output path.
    pub screenshot_path: Option<String>,
}

impl Default for ExportSettings {
    fn default() -> Self {
        Self {
            output_path: None,
            framerate: 60,
            screenshot_path: None,
        }
    }
}
