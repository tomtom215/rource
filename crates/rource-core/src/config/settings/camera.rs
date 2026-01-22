//! Camera-related settings.

/// Camera mode for the visualization.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CameraModeSetting {
    /// Overview mode - camera fits all content.
    #[default]
    Overview,
    /// Track mode - camera follows active users.
    Track,
    /// Follow mode - camera follows a specific user.
    Follow,
}

impl CameraModeSetting {
    /// Parse from a string representation.
    #[must_use]
    pub fn parse(s: &str) -> Self {
        match s.to_lowercase().as_str() {
            "track" => Self::Track,
            "follow" => Self::Follow,
            _ => Self::Overview,
        }
    }

    /// Convert to string.
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::Overview => "overview",
            Self::Track => "track",
            Self::Follow => "follow",
        }
    }
}

/// Camera settings.
#[derive(Debug, Clone)]
pub struct CameraSettings {
    /// Camera mode (overview, track, follow).
    pub mode: CameraModeSetting,
    /// Minimum zoom level.
    pub min_zoom: f32,
    /// Maximum zoom level.
    pub max_zoom: f32,
    /// Camera smoothness (0.0 = instant, 1.0 = very slow).
    pub smoothness: f32,
    /// Padding around content when auto-fitting.
    pub padding: f32,
    /// Username to follow when in follow mode.
    pub follow_user: Option<String>,
    /// Username(s) to highlight (comma-separated).
    pub highlight_users: Option<String>,
    /// Highlight all users (overrides `highlight_users`).
    pub highlight_all_users: bool,
    /// Enable 3D perspective camera mode.
    pub enable_3d: bool,
    /// Initial pitch angle in degrees (3D mode only).
    pub pitch: f32,
    /// Auto-rotation speed in radians per second (3D mode only).
    pub rotation_speed: f32,
    /// Disable automatic camera rotation (3D mode only).
    pub disable_auto_rotate: bool,
}

impl Default for CameraSettings {
    fn default() -> Self {
        Self {
            mode: CameraModeSetting::Overview,
            min_zoom: 0.05, // Matches AUTO_FIT_MIN_ZOOM to prevent LOD culling all entities
            max_zoom: 10.0,
            smoothness: 0.85,
            padding: 100.0,
            follow_user: None,
            highlight_users: None,
            highlight_all_users: false,
            enable_3d: false,
            pitch: -17.0,
            rotation_speed: 0.05,
            disable_auto_rotate: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_camera_mode_parse() {
        assert_eq!(
            CameraModeSetting::parse("overview"),
            CameraModeSetting::Overview
        );
        assert_eq!(CameraModeSetting::parse("TRACK"), CameraModeSetting::Track);
        assert_eq!(
            CameraModeSetting::parse("follow"),
            CameraModeSetting::Follow
        );
        assert_eq!(
            CameraModeSetting::parse("invalid"),
            CameraModeSetting::Overview
        );
    }

    #[test]
    fn test_camera_mode_as_str() {
        assert_eq!(CameraModeSetting::Overview.as_str(), "overview");
        assert_eq!(CameraModeSetting::Track.as_str(), "track");
        assert_eq!(CameraModeSetting::Follow.as_str(), "follow");
    }

    #[test]
    fn test_camera_settings_follow_user() {
        let camera = CameraSettings::default();
        assert!(camera.follow_user.is_none());
        assert!(camera.highlight_users.is_none());
        assert!(!camera.highlight_all_users);

        let custom = CameraSettings {
            follow_user: Some("alice".to_string()),
            highlight_users: Some("bob,charlie".to_string()),
            highlight_all_users: true,
            ..Default::default()
        };
        assert_eq!(custom.follow_user, Some("alice".to_string()));
        assert_eq!(custom.highlight_users, Some("bob,charlie".to_string()));
        assert!(custom.highlight_all_users);
    }
}
