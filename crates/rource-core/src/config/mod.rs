//! Configuration module for Rource.
//!
//! This module provides:
//! - [`Settings`] - Complete visualization settings
//! - [`CameraModeSetting`] - Camera behavior modes
//!
//! # Example
//!
//! ```
//! use rource_core::config::{Settings, CameraModeSetting};
//!
//! let settings = Settings::new()
//!     .with_dimensions(1920, 1080)
//!     .with_bloom(true)
//!     .with_camera_mode(CameraModeSetting::Track);
//!
//! assert!(settings.is_valid());
//! ```

mod settings;

pub use settings::{
    CameraModeSetting, CameraSettings, DisplaySettings, ExportSettings, InputSettings,
    LimitSettings, PlaybackSettings, Settings, TitleSettings, VisibilitySettings,
};
