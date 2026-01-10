//! Configuration module for Rource.
//!
//! This module provides:
//! - [`Settings`] - Complete visualization settings
//! - [`CameraModeSetting`] - Camera behavior modes
//! - Config file parsing (with the `config-file` feature)
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
//!
//! # Configuration File (requires `config-file` feature)
//!
//! With the `config-file` feature enabled, you can load settings from TOML files:
//!
//! ```ignore
//! use rource_core::config::{load_config_file, merge_config_file, Settings};
//!
//! // Load settings from a config file
//! let settings = load_config_file("rource.toml")?;
//!
//! // Or merge config file with existing settings
//! let base = Settings::default();
//! let settings = merge_config_file(base, "rource.toml")?;
//! ```

mod settings;

#[cfg(feature = "config-file")]
mod config_file;

pub use settings::{
    CameraModeSetting, CameraSettings, DisplaySettings, ExportSettings, InputSettings,
    LimitSettings, PlaybackSettings, Settings, TitleSettings, VisibilitySettings,
};

#[cfg(feature = "config-file")]
pub use config_file::{load_config_file, merge_config_file, parse_config, ConfigError};
