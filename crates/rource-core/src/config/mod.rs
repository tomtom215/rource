// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Configuration module for Rource.
//!
//! This module provides:
//! - [`Settings`] - Complete visualization settings
//! - [`CameraModeSetting`] - Camera behavior modes
//! - Config file parsing (with the `config-file` feature)
//! - Environment variable configuration
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
//!
//! # Environment Variables
//!
//! Settings can be configured via environment variables with the `ROURCE_` prefix:
//!
//! ```ignore
//! use rource_core::config::{load_env, merge_env, Settings};
//!
//! // Load settings from environment only
//! let settings = load_env();
//!
//! // Or merge environment with existing settings
//! let base = Settings::default();
//! let settings = merge_env(base);
//! ```
//!
//! # Configuration Priority
//!
//! The recommended priority (highest to lowest):
//! 1. CLI arguments
//! 2. Environment variables
//! 3. Config file
//! 4. Defaults
//!
//! This allows users to set defaults in config files, override them with
//! environment variables in CI/CD, and further override with CLI args.

mod config_env;
mod settings;

#[cfg(feature = "config-file")]
mod config_file;

pub use config_env::{env_var_names, load_env, merge_env};
pub use settings::{
    CameraModeSetting, CameraSettings, DirectorySettings, DisplaySettings, ExportSettings,
    FilterSettings, InputSettings, LayoutSettings, LimitSettings, OverlaySettings,
    PlaybackSettings, Settings, TitleSettings, VisibilitySettings, WatermarkPosition,
    WatermarkSettings,
};

#[cfg(feature = "config-file")]
pub use config_file::{load_config_file, merge_config_file, parse_config, ConfigError};
