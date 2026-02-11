// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! WASM API modules for Rource.
//!
//! This module organizes the JavaScript-facing API into focused submodules.
//! Each submodule contains an `impl Rource` block with related methods.
//!
//! ## Module Organization
//!
//! | Module | Responsibility |
//! |--------|---------------|
//! | `input` | Mouse and keyboard event handlers |
//! | `playback` | Timeline control (play, pause, seek, speed) |
//! | `camera` | View control (zoom, pan, resize) |
//! | `layout` | Layout algorithm configuration |
//! | `settings` | Visual settings (bloom, background, labels) |
//! | `export` | Screenshot and full-map export |
//! | `stats` | Render statistics and entity counts |
//! | `error` | Error metrics and error rate tracking |
//! | `authors` | Author information and colors |
//! | `hover` | Hover detection and entity info for tooltips |
//! | `insights` | Repository insights (hotspots, coupling, ownership, bus factor) |

mod authors;
#[cfg(feature = "cache")]
mod cache;
mod camera;
mod error;
mod export;
mod hover;
mod input;
mod insights;
mod layout;
mod playback;
mod settings;
pub mod stats;
