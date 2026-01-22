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
//! | `authors` | Author information and colors |

mod authors;
mod camera;
mod export;
mod input;
mod layout;
mod playback;
mod settings;
mod stats;
