// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Input handling settings.

/// Input settings.
#[derive(Debug, Clone)]
pub struct InputSettings {
    /// Disable all user input (for automated playback).
    pub disable_input: bool,
    /// Mouse sensitivity for pan/zoom.
    pub mouse_sensitivity: f32,
}

impl InputSettings {
    /// Default mouse sensitivity.
    const DEFAULT_MOUSE_SENSITIVITY: f32 = 1.0;
}

impl Default for InputSettings {
    fn default() -> Self {
        Self {
            disable_input: false,
            mouse_sensitivity: Self::DEFAULT_MOUSE_SENSITIVITY,
        }
    }
}
