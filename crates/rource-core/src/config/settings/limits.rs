// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Performance limit settings.

/// Limit settings for performance control.
#[derive(Debug, Clone)]
pub struct LimitSettings {
    /// Maximum number of files to display (0 = unlimited).
    pub max_files: usize,
    /// Maximum number of users to display (0 = unlimited).
    pub max_users: usize,
    /// Time in seconds before idle files fade out.
    pub file_idle_time: f32,
    /// Time in seconds before idle users fade out.
    pub user_idle_time: f32,
}

impl Default for LimitSettings {
    fn default() -> Self {
        Self {
            max_files: 0,
            max_users: 0,
            file_idle_time: 60.0,
            user_idle_time: 10.0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_limit_settings_default() {
        let limits = LimitSettings::default();
        assert_eq!(limits.max_files, 0); // 0 = unlimited
        assert_eq!(limits.max_users, 0);
    }
}
