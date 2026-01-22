//! Directory display settings.

/// Directory display settings.
#[derive(Debug, Clone)]
pub struct DirectorySettings {
    /// Depth of directory names to display (0 = none, 1 = immediate parent, etc.).
    pub name_depth: u32,
    /// Position of directory name along the edge (0.0 = start, 1.0 = end).
    pub name_position: f32,
}

impl Default for DirectorySettings {
    fn default() -> Self {
        Self {
            name_depth: 1,
            name_position: 0.5,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_directory_settings_default() {
        let dir = DirectorySettings::default();
        assert_eq!(dir.name_depth, 1);
        assert!((dir.name_position - 0.5).abs() < 0.01);
    }
}
