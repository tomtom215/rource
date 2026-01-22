//! UI element visibility settings.

/// Visibility settings for UI elements.
#[derive(Debug, Clone, Default)]
#[allow(clippy::struct_excessive_bools)]
pub struct VisibilitySettings {
    /// Hide file names.
    pub hide_filenames: bool,
    /// Hide user names.
    pub hide_usernames: bool,
    /// Hide the date display.
    pub hide_date: bool,
    /// Hide the progress bar.
    pub hide_progress: bool,
    /// Hide the file extension legend.
    pub hide_legend: bool,
    /// Hide directory names/labels.
    pub hide_dirnames: bool,
    /// Hide the root directory node.
    pub hide_root: bool,
    /// Hide the tree structure (connecting lines).
    pub hide_tree: bool,
    /// Hide the bloom/glow effect (runtime visibility, not same as `bloom_enabled`).
    pub hide_bloom: bool,
    /// Hide the mouse cursor during visualization.
    pub hide_mouse: bool,
    /// Show FPS counter.
    pub show_fps: bool,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_visibility_settings_new_fields() {
        let mut vis = VisibilitySettings::default();
        assert!(!vis.hide_dirnames);
        assert!(!vis.hide_root);
        assert!(!vis.hide_tree);
        assert!(!vis.hide_bloom);
        assert!(!vis.hide_mouse);

        vis.hide_dirnames = true;
        vis.hide_root = true;
        vis.hide_tree = true;
        vis.hide_bloom = true;
        vis.hide_mouse = true;

        assert!(vis.hide_dirnames);
        assert!(vis.hide_root);
        assert!(vis.hide_tree);
        assert!(vis.hide_bloom);
        assert!(vis.hide_mouse);
    }
}
