// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Layout settings for radial tree visualization.

/// Layout settings for radial tree visualization.
///
/// These settings control how directories and files are positioned in the
/// visualization. The layout automatically adapts to repository size when
/// `auto_scale` is enabled.
///
/// # Adaptive Scaling
///
/// For large repositories (10k+ files), the default spacing can cause
/// extreme center density. When `auto_scale` is true, parameters are
/// automatically adjusted based on repository statistics:
///
/// - `radial_distance_scale` increases logarithmically with file count
/// - `min_angular_span` increases to prevent collapsed sectors
/// - `depth_distance_exponent` adds extra spacing for deep hierarchies
///
/// # Performance Considerations
///
/// Larger `radial_distance_scale` values increase world space size, which
/// may affect rendering performance. The layout algorithm is O(n) for
/// positioning but force-directed physics can be O(n²) for dense areas.
#[derive(Debug, Clone)]
pub struct LayoutSettings {
    /// Enable automatic scaling based on repository size.
    /// When true, layout parameters adapt to file count and directory depth.
    pub auto_scale: bool,

    /// Base distance per depth level (pixels in world space).
    /// Higher values spread the tree outward more.
    /// Default: 80.0, Range: [40.0, 500.0]
    pub radial_distance_scale: f32,

    /// Minimum angular span for directory sectors (radians).
    /// Prevents thin slivers for directories with few children.
    /// Default: 0.05 (~3°), Range: [0.01, 0.5]
    pub min_angular_span: f32,

    /// Exponent for depth-based distance scaling.
    /// Values > 1.0 add extra spacing at deeper levels.
    /// Formula: `distance = base_distance * depth^exponent`
    /// Default: 1.0 (linear), Range: [0.5, 2.0]
    pub depth_distance_exponent: f32,

    /// Multiplier for sibling spacing within a directory.
    /// Higher values spread siblings further apart angularly.
    /// Default: 1.0, Range: [0.5, 3.0]
    pub sibling_spacing_multiplier: f32,

    /// Opacity falloff rate for branch lines based on depth.
    /// Higher values make deep branches fade faster.
    /// 0.0 = no fading, 1.0 = full fade at max depth.
    /// Default: 0.3, Range: [0.0, 1.0]
    pub branch_depth_fade: f32,

    /// Maximum opacity for directory-to-parent branch lines.
    /// Default: 0.35, Range: [0.0, 1.0]
    pub branch_opacity_max: f32,

    /// File count threshold for "large repository" mode.
    /// When exceeded and `auto_scale` is true, layout adapts.
    /// Default: 10000
    pub large_repo_threshold: usize,

    /// Maximum radial distance scale (caps auto-scaling).
    /// Prevents excessive world space for extreme repositories.
    /// Default: 400.0
    pub max_radial_distance_scale: f32,
}

impl Default for LayoutSettings {
    fn default() -> Self {
        Self {
            auto_scale: true,
            radial_distance_scale: 80.0,
            min_angular_span: 0.05,
            depth_distance_exponent: 1.0,
            sibling_spacing_multiplier: 1.0,
            branch_depth_fade: 0.3,
            branch_opacity_max: 0.35,
            large_repo_threshold: 10_000,
            max_radial_distance_scale: 400.0,
        }
    }
}

impl LayoutSettings {
    /// Creates layout settings optimized for small repositories (< 1000 files).
    pub fn small_repo() -> Self {
        Self {
            auto_scale: false,
            radial_distance_scale: 60.0,
            min_angular_span: 0.03,
            depth_distance_exponent: 1.0,
            sibling_spacing_multiplier: 0.8,
            branch_depth_fade: 0.2,
            branch_opacity_max: 0.4,
            ..Default::default()
        }
    }

    /// Creates layout settings optimized for medium repositories (1000-10000 files).
    pub fn medium_repo() -> Self {
        Self {
            auto_scale: false,
            radial_distance_scale: 100.0,
            min_angular_span: 0.05,
            depth_distance_exponent: 1.1,
            sibling_spacing_multiplier: 1.0,
            branch_depth_fade: 0.3,
            branch_opacity_max: 0.35,
            ..Default::default()
        }
    }

    /// Creates layout settings optimized for large repositories (10000-50000 files).
    pub fn large_repo() -> Self {
        Self {
            auto_scale: false,
            radial_distance_scale: 160.0,
            min_angular_span: 0.08,
            depth_distance_exponent: 1.2,
            sibling_spacing_multiplier: 1.2,
            branch_depth_fade: 0.5,
            branch_opacity_max: 0.25,
            ..Default::default()
        }
    }

    /// Creates layout settings optimized for massive repositories (50000+ files).
    pub fn massive_repo() -> Self {
        Self {
            auto_scale: false,
            radial_distance_scale: 250.0,
            min_angular_span: 0.1,
            depth_distance_exponent: 1.3,
            sibling_spacing_multiplier: 1.5,
            branch_depth_fade: 0.7,
            branch_opacity_max: 0.15,
            ..Default::default()
        }
    }

    /// Computes optimal layout settings based on repository statistics.
    ///
    /// # Arguments
    /// * `file_count` - Total number of files in the repository
    /// * `max_depth` - Maximum directory depth
    /// * `dir_count` - Total number of directories
    ///
    /// # Returns
    /// Layout settings tuned for the given repository characteristics.
    #[must_use]
    pub fn from_repo_stats(file_count: usize, max_depth: u32, dir_count: usize) -> Self {
        // Start with defaults, but auto_scale is false since we're computing explicit values
        let mut settings = Self {
            auto_scale: false,
            ..Default::default()
        };

        // Logarithmic scaling for radial distance based on file count
        // Formula: base * (1 + log2(files / threshold))
        if file_count > settings.large_repo_threshold {
            let scale_factor =
                1.0 + (file_count as f32 / settings.large_repo_threshold as f32).log2();
            settings.radial_distance_scale =
                (80.0 * scale_factor).min(settings.max_radial_distance_scale);
        }

        // Adjust angular span based on average children per directory
        let avg_children = if dir_count > 0 {
            (file_count + dir_count) as f32 / dir_count as f32
        } else {
            1.0
        };
        if avg_children > 20.0 {
            settings.min_angular_span = (0.05 * (avg_children / 20.0).sqrt()).min(0.2);
        }

        // Depth exponent increases for deep hierarchies
        if max_depth > 8 {
            settings.depth_distance_exponent = 1.0 + (max_depth as f32 - 8.0) * 0.05;
            settings.depth_distance_exponent = settings.depth_distance_exponent.min(1.5);
        }

        // Branch fading increases with file count
        settings.branch_depth_fade = match file_count {
            0..=1_000 => 0.2,
            1_001..=10_000 => 0.3,
            10_001..=50_000 => 0.5,
            _ => 0.7,
        };

        // Branch opacity decreases for dense repos
        settings.branch_opacity_max = match file_count {
            0..=1_000 => 0.4,
            1_001..=10_000 => 0.35,
            10_001..=50_000 => 0.25,
            _ => 0.15,
        };

        settings
    }

    /// Validates settings and returns errors if any values are out of range.
    pub fn validate(&self) -> Vec<String> {
        let mut errors = Vec::new();

        if self.radial_distance_scale < 20.0 || self.radial_distance_scale > 1000.0 {
            errors.push(format!(
                "radial_distance_scale {} out of range [20, 1000]",
                self.radial_distance_scale
            ));
        }

        if self.min_angular_span < 0.001 || self.min_angular_span > 1.0 {
            errors.push(format!(
                "min_angular_span {} out of range [0.001, 1.0]",
                self.min_angular_span
            ));
        }

        if self.depth_distance_exponent < 0.1 || self.depth_distance_exponent > 3.0 {
            errors.push(format!(
                "depth_distance_exponent {} out of range [0.1, 3.0]",
                self.depth_distance_exponent
            ));
        }

        if self.branch_depth_fade < 0.0 || self.branch_depth_fade > 1.0 {
            errors.push(format!(
                "branch_depth_fade {} out of range [0.0, 1.0]",
                self.branch_depth_fade
            ));
        }

        if self.branch_opacity_max < 0.0 || self.branch_opacity_max > 1.0 {
            errors.push(format!(
                "branch_opacity_max {} out of range [0.0, 1.0]",
                self.branch_opacity_max
            ));
        }

        errors
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_layout_settings_default() {
        let layout = LayoutSettings::default();
        assert!(layout.auto_scale);
        assert!((layout.radial_distance_scale - 80.0).abs() < 0.01);
        assert!((layout.min_angular_span - 0.05).abs() < 0.01);
        assert!((layout.depth_distance_exponent - 1.0).abs() < 0.01);
        assert!((layout.branch_depth_fade - 0.3).abs() < 0.01);
        assert!((layout.branch_opacity_max - 0.35).abs() < 0.01);
    }

    #[test]
    fn test_layout_settings_presets() {
        let small = LayoutSettings::small_repo();
        assert!((small.radial_distance_scale - 60.0).abs() < 0.01);

        let large = LayoutSettings::large_repo();
        assert!((large.radial_distance_scale - 160.0).abs() < 0.01);
        assert!((large.branch_depth_fade - 0.5).abs() < 0.01);

        let massive = LayoutSettings::massive_repo();
        assert!((massive.radial_distance_scale - 250.0).abs() < 0.01);
        assert!((massive.branch_depth_fade - 0.7).abs() < 0.01);
        assert!((massive.branch_opacity_max - 0.15).abs() < 0.01);
    }

    #[test]
    fn test_layout_settings_from_repo_stats() {
        // Small repo
        let settings = LayoutSettings::from_repo_stats(500, 4, 50);
        assert!((settings.branch_depth_fade - 0.2).abs() < 0.01);

        // Medium repo
        let settings = LayoutSettings::from_repo_stats(5000, 6, 300);
        assert!((settings.branch_depth_fade - 0.3).abs() < 0.01);

        // Large repo
        let settings = LayoutSettings::from_repo_stats(30000, 10, 2000);
        assert!((settings.branch_depth_fade - 0.5).abs() < 0.01);
        assert!(settings.radial_distance_scale > 80.0);

        // Massive repo (like Home Assistant)
        let settings = LayoutSettings::from_repo_stats(100_000, 15, 5000);
        assert!((settings.branch_depth_fade - 0.7).abs() < 0.01);
        assert!((settings.branch_opacity_max - 0.15).abs() < 0.01);
        // Radial scale should be significantly increased
        assert!(settings.radial_distance_scale > 150.0);
    }

    #[test]
    fn test_layout_settings_validation() {
        let mut layout = LayoutSettings::default();
        assert!(layout.validate().is_empty());

        // Invalid radial distance scale
        layout.radial_distance_scale = 10.0;
        let errors = layout.validate();
        assert!(!errors.is_empty());
        assert!(errors[0].contains("radial_distance_scale"));

        // Reset and try invalid branch fade
        layout = LayoutSettings::default();
        layout.branch_depth_fade = 1.5;
        let errors = layout.validate();
        assert!(!errors.is_empty());
        assert!(errors[0].contains("branch_depth_fade"));
    }

    #[test]
    fn test_layout_settings_depth_scaling() {
        // With exponent 1.0, depth 5 should give linear scaling
        let settings = LayoutSettings::default();
        assert!((settings.depth_distance_exponent - 1.0).abs() < 0.01);

        // For large repos, exponent increases
        let settings = LayoutSettings::from_repo_stats(50000, 12, 3000);
        assert!(settings.depth_distance_exponent > 1.0);
    }
}
