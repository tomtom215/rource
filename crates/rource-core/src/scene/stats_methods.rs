//! Extension statistics methods for the scene.
//!
//! This module contains methods for computing and caching file extension
//! statistics for the legend display.

use super::Scene;

/// How often to refresh extension stats cache (in frames).
/// At 60fps, 30 frames = 0.5 seconds - acceptable for legend updates.
pub(super) const STATS_CACHE_INTERVAL: u32 = 30;

impl Scene {
    /// Returns file extension statistics (extension -> count).
    ///
    /// Only includes extensions for files that are currently visible (alpha > 0.1).
    /// Uses caching to avoid recomputation every frame - cache is refreshed when:
    /// - Files are added or removed
    /// - Every `STATS_CACHE_INTERVAL` frames (to account for alpha changes)
    #[must_use]
    pub fn file_extension_stats(&mut self) -> &[(String, usize)] {
        // Check if cache needs refresh
        let needs_refresh = self.extension_stats_dirty
            || self.stats_cache_frame >= STATS_CACHE_INTERVAL
            || self.extension_stats_cache.is_empty();

        if needs_refresh {
            self.recompute_extension_stats();
            self.extension_stats_dirty = false;
            self.stats_cache_frame = 0;
        } else {
            self.stats_cache_frame += 1;
        }

        &self.extension_stats_cache
    }

    /// Recomputes extension statistics and updates the cache.
    pub(super) fn recompute_extension_stats(&mut self) {
        use std::collections::HashMap;

        let mut stats: HashMap<String, usize> = HashMap::new();

        for file in self.files.values() {
            if file.alpha() < 0.1 {
                continue;
            }
            let ext = file
                .extension()
                .map_or_else(|| "other".to_string(), str::to_lowercase);
            *stats.entry(ext).or_insert(0) += 1;
        }

        // Sort by count descending, then by extension name
        self.extension_stats_cache.clear();
        self.extension_stats_cache.extend(stats);
        self.extension_stats_cache
            .sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    }

    /// Returns file extension statistics without updating the cache.
    ///
    /// This is useful when you need stats but don't want to mutate the scene.
    /// Note: This may return stale data if the cache hasn't been refreshed recently.
    #[must_use]
    pub fn file_extension_stats_cached(&self) -> &[(String, usize)] {
        &self.extension_stats_cache
    }

    /// Invalidates the extension stats cache, forcing a recomputation on next access.
    ///
    /// This is useful for testing or when you need fresh statistics immediately.
    #[inline]
    pub fn invalidate_extension_stats(&mut self) {
        self.extension_stats_dirty = true;
    }
}
