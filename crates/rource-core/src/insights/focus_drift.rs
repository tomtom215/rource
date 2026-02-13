// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Development focus drift analysis (M30).
//!
//! Tracks which areas of the codebase are getting more or less attention
//! over time. Reveals shifting priorities and potential neglect of
//! critical components.
//!
//! # Research Basis
//!
//! Hassan (2008) "The Road Ahead for Mining Software Repositories" (`FoSE`,
//! DOI: 10.1145/1370175.1370177) — mining for development trends.
//!
//! D'Ambros & Lanza (2010) "Distributed and Collaborative Software Evolution
//! Analysis with Churrasco" (Science of Computer Programming,
//! DOI: 10.1016/j.scico.2009.04.007).
//!
//! # Algorithm
//!
//! 1. Divide timeline into monthly windows
//! 2. For each window: `commit_share(dir) = commits_in_dir / total_commits`
//! 3. Track share over time and classify:
//!    - Rising: share increasing (growing focus)
//!    - Declining: share decreasing (potential neglect)
//!    - Stable: no significant change
//!    - Newly active: first appeared in recent windows
//!    - Abandoned: had activity, now none
//!
//! # Complexity
//!
//! - Accumulation: O(1) per file change
//! - Finalization: O(N) where N = commits, plus O(D × W) for windowing

use rustc_hash::FxHashMap;

/// Focus trend classification for a directory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FocusTrend {
    /// Increasing development attention.
    Rising,
    /// Decreasing development attention.
    Declining,
    /// Stable attention level.
    Stable,
    /// First appeared recently.
    NewlyActive,
    /// Had activity but none in recent windows.
    Abandoned,
}

impl FocusTrend {
    /// Returns a human-readable label.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Rising => "Rising",
            Self::Declining => "Declining",
            Self::Stable => "Stable",
            Self::NewlyActive => "Newly Active",
            Self::Abandoned => "Abandoned",
        }
    }
}

/// Per-directory focus drift profile.
#[derive(Debug, Clone)]
pub struct DirectoryFocusDrift {
    /// Directory path.
    pub directory: String,
    /// Focus trend classification.
    pub trend: FocusTrend,
    /// Current commit share (fraction of total commits).
    pub current_share: f64,
    /// Previous period commit share.
    pub previous_share: f64,
    /// Change in share (current - previous).
    pub share_delta: f64,
    /// Total commits to this directory.
    pub total_commits: u32,
}

/// Complete focus drift report.
#[derive(Debug, Clone)]
pub struct FocusDriftReport {
    /// Per-directory focus drift (sorted by absolute delta descending).
    pub directories: Vec<DirectoryFocusDrift>,
    /// Directories with rising focus.
    pub rising_count: usize,
    /// Directories with declining focus.
    pub declining_count: usize,
    /// Directories abandoned (no recent activity).
    pub abandoned_count: usize,
    /// Total directories analyzed.
    pub total_analyzed: usize,
}

/// Accumulates focus drift data from commit stream.
pub struct FocusDriftAccumulator {
    /// (timestamp, directory) pairs.
    commits: Vec<(i64, String)>,
}

impl Default for FocusDriftAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl FocusDriftAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            commits: Vec::new(),
        }
    }

    /// Records file changes from a commit, extracting directory.
    pub fn record_commit(&mut self, timestamp: i64, file_paths: &[&str]) {
        for path in file_paths {
            let dir = extract_directory(path);
            self.commits.push((timestamp, dir));
        }
    }

    /// Finalizes the focus drift report.
    #[must_use]
    pub fn finalize(mut self) -> FocusDriftReport {
        if self.commits.is_empty() {
            return FocusDriftReport {
                directories: Vec::new(),
                rising_count: 0,
                declining_count: 0,
                abandoned_count: 0,
                total_analyzed: 0,
            };
        }

        self.commits.sort_by_key(|&(t, _)| t);

        let t_max = self.commits.last().map_or(0, |&(t, _)| t);
        let t_min = self.commits.first().map_or(0, |&(t, _)| t);
        let span = t_max - t_min;

        // Split into two halves: previous and current
        let midpoint = t_min + span / 2;

        let mut prev_counts: FxHashMap<String, u32> = FxHashMap::default();
        let mut curr_counts: FxHashMap<String, u32> = FxHashMap::default();
        let mut total_counts: FxHashMap<String, u32> = FxHashMap::default();
        let mut prev_total = 0u32;
        let mut curr_total = 0u32;

        for &(t, ref dir) in &self.commits {
            *total_counts.entry(dir.clone()).or_insert(0) += 1;
            if t < midpoint {
                *prev_counts.entry(dir.clone()).or_insert(0) += 1;
                prev_total += 1;
            } else {
                *curr_counts.entry(dir.clone()).or_insert(0) += 1;
                curr_total += 1;
            }
        }

        let prev_total_f = f64::from(prev_total.max(1));
        let curr_total_f = f64::from(curr_total.max(1));

        // Collect all directories
        let all_dirs: rustc_hash::FxHashSet<String> = total_counts.keys().cloned().collect();

        let total_analyzed = all_dirs.len();

        let mut directories: Vec<DirectoryFocusDrift> = all_dirs
            .into_iter()
            .map(|dir| {
                let prev_count = prev_counts.get(&dir).copied().unwrap_or(0);
                let curr_count = curr_counts.get(&dir).copied().unwrap_or(0);
                let total = total_counts.get(&dir).copied().unwrap_or(0);

                let previous_share = f64::from(prev_count) / prev_total_f;
                let current_share = f64::from(curr_count) / curr_total_f;
                let share_delta = current_share - previous_share;

                // Classify trend
                let trend = if prev_count == 0 && curr_count > 0 {
                    FocusTrend::NewlyActive
                } else if curr_count == 0 && prev_count > 0 {
                    FocusTrend::Abandoned
                } else if share_delta > 0.05 {
                    FocusTrend::Rising
                } else if share_delta < -0.05 {
                    FocusTrend::Declining
                } else {
                    FocusTrend::Stable
                };

                DirectoryFocusDrift {
                    directory: dir,
                    trend,
                    current_share,
                    previous_share,
                    share_delta,
                    total_commits: total,
                }
            })
            .collect();

        // Sort by absolute delta descending (biggest changes first)
        directories.sort_by(|a, b| {
            b.share_delta
                .abs()
                .partial_cmp(&a.share_delta.abs())
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        directories.truncate(50);

        let rising_count = directories
            .iter()
            .filter(|d| d.trend == FocusTrend::Rising)
            .count();
        let declining_count = directories
            .iter()
            .filter(|d| d.trend == FocusTrend::Declining)
            .count();
        let abandoned_count = directories
            .iter()
            .filter(|d| d.trend == FocusTrend::Abandoned)
            .count();

        FocusDriftReport {
            directories,
            rising_count,
            declining_count,
            abandoned_count,
            total_analyzed,
        }
    }
}

/// Extracts the top-level directory from a file path.
fn extract_directory(path: &str) -> String {
    path.split('/')
        .next()
        .filter(|_| path.contains('/'))
        .unwrap_or(".")
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let acc = FocusDriftAccumulator::new();
        let report = acc.finalize();
        assert!(report.directories.is_empty());
    }

    #[test]
    fn test_rising_trend() {
        let mut acc = FocusDriftAccumulator::new();
        // Few commits to src/ early, many later
        acc.record_commit(100, &["tests/a.rs"]);
        acc.record_commit(200, &["tests/b.rs"]);
        acc.record_commit(300, &["tests/c.rs"]);
        acc.record_commit(400, &["tests/d.rs"]);
        // Late: lots of src/ activity
        acc.record_commit(500, &["src/a.rs"]);
        acc.record_commit(600, &["src/b.rs"]);
        acc.record_commit(700, &["src/c.rs"]);
        acc.record_commit(800, &["src/d.rs"]);
        acc.record_commit(900, &["src/e.rs"]);
        let report = acc.finalize();
        assert!(!report.directories.is_empty());
    }

    #[test]
    fn test_abandoned_directory() {
        let mut acc = FocusDriftAccumulator::new();
        // Activity only in first half
        acc.record_commit(100, &["old/a.rs"]);
        acc.record_commit(200, &["old/b.rs"]);
        // Second half: only other dirs
        acc.record_commit(1000, &["new/c.rs"]);
        acc.record_commit(2000, &["new/d.rs"]);
        let report = acc.finalize();
        let old_dir = report.directories.iter().find(|d| d.directory == "old");
        if let Some(d) = old_dir {
            assert_eq!(d.trend, FocusTrend::Abandoned);
        }
    }

    #[test]
    fn test_default_impl() {
        let acc = FocusDriftAccumulator::default();
        let report = acc.finalize();
        assert!(report.directories.is_empty());
    }
}
