// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Codebase growth trajectory analysis.
//!
//! Tracks codebase size (active file count) over time and computes growth
//! rate, acceleration, and growth/consolidation periods.
//!
//! # Research Basis
//!
//! Lehman (1996) "Laws of Software Evolution" established that software
//! systems must continually adapt or become progressively less satisfactory.
//! Tracking growth trajectory reveals whether a codebase is growing
//! sustainably (linear) or unsustainably (super-linear).
//!
//! # Algorithm
//!
//! Maintains a running set of active files. On each commit:
//! - `Create` adds a file to the active set
//! - `Delete` removes a file from the active set
//! - `Modify` has no effect on the file count
//!
//! Growth rate is computed as files per month over the repository lifetime.
//! Growth periods are intervals where the creation rate exceeds the deletion
//! rate, and consolidation periods are the reverse.
//!
//! # Complexity
//!
//! - Accumulation: O(N) where N = total file actions
//! - Finalization: O(N log N) for sorting the time series

use rustc_hash::FxHashSet;

use super::FileActionKind;

/// Seconds per 30-day month (used for rate normalization).
const SECONDS_PER_MONTH: f64 = 30.0 * 86400.0;

/// A snapshot of codebase size at a point in time.
#[derive(Debug, Clone)]
pub struct GrowthSnapshot {
    /// Unix timestamp of this snapshot.
    pub timestamp: i64,
    /// Number of active (non-deleted) files at this point.
    pub active_files: usize,
    /// Cumulative files created up to this point.
    pub cumulative_creates: u32,
    /// Cumulative files deleted up to this point.
    pub cumulative_deletes: u32,
}

/// Complete growth analysis for the repository.
#[derive(Debug, Clone)]
pub struct GrowthReport {
    /// Time series of codebase size snapshots (one per commit).
    pub snapshots: Vec<GrowthSnapshot>,
    /// Current number of active files.
    pub current_file_count: usize,
    /// Total files ever created.
    pub total_created: u32,
    /// Total files ever deleted.
    pub total_deleted: u32,
    /// Net growth (created - deleted).
    pub net_growth: i64,
    /// Average monthly growth rate (files per month).
    pub avg_monthly_growth: f64,
    /// Growth trend classification.
    pub trend: GrowthTrend,
}

/// Growth trend classification based on rate changes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GrowthTrend {
    /// Growth rate is increasing over time.
    Accelerating,
    /// Growth rate is approximately constant.
    Stable,
    /// Growth rate is decreasing over time.
    Decelerating,
    /// Codebase is shrinking (more deletes than creates).
    Shrinking,
}

/// Accumulates growth data during commit processing.
pub struct GrowthAccumulator {
    /// Set of currently active file paths.
    active_files: FxHashSet<String>,
    /// Cumulative create count.
    creates: u32,
    /// Cumulative delete count.
    deletes: u32,
    /// Snapshots recorded at each commit.
    snapshots: Vec<GrowthSnapshot>,
}

impl Default for GrowthAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl GrowthAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            active_files: FxHashSet::default(),
            creates: 0,
            deletes: 0,
            snapshots: Vec::new(),
        }
    }

    /// Records a file action for growth tracking.
    pub fn record_file(&mut self, path: &str, action: FileActionKind) {
        match action {
            FileActionKind::Create => {
                self.active_files.insert(path.to_string());
                self.creates += 1;
            }
            FileActionKind::Delete => {
                self.active_files.remove(path);
                self.deletes += 1;
            }
            FileActionKind::Modify => {}
        }
    }

    /// Records a snapshot after processing a commit.
    pub fn record_snapshot(&mut self, timestamp: i64) {
        self.snapshots.push(GrowthSnapshot {
            timestamp,
            active_files: self.active_files.len(),
            cumulative_creates: self.creates,
            cumulative_deletes: self.deletes,
        });
    }

    /// Finalizes the accumulator into a [`GrowthReport`].
    ///
    /// # Arguments
    ///
    /// * `t_min` - Earliest commit timestamp
    /// * `t_max` - Latest commit timestamp
    #[must_use]
    pub fn finalize(self, t_min: i64, t_max: i64) -> GrowthReport {
        let current_file_count = self.active_files.len();
        let net_growth = i64::from(self.creates) - i64::from(self.deletes);
        let time_span = (t_max - t_min) as f64;

        let avg_monthly_growth = if time_span > 0.0 {
            net_growth as f64 / (time_span / SECONDS_PER_MONTH)
        } else {
            net_growth as f64
        };

        let trend = classify_trend(&self.snapshots, time_span);

        GrowthReport {
            snapshots: self.snapshots,
            current_file_count,
            total_created: self.creates,
            total_deleted: self.deletes,
            net_growth,
            avg_monthly_growth,
            trend,
        }
    }
}

/// Classifies the growth trend by comparing first-half and second-half rates.
fn classify_trend(snapshots: &[GrowthSnapshot], time_span: f64) -> GrowthTrend {
    if snapshots.len() < 4 || time_span <= 0.0 {
        if snapshots.last().map_or(0, |s| s.active_files) == 0 {
            return GrowthTrend::Shrinking;
        }
        return GrowthTrend::Stable;
    }

    let mid = snapshots.len() / 2;
    let first_half = &snapshots[..mid];
    let second_half = &snapshots[mid..];

    let first_growth = compute_half_growth(first_half);
    let second_growth = compute_half_growth(second_half);

    // Net growth across entire history
    #[allow(clippy::cast_possible_wrap)]
    let total_net = snapshots.last().map_or(0, |s| s.active_files) as i64
        - snapshots.first().map_or(0, |s| s.active_files) as i64;

    if total_net < 0 {
        return GrowthTrend::Shrinking;
    }

    // Compare halves: >20% difference is meaningful
    let threshold = 0.2;
    if first_growth.abs() < f64::EPSILON && second_growth.abs() < f64::EPSILON {
        GrowthTrend::Stable
    } else if first_growth.abs() < f64::EPSILON {
        if second_growth > 0.0 {
            GrowthTrend::Accelerating
        } else {
            GrowthTrend::Decelerating
        }
    } else {
        let ratio = second_growth / first_growth;
        if ratio > 1.0 + threshold {
            GrowthTrend::Accelerating
        } else if ratio < 1.0 - threshold {
            GrowthTrend::Decelerating
        } else {
            GrowthTrend::Stable
        }
    }
}

/// Computes net file growth for a slice of snapshots.
fn compute_half_growth(snapshots: &[GrowthSnapshot]) -> f64 {
    if snapshots.len() < 2 {
        return 0.0;
    }
    let first = snapshots.first().unwrap();
    let last = snapshots.last().unwrap();
    last.active_files as f64 - first.active_files as f64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = GrowthAccumulator::new();
        let report = acc.finalize(0, 0);
        assert_eq!(report.current_file_count, 0);
        assert_eq!(report.total_created, 0);
        assert_eq!(report.total_deleted, 0);
        assert_eq!(report.net_growth, 0);
        assert!(report.snapshots.is_empty());
    }

    #[test]
    fn test_create_increases_file_count() {
        let mut acc = GrowthAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create);
        acc.record_snapshot(1000);
        acc.record_file("b.rs", FileActionKind::Create);
        acc.record_snapshot(2000);

        let report = acc.finalize(1000, 2000);
        assert_eq!(report.current_file_count, 2);
        assert_eq!(report.total_created, 2);
        assert_eq!(report.total_deleted, 0);
        assert_eq!(report.net_growth, 2);
        assert_eq!(report.snapshots.len(), 2);
        assert_eq!(report.snapshots[0].active_files, 1);
        assert_eq!(report.snapshots[1].active_files, 2);
    }

    #[test]
    fn test_delete_decreases_file_count() {
        let mut acc = GrowthAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create);
        acc.record_file("b.rs", FileActionKind::Create);
        acc.record_snapshot(1000);
        acc.record_file("a.rs", FileActionKind::Delete);
        acc.record_snapshot(2000);

        let report = acc.finalize(1000, 2000);
        assert_eq!(report.current_file_count, 1);
        assert_eq!(report.total_created, 2);
        assert_eq!(report.total_deleted, 1);
        assert_eq!(report.net_growth, 1);
        assert_eq!(report.snapshots[0].active_files, 2);
        assert_eq!(report.snapshots[1].active_files, 1);
    }

    #[test]
    fn test_modify_does_not_change_count() {
        let mut acc = GrowthAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create);
        acc.record_snapshot(1000);
        acc.record_file("a.rs", FileActionKind::Modify);
        acc.record_snapshot(2000);

        let report = acc.finalize(1000, 2000);
        assert_eq!(report.current_file_count, 1);
        assert_eq!(report.total_created, 1);
        assert_eq!(report.total_deleted, 0);
        assert_eq!(report.snapshots[0].active_files, 1);
        assert_eq!(report.snapshots[1].active_files, 1);
    }

    #[test]
    fn test_delete_nonexistent_is_safe() {
        let mut acc = GrowthAccumulator::new();
        acc.record_file("missing.rs", FileActionKind::Delete);
        acc.record_snapshot(1000);

        let report = acc.finalize(1000, 1000);
        assert_eq!(report.current_file_count, 0);
        assert_eq!(report.total_deleted, 1);
        assert_eq!(report.net_growth, -1);
    }

    #[test]
    fn test_avg_monthly_growth() {
        let mut acc = GrowthAccumulator::new();
        // Create 30 files over 30 days
        for i in 0..30 {
            let name = format!("file{i}.rs");
            acc.record_file(&name, FileActionKind::Create);
            acc.record_snapshot(i * 86400);
        }

        let report = acc.finalize(0, 29 * 86400);
        // 30 files in 29 days ≈ 31.03 files/month
        assert_eq!(report.total_created, 30);
        assert!(
            (report.avg_monthly_growth - 30.0 / (29.0 * 86400.0 / SECONDS_PER_MONTH)).abs() < 0.01,
            "avg_monthly_growth={}, expected=~31.0",
            report.avg_monthly_growth
        );
    }

    #[test]
    fn test_zero_time_span_growth() {
        let mut acc = GrowthAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create);
        acc.record_snapshot(5000);

        let report = acc.finalize(5000, 5000);
        // With zero time span, avg_monthly_growth = net_growth = 1.0
        assert!((report.avg_monthly_growth - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_shrinking_trend() {
        let mut acc = GrowthAccumulator::new();
        // Create 10 files, then delete them all
        for i in 0..10 {
            let name = format!("file{i}.rs");
            acc.record_file(&name, FileActionKind::Create);
            acc.record_snapshot(i * 1000);
        }
        for i in 0..10 {
            let name = format!("file{i}.rs");
            acc.record_file(&name, FileActionKind::Delete);
            acc.record_snapshot(10000 + i * 1000);
        }

        let report = acc.finalize(0, 19000);
        assert_eq!(report.trend, GrowthTrend::Shrinking);
        assert_eq!(report.current_file_count, 0);
    }

    #[test]
    fn test_cumulative_counts_in_snapshots() {
        let mut acc = GrowthAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create);
        acc.record_snapshot(1000);
        acc.record_file("b.rs", FileActionKind::Create);
        acc.record_file("a.rs", FileActionKind::Delete);
        acc.record_snapshot(2000);

        let report = acc.finalize(1000, 2000);
        assert_eq!(report.snapshots[0].cumulative_creates, 1);
        assert_eq!(report.snapshots[0].cumulative_deletes, 0);
        assert_eq!(report.snapshots[1].cumulative_creates, 2);
        assert_eq!(report.snapshots[1].cumulative_deletes, 1);
    }

    #[test]
    fn test_default() {
        let acc = GrowthAccumulator::default();
        let report = acc.finalize(0, 0);
        assert_eq!(report.current_file_count, 0);
    }

    #[test]
    fn test_duplicate_create_idempotent() {
        let mut acc = GrowthAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create);
        acc.record_file("a.rs", FileActionKind::Create);
        acc.record_snapshot(1000);

        let report = acc.finalize(1000, 1000);
        // HashSet deduplicates: only 1 active file
        assert_eq!(report.current_file_count, 1);
        // But creates counter incremented twice
        assert_eq!(report.total_created, 2);
    }
}
