// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! File lifecycle analysis.
//!
//! Tracks the full lifecycle of each file: creation, modification history,
//! and eventual deletion. Identifies short-lived (ephemeral) files and
//! long-dormant (dead) files.
//!
//! # Research Basis
//!
//! Godfrey & Tu (2000) "Evolution in Open Source Software" studied growth
//! patterns in Linux. Gall et al. (1998) "Detection of Logical Coupling
//! Based on Product Release History" established lifecycle-based analysis
//! of software artifacts.
//!
//! # Algorithm
//!
//! For each file, record first creation, last modification, and deletion
//! timestamps. Classify lifecycle:
//! - **Active**: recently modified (within last 20% of time span)
//! - **Stable**: exists but rarely changes
//! - **Ephemeral**: created and deleted within `threshold_days`
//! - **Dead**: no changes in the last `dead_threshold_days`
//! - **Deleted**: file has been removed
//!
//! # Complexity
//!
//! - Accumulation: O(1) per file action
//! - Finalization: O(F log F) where F = number of files

use rustc_hash::FxHashMap;

use super::FileActionKind;

/// Seconds per day.
const SECONDS_PER_DAY: f64 = 86400.0;

/// Default threshold for ephemeral file detection (days).
const EPHEMERAL_THRESHOLD_DAYS: f64 = 30.0;

/// Default threshold for dead file detection (fraction of total time span).
/// Files not modified in the last 30% of the repo's history are considered dead.
const DEAD_FRACTION: f64 = 0.30;

/// Lifecycle stage of a file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LifecycleStage {
    /// Recently modified (within last 20% of time span).
    Active,
    /// Exists, rarely changes, not recently modified.
    Stable,
    /// Created and deleted within a short window.
    Ephemeral,
    /// No changes in a long time (but not deleted).
    Dead,
    /// File has been deleted from the repository.
    Deleted,
}

/// Lifecycle data for a single file.
#[derive(Debug, Clone)]
pub struct FileLifecycle {
    /// File path relative to repository root.
    pub path: String,
    /// Lifecycle stage.
    pub stage: LifecycleStage,
    /// Timestamp of first appearance (Unix seconds).
    pub first_seen: i64,
    /// Timestamp of last modification (Unix seconds).
    pub last_modified: i64,
    /// Timestamp of deletion, if deleted (Unix seconds).
    pub deleted_at: Option<i64>,
    /// Age in days (from `first_seen` to `t_max` or deletion).
    pub age_days: f64,
    /// Total number of modifications.
    pub modification_count: u32,
    /// Modifications per month (change rate).
    pub modifications_per_month: f64,
    /// Number of unique authors.
    pub unique_authors: usize,
}

/// Aggregate lifecycle report.
#[derive(Debug, Clone)]
pub struct LifecycleReport {
    /// Per-file lifecycle data, sorted by stage priority (ephemeral first).
    pub files: Vec<FileLifecycle>,
    /// Average file lifespan in days.
    pub avg_lifespan_days: f64,
    /// Number of ephemeral files.
    pub ephemeral_count: usize,
    /// Number of dead files.
    pub dead_count: usize,
    /// Number of deleted files.
    pub deleted_count: usize,
    /// Number of active files.
    pub active_count: usize,
    /// Churn rate: (created + deleted) / total files seen.
    pub churn_rate: f64,
    /// Total files ever seen.
    pub total_files_seen: usize,
}

/// Per-file accumulator data.
struct FileData {
    first_seen: i64,
    last_modified: i64,
    deleted_at: Option<i64>,
    modification_count: u32,
    authors: rustc_hash::FxHashSet<String>,
    was_created: bool,
}

/// Accumulates file lifecycle data during commit processing.
pub struct LifecycleAccumulator {
    files: FxHashMap<String, FileData>,
    total_creates: u32,
    total_deletes: u32,
}

impl Default for LifecycleAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl LifecycleAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            files: FxHashMap::default(),
            total_creates: 0,
            total_deletes: 0,
        }
    }

    /// Records a file action for lifecycle tracking.
    pub fn record_file(
        &mut self,
        path: &str,
        action: FileActionKind,
        timestamp: i64,
        author: &str,
    ) {
        let data = self
            .files
            .entry(path.to_string())
            .or_insert_with(|| FileData {
                first_seen: timestamp,
                last_modified: timestamp,
                deleted_at: None,
                modification_count: 0,
                authors: rustc_hash::FxHashSet::default(),
                was_created: false,
            });

        data.authors.insert(author.to_string());

        if timestamp < data.first_seen {
            data.first_seen = timestamp;
        }
        if timestamp > data.last_modified {
            data.last_modified = timestamp;
        }

        match action {
            FileActionKind::Create => {
                data.was_created = true;
                data.deleted_at = None; // Re-created after deletion
                self.total_creates += 1;
            }
            FileActionKind::Modify => {
                data.modification_count += 1;
            }
            FileActionKind::Delete => {
                data.deleted_at = Some(timestamp);
                self.total_deletes += 1;
            }
        }
    }

    /// Finalizes the accumulator into a [`LifecycleReport`].
    ///
    /// # Arguments
    ///
    /// * `t_min` - Earliest commit timestamp
    /// * `t_max` - Latest commit timestamp
    #[must_use]
    pub fn finalize(self, t_min: i64, t_max: i64) -> LifecycleReport {
        let time_span = (t_max - t_min) as f64;
        let dead_threshold = t_max as f64 - time_span * DEAD_FRACTION;
        let active_threshold = t_max as f64 - time_span * 0.20;
        let total_files_seen = self.files.len();

        let mut files: Vec<FileLifecycle> = self
            .files
            .into_iter()
            .map(|(path, data)| {
                build_lifecycle(path, &data, t_max, dead_threshold, active_threshold)
            })
            .collect();

        // Sort: ephemeral first, then dead, then deleted, then active, then stable
        files.sort_by_key(|f| stage_priority(f.stage));

        let ephemeral_count = files
            .iter()
            .filter(|f| f.stage == LifecycleStage::Ephemeral)
            .count();
        let dead_count = files
            .iter()
            .filter(|f| f.stage == LifecycleStage::Dead)
            .count();
        let deleted_count = files
            .iter()
            .filter(|f| f.stage == LifecycleStage::Deleted)
            .count();
        let active_count = files
            .iter()
            .filter(|f| f.stage == LifecycleStage::Active)
            .count();

        let avg_lifespan_days = if files.is_empty() {
            0.0
        } else {
            files.iter().map(|f| f.age_days).sum::<f64>() / files.len() as f64
        };

        let churn_rate = if total_files_seen > 0 {
            f64::from(self.total_creates + self.total_deletes) / total_files_seen as f64
        } else {
            0.0
        };

        LifecycleReport {
            files,
            avg_lifespan_days,
            ephemeral_count,
            dead_count,
            deleted_count,
            active_count,
            churn_rate,
            total_files_seen,
        }
    }
}

/// Builds lifecycle data for a single file.
fn build_lifecycle(
    path: String,
    data: &FileData,
    t_max: i64,
    dead_threshold: f64,
    active_threshold: f64,
) -> FileLifecycle {
    let end_time = data.deleted_at.unwrap_or(t_max);
    let age_days = (end_time - data.first_seen) as f64 / SECONDS_PER_DAY;
    let age_seconds = (end_time - data.first_seen) as f64;

    let modifications_per_month = if age_seconds > 0.0 {
        f64::from(data.modification_count) / (age_seconds / (30.0 * SECONDS_PER_DAY))
    } else {
        f64::from(data.modification_count)
    };

    let stage = classify_lifecycle(data, dead_threshold, active_threshold);

    FileLifecycle {
        path,
        stage,
        first_seen: data.first_seen,
        last_modified: data.last_modified,
        deleted_at: data.deleted_at,
        age_days,
        modification_count: data.modification_count,
        modifications_per_month,
        unique_authors: data.authors.len(),
    }
}

/// Classifies a file's lifecycle stage.
fn classify_lifecycle(
    data: &FileData,
    dead_threshold: f64,
    active_threshold: f64,
) -> LifecycleStage {
    // Deleted files
    if let Some(delete_time) = data.deleted_at {
        // Ephemeral: created and deleted within threshold
        if data.was_created {
            let lifespan = (delete_time - data.first_seen) as f64 / SECONDS_PER_DAY;
            if lifespan <= EPHEMERAL_THRESHOLD_DAYS {
                return LifecycleStage::Ephemeral;
            }
        }
        return LifecycleStage::Deleted;
    }

    // Active: recently modified
    if (data.last_modified as f64) >= active_threshold {
        return LifecycleStage::Active;
    }

    // Dead: not modified for a long time
    if (data.last_modified as f64) < dead_threshold {
        return LifecycleStage::Dead;
    }

    LifecycleStage::Stable
}

/// Maps lifecycle stage to sort priority (lower = first).
fn stage_priority(stage: LifecycleStage) -> u8 {
    match stage {
        LifecycleStage::Ephemeral => 0,
        LifecycleStage::Dead => 1,
        LifecycleStage::Deleted => 2,
        LifecycleStage::Stable => 3,
        LifecycleStage::Active => 4,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = LifecycleAccumulator::new();
        let report = acc.finalize(0, 0);
        assert!(report.files.is_empty());
        assert_eq!(report.total_files_seen, 0);
        assert!((report.avg_lifespan_days - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_active_file() {
        let mut acc = LifecycleAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create, 1000, "Alice");
        acc.record_file("a.rs", FileActionKind::Modify, 9000, "Alice");

        let report = acc.finalize(0, 10000);
        assert_eq!(report.files.len(), 1);
        // last_modified = 9000, active_threshold = 10000 - 0.2*10000 = 8000
        assert_eq!(report.files[0].stage, LifecycleStage::Active);
        assert_eq!(report.active_count, 1);
    }

    #[test]
    fn test_dead_file() {
        let mut acc = LifecycleAccumulator::new();
        acc.record_file("old.rs", FileActionKind::Create, 0, "Alice");
        acc.record_file("old.rs", FileActionKind::Modify, 100, "Alice");

        let report = acc.finalize(0, 100_000);
        // last_modified = 100, dead_threshold = 100000 - 0.3*100000 = 70000
        assert_eq!(report.files[0].stage, LifecycleStage::Dead);
        assert_eq!(report.dead_count, 1);
    }

    #[test]
    fn test_ephemeral_file() {
        let mut acc = LifecycleAccumulator::new();
        // Created and deleted within 30 days
        acc.record_file("temp.rs", FileActionKind::Create, 1000, "Alice");
        acc.record_file(
            "temp.rs",
            FileActionKind::Delete,
            1000 + 20 * 86400, // 20 days later
            "Alice",
        );

        let report = acc.finalize(0, 100_000);
        assert_eq!(report.files[0].stage, LifecycleStage::Ephemeral);
        assert_eq!(report.ephemeral_count, 1);
    }

    #[test]
    fn test_deleted_not_ephemeral() {
        let mut acc = LifecycleAccumulator::new();
        // Created and deleted but after 60 days → Deleted (not Ephemeral)
        acc.record_file("long.rs", FileActionKind::Create, 1000, "Alice");
        acc.record_file(
            "long.rs",
            FileActionKind::Delete,
            1000 + 60 * 86400,
            "Alice",
        );

        let report = acc.finalize(0, 100_000);
        assert_eq!(report.files[0].stage, LifecycleStage::Deleted);
        assert_eq!(report.deleted_count, 1);
    }

    #[test]
    fn test_modification_count() {
        let mut acc = LifecycleAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create, 1000, "Alice");
        acc.record_file("a.rs", FileActionKind::Modify, 2000, "Alice");
        acc.record_file("a.rs", FileActionKind::Modify, 3000, "Bob");
        acc.record_file("a.rs", FileActionKind::Modify, 4000, "Carol");

        let report = acc.finalize(1000, 4000);
        assert_eq!(report.files[0].modification_count, 3);
        assert_eq!(report.files[0].unique_authors, 3);
    }

    #[test]
    fn test_churn_rate() {
        let mut acc = LifecycleAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create, 1000, "Alice");
        acc.record_file("b.rs", FileActionKind::Create, 2000, "Alice");
        acc.record_file("a.rs", FileActionKind::Delete, 3000, "Alice");

        let report = acc.finalize(1000, 3000);
        // 2 creates + 1 delete = 3 events, 2 unique files
        // churn_rate = 3 / 2 = 1.5
        assert!(
            (report.churn_rate - 1.5).abs() < f64::EPSILON,
            "churn_rate={}, expected=1.5",
            report.churn_rate
        );
    }

    #[test]
    fn test_re_creation_clears_deletion() {
        let mut acc = LifecycleAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create, 1000, "Alice");
        acc.record_file("a.rs", FileActionKind::Delete, 2000, "Alice");
        acc.record_file("a.rs", FileActionKind::Create, 9000, "Bob"); // Re-created

        let report = acc.finalize(0, 10000);
        // Re-creation clears the deleted_at flag
        assert!(report.files[0].deleted_at.is_none());
        // Should be Active since last_modified = 9000, active_threshold = 8000
        assert_eq!(report.files[0].stage, LifecycleStage::Active);
    }

    #[test]
    fn test_age_days() {
        let mut acc = LifecycleAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create, 0, "Alice");

        let report = acc.finalize(0, 10 * 86400); // 10 days
        assert!(
            (report.files[0].age_days - 10.0).abs() < f64::EPSILON,
            "age_days={}, expected=10.0",
            report.files[0].age_days
        );
    }

    #[test]
    fn test_deleted_file_age() {
        let mut acc = LifecycleAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create, 0, "Alice");
        acc.record_file("a.rs", FileActionKind::Delete, 5 * 86400, "Alice");

        let report = acc.finalize(0, 10 * 86400);
        // Age should be from first_seen to delete_time, not t_max
        assert!(
            (report.files[0].age_days - 5.0).abs() < f64::EPSILON,
            "age_days={}, expected=5.0",
            report.files[0].age_days
        );
    }

    #[test]
    fn test_default() {
        let acc = LifecycleAccumulator::default();
        let report = acc.finalize(0, 0);
        assert!(report.files.is_empty());
    }

    #[test]
    fn test_sort_order() {
        let mut acc = LifecycleAccumulator::new();
        // Active file
        acc.record_file("active.rs", FileActionKind::Create, 0, "Alice");
        acc.record_file("active.rs", FileActionKind::Modify, 9500, "Alice");
        // Dead file
        acc.record_file("dead.rs", FileActionKind::Create, 0, "Alice");
        acc.record_file("dead.rs", FileActionKind::Modify, 100, "Alice");
        // Ephemeral file
        acc.record_file("temp.rs", FileActionKind::Create, 1000, "Alice");
        acc.record_file("temp.rs", FileActionKind::Delete, 1000 + 5 * 86400, "Alice");

        let report = acc.finalize(0, 10000);
        // Sort order: ephemeral (0), dead (1), active (4)
        assert_eq!(report.files[0].stage, LifecycleStage::Ephemeral);
        assert_eq!(report.files[1].stage, LifecycleStage::Dead);
        assert_eq!(report.files[2].stage, LifecycleStage::Active);
    }

    #[test]
    fn test_ephemeral_boundary_exactly_30_days() {
        // Kills mutant: <= vs < in lifespan <= EPHEMERAL_THRESHOLD_DAYS
        // Exactly 30 days → should be Ephemeral (<=)
        let mut acc = LifecycleAccumulator::new();
        let create_ts = 1000;
        let delete_ts = create_ts + 30 * 86400; // exactly 30 days
        acc.record_file("exact30.rs", FileActionKind::Create, create_ts, "Alice");
        acc.record_file("exact30.rs", FileActionKind::Delete, delete_ts, "Alice");

        let report = acc.finalize(0, delete_ts + 100_000);
        assert_eq!(
            report.files[0].stage,
            LifecycleStage::Ephemeral,
            "exactly 30 days should be Ephemeral"
        );
    }

    #[test]
    fn test_not_ephemeral_at_31_days() {
        // 31 days → should be Deleted (not Ephemeral)
        let mut acc = LifecycleAccumulator::new();
        let create_ts = 1000;
        let delete_ts = create_ts + 31 * 86400; // 31 days
        acc.record_file("long31.rs", FileActionKind::Create, create_ts, "Alice");
        acc.record_file("long31.rs", FileActionKind::Delete, delete_ts, "Alice");

        let report = acc.finalize(0, delete_ts + 100_000);
        assert_eq!(
            report.files[0].stage,
            LifecycleStage::Deleted,
            "31 days should be Deleted, not Ephemeral"
        );
    }

    #[test]
    fn test_active_at_exact_threshold() {
        // Kills mutant: >= vs > in active_threshold check
        // active_threshold = t_max - 0.20 * time_span
        // With t_min=0, t_max=10000: active_threshold = 10000 - 2000 = 8000
        // last_modified=8000 exactly → should be Active (>=)
        let mut acc = LifecycleAccumulator::new();
        acc.record_file("edge.rs", FileActionKind::Create, 0, "Alice");
        acc.record_file("edge.rs", FileActionKind::Modify, 8000, "Alice");

        let report = acc.finalize(0, 10000);
        assert_eq!(
            report.files[0].stage,
            LifecycleStage::Active,
            "last_modified at exact active_threshold should be Active"
        );
    }

    #[test]
    fn test_dead_at_exact_threshold() {
        // Kills mutant: < vs <= in dead_threshold check
        // dead_threshold = t_max - 0.30 * time_span
        // With t_min=0, t_max=100000: dead_threshold = 100000 - 30000 = 70000
        // last_modified=70000 exactly → should be Stable (not Dead), since < 70000 is Dead
        let mut acc = LifecycleAccumulator::new();
        acc.record_file("border.rs", FileActionKind::Create, 0, "Alice");
        acc.record_file("border.rs", FileActionKind::Modify, 70000, "Alice");

        let report = acc.finalize(0, 100_000);
        assert_eq!(
            report.files[0].stage,
            LifecycleStage::Stable,
            "last_modified at exact dead_threshold should be Stable, not Dead"
        );
    }

    #[test]
    fn test_churn_rate_division() {
        // Kills mutant: replace / with * in churn_rate calculation
        // 3 creates + 2 deletes = 5 events, 3 unique files → 5/3 = 1.667
        let mut acc = LifecycleAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create, 1000, "Alice");
        acc.record_file("b.rs", FileActionKind::Create, 2000, "Alice");
        acc.record_file("c.rs", FileActionKind::Create, 3000, "Alice");
        acc.record_file("a.rs", FileActionKind::Delete, 4000, "Alice");
        acc.record_file("b.rs", FileActionKind::Delete, 5000, "Alice");

        let report = acc.finalize(1000, 5000);
        let expected = 5.0 / 3.0;
        assert!(
            (report.churn_rate - expected).abs() < 1e-10,
            "churn_rate={}, expected={}",
            report.churn_rate,
            expected
        );
    }

    #[test]
    fn test_avg_lifespan_days_exact() {
        // Kills mutant: replace / with * in avg_lifespan computation
        let mut acc = LifecycleAccumulator::new();
        // File a: 10 days old, File b: 20 days old → avg = 15 days
        acc.record_file("a.rs", FileActionKind::Create, 0, "Alice");
        acc.record_file("b.rs", FileActionKind::Create, 0, "Alice");

        let t_max = 20 * 86400; // 20 days
                                // But a.rs deleted at day 10
        acc.record_file("a.rs", FileActionKind::Delete, 10 * 86400, "Alice");

        let report = acc.finalize(0, t_max);
        // a.rs: age = 10 days (deleted), b.rs: age = 20 days
        // avg = (10 + 20) / 2 = 15
        assert!(
            (report.avg_lifespan_days - 15.0).abs() < 1e-10,
            "avg_lifespan_days={}, expected=15.0",
            report.avg_lifespan_days
        );
    }

    #[test]
    fn test_modifications_per_month_exact() {
        // Kills mutant: replace / with * in modifications_per_month
        let mut acc = LifecycleAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create, 0, "Alice");
        // 6 modifications over 60 days
        for i in 1..=6 {
            acc.record_file("a.rs", FileActionKind::Modify, i * 10 * 86400, "Alice");
        }

        let report = acc.finalize(0, 60 * 86400);
        let f = &report.files[0];
        // 6 modifications / 2 months = 3 per month
        let expected = 6.0 / (60.0 * 86400.0 / (30.0 * 86400.0));
        assert!(
            (f.modifications_per_month - expected).abs() < 1e-6,
            "mods_per_month={}, expected={}",
            f.modifications_per_month,
            expected
        );
    }

    #[test]
    fn test_stable_stage() {
        // A file that is not recently modified, not dead, and not deleted → Stable
        let mut acc = LifecycleAccumulator::new();
        // With t_min=0, t_max=100000:
        // active_threshold = 80000, dead_threshold = 70000
        // last_modified = 75000 → between dead and active → Stable
        acc.record_file("mid.rs", FileActionKind::Create, 0, "Alice");
        acc.record_file("mid.rs", FileActionKind::Modify, 75000, "Alice");

        let report = acc.finalize(0, 100_000);
        assert_eq!(report.files[0].stage, LifecycleStage::Stable);
    }
}
