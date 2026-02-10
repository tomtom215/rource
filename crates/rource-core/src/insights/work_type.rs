// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Work-type mix analysis.
//!
//! Classifies commits by the ratio of Create/Modify/Delete actions to infer
//! whether the team is primarily building new features, maintaining existing
//! code, or cleaning up technical debt.
//!
//! # Research Basis
//!
//! Hindle et al. (2008) "Large-Scale Model of Software Development Activity"
//! showed that software development activities follow predictable patterns.
//! Mockus & Votta (2000) "Identifying Reasons for Software Changes" established
//! that the type of change (new code vs. maintenance) strongly predicts quality
//! outcomes.
//!
//! # Algorithm
//!
//! For each commit, compute the ratio of Create/Modify/Delete actions:
//! - **Feature**: `create_ratio` > 0.5 (primarily adding new files)
//! - **Maintenance**: `modify_ratio` > 0.7 (primarily modifying existing files)
//! - **Cleanup**: `delete_ratio` > 0.3 (significant deletion activity)
//! - **Mixed**: none of the above thresholds met
//!
//! # Complexity
//!
//! - Accumulation: O(1) per commit
//! - Finalization: O(N) where N = number of commits

use super::FileActionKind;

/// Classification of a commit's primary work type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkType {
    /// Primarily creating new files (`create_ratio` > 0.5).
    Feature,
    /// Primarily modifying existing files (`modify_ratio` > 0.7).
    Maintenance,
    /// Significant file deletion (`delete_ratio` > 0.3).
    Cleanup,
    /// No single dominant action type.
    Mixed,
}

/// Work type classification for a single commit.
#[derive(Debug, Clone)]
pub struct CommitWorkType {
    /// Unix timestamp of the commit.
    pub timestamp: i64,
    /// Classified work type.
    pub work_type: WorkType,
    /// Ratio of create actions (0.0-1.0).
    pub create_ratio: f64,
    /// Ratio of modify actions (0.0-1.0).
    pub modify_ratio: f64,
    /// Ratio of delete actions (0.0-1.0).
    pub delete_ratio: f64,
    /// Total file actions in this commit.
    pub file_count: usize,
}

/// Aggregate work type statistics for the repository.
#[derive(Debug, Clone)]
pub struct WorkTypeReport {
    /// Per-commit classifications.
    pub commits: Vec<CommitWorkType>,
    /// Percentage of commits classified as Feature (0.0-100.0).
    pub feature_pct: f64,
    /// Percentage of commits classified as Maintenance (0.0-100.0).
    pub maintenance_pct: f64,
    /// Percentage of commits classified as Cleanup (0.0-100.0).
    pub cleanup_pct: f64,
    /// Percentage of commits classified as Mixed (0.0-100.0).
    pub mixed_pct: f64,
    /// Dominant work type across all commits.
    pub dominant_type: WorkType,
    /// Total commits analyzed.
    pub total_commits: usize,
}

/// Accumulates work type data during commit processing.
pub struct WorkTypeAccumulator {
    /// Classified commits.
    commits: Vec<CommitWorkType>,
    /// Running counters for classification totals.
    feature_count: usize,
    maintenance_count: usize,
    cleanup_count: usize,
    mixed_count: usize,
}

impl Default for WorkTypeAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl WorkTypeAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            commits: Vec::new(),
            feature_count: 0,
            maintenance_count: 0,
            cleanup_count: 0,
            mixed_count: 0,
        }
    }

    /// Records a commit with its file action counts.
    ///
    /// # Arguments
    ///
    /// * `timestamp` - Unix epoch seconds
    /// * `creates` - Number of create actions
    /// * `modifies` - Number of modify actions
    /// * `deletes` - Number of delete actions
    pub fn record_commit(&mut self, timestamp: i64, creates: u32, modifies: u32, deletes: u32) {
        let total = creates + modifies + deletes;
        if total == 0 {
            return;
        }

        let total_f = f64::from(total);
        let create_ratio = f64::from(creates) / total_f;
        let modify_ratio = f64::from(modifies) / total_f;
        let delete_ratio = f64::from(deletes) / total_f;

        let work_type = classify_work_type(create_ratio, modify_ratio, delete_ratio);

        match work_type {
            WorkType::Feature => self.feature_count += 1,
            WorkType::Maintenance => self.maintenance_count += 1,
            WorkType::Cleanup => self.cleanup_count += 1,
            WorkType::Mixed => self.mixed_count += 1,
        }

        self.commits.push(CommitWorkType {
            timestamp,
            work_type,
            create_ratio,
            modify_ratio,
            delete_ratio,
            file_count: total as usize,
        });
    }

    /// Finalizes the accumulator into a [`WorkTypeReport`].
    #[must_use]
    pub fn finalize(self) -> WorkTypeReport {
        let total = self.commits.len();
        if total == 0 {
            return WorkTypeReport {
                commits: Vec::new(),
                feature_pct: 0.0,
                maintenance_pct: 0.0,
                cleanup_pct: 0.0,
                mixed_pct: 0.0,
                dominant_type: WorkType::Mixed,
                total_commits: 0,
            };
        }

        let total_f = total as f64;
        let feature_pct = self.feature_count as f64 / total_f * 100.0;
        let maintenance_pct = self.maintenance_count as f64 / total_f * 100.0;
        let cleanup_pct = self.cleanup_count as f64 / total_f * 100.0;
        let mixed_pct = self.mixed_count as f64 / total_f * 100.0;

        let dominant_type = determine_dominant(&[
            (WorkType::Feature, self.feature_count),
            (WorkType::Maintenance, self.maintenance_count),
            (WorkType::Cleanup, self.cleanup_count),
            (WorkType::Mixed, self.mixed_count),
        ]);

        WorkTypeReport {
            commits: self.commits,
            feature_pct,
            maintenance_pct,
            cleanup_pct,
            mixed_pct,
            dominant_type,
            total_commits: total,
        }
    }
}

/// Classifies a commit based on action ratios.
fn classify_work_type(create_ratio: f64, modify_ratio: f64, delete_ratio: f64) -> WorkType {
    // Priority: cleanup > feature > maintenance > mixed
    // Cleanup checked first because high-delete commits are notable regardless of other ratios
    if delete_ratio > 0.3 {
        WorkType::Cleanup
    } else if create_ratio > 0.5 {
        WorkType::Feature
    } else if modify_ratio > 0.7 {
        WorkType::Maintenance
    } else {
        WorkType::Mixed
    }
}

/// Determines the dominant work type from counts.
fn determine_dominant(counts: &[(WorkType, usize)]) -> WorkType {
    counts
        .iter()
        .max_by_key(|(_, count)| *count)
        .map_or(WorkType::Mixed, |(wt, _)| *wt)
}

/// Counts file actions by type from a list of file records.
///
/// # Arguments
///
/// * `files` - Slice of `(action,)` tuples
///
/// Returns `(creates, modifies, deletes)`.
pub fn count_actions(actions: &[FileActionKind]) -> (u32, u32, u32) {
    let mut creates = 0u32;
    let mut modifies = 0u32;
    let mut deletes = 0u32;
    for &action in actions {
        match action {
            FileActionKind::Create => creates += 1,
            FileActionKind::Modify => modifies += 1,
            FileActionKind::Delete => deletes += 1,
        }
    }
    (creates, modifies, deletes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = WorkTypeAccumulator::new();
        let report = acc.finalize();
        assert_eq!(report.total_commits, 0);
        assert!((report.feature_pct - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_feature_classification() {
        let mut acc = WorkTypeAccumulator::new();
        // 3 creates, 1 modify, 0 deletes → create_ratio = 0.75 > 0.5 → Feature
        acc.record_commit(1000, 3, 1, 0);
        let report = acc.finalize();
        assert_eq!(report.commits[0].work_type, WorkType::Feature);
        assert!((report.feature_pct - 100.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_maintenance_classification() {
        let mut acc = WorkTypeAccumulator::new();
        // 0 creates, 8 modifies, 0 deletes → modify_ratio = 1.0 > 0.7 → Maintenance
        acc.record_commit(1000, 0, 8, 0);
        let report = acc.finalize();
        assert_eq!(report.commits[0].work_type, WorkType::Maintenance);
        assert!((report.maintenance_pct - 100.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_cleanup_classification() {
        let mut acc = WorkTypeAccumulator::new();
        // 1 create, 1 modify, 3 deletes → delete_ratio = 0.6 > 0.3 → Cleanup
        acc.record_commit(1000, 1, 1, 3);
        let report = acc.finalize();
        assert_eq!(report.commits[0].work_type, WorkType::Cleanup);
        assert!((report.cleanup_pct - 100.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_mixed_classification() {
        let mut acc = WorkTypeAccumulator::new();
        // 2 creates, 3 modifies, 1 delete → no threshold met
        // create_ratio = 2/6 = 0.33, modify_ratio = 3/6 = 0.5, delete_ratio = 1/6 = 0.17
        acc.record_commit(1000, 2, 3, 1);
        let report = acc.finalize();
        assert_eq!(report.commits[0].work_type, WorkType::Mixed);
    }

    #[test]
    fn test_cleanup_priority_over_feature() {
        let mut acc = WorkTypeAccumulator::new();
        // 4 creates, 0 modifies, 3 deletes
        // create_ratio = 4/7 = 0.57 > 0.5 (Feature)
        // delete_ratio = 3/7 = 0.43 > 0.3 (Cleanup)
        // Cleanup takes priority
        acc.record_commit(1000, 4, 0, 3);
        let report = acc.finalize();
        assert_eq!(report.commits[0].work_type, WorkType::Cleanup);
    }

    #[test]
    fn test_zero_file_commit_skipped() {
        let mut acc = WorkTypeAccumulator::new();
        acc.record_commit(1000, 0, 0, 0);
        let report = acc.finalize();
        assert_eq!(report.total_commits, 0);
        assert!(report.commits.is_empty());
    }

    #[test]
    fn test_percentages_sum_to_100() {
        let mut acc = WorkTypeAccumulator::new();
        acc.record_commit(1000, 5, 0, 0); // Feature
        acc.record_commit(2000, 0, 10, 0); // Maintenance
        acc.record_commit(3000, 0, 0, 5); // Cleanup
        acc.record_commit(4000, 2, 3, 1); // Mixed

        let report = acc.finalize();
        let sum =
            report.feature_pct + report.maintenance_pct + report.cleanup_pct + report.mixed_pct;
        assert!(
            (sum - 100.0).abs() < 1e-10,
            "percentages must sum to 100, got {sum}"
        );
        assert_eq!(report.total_commits, 4);
    }

    #[test]
    fn test_dominant_type() {
        let mut acc = WorkTypeAccumulator::new();
        acc.record_commit(1000, 5, 0, 0); // Feature
        acc.record_commit(2000, 5, 0, 0); // Feature
        acc.record_commit(3000, 5, 0, 0); // Feature
        acc.record_commit(4000, 0, 10, 0); // Maintenance

        let report = acc.finalize();
        assert_eq!(report.dominant_type, WorkType::Feature);
    }

    #[test]
    fn test_ratios_exact() {
        let mut acc = WorkTypeAccumulator::new();
        // 2 creates, 3 modifies, 5 deletes → total = 10
        acc.record_commit(1000, 2, 3, 5);
        let report = acc.finalize();
        let c = &report.commits[0];
        assert!((c.create_ratio - 0.2).abs() < f64::EPSILON);
        assert!((c.modify_ratio - 0.3).abs() < f64::EPSILON);
        assert!((c.delete_ratio - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_count_actions() {
        let actions = vec![
            FileActionKind::Create,
            FileActionKind::Modify,
            FileActionKind::Modify,
            FileActionKind::Delete,
        ];
        let (c, m, d) = count_actions(&actions);
        assert_eq!(c, 1);
        assert_eq!(m, 2);
        assert_eq!(d, 1);
    }

    #[test]
    fn test_default() {
        let acc = WorkTypeAccumulator::default();
        let report = acc.finalize();
        assert_eq!(report.total_commits, 0);
    }

    // --- Mutation-killing tests ---

    #[test]
    fn test_delete_ratio_exactly_at_boundary() {
        // delete_ratio = 0.3 exactly → NOT Cleanup (kills `>=` vs `>` mutant)
        // 3 deletes out of 10 total = 0.3
        let mut acc = WorkTypeAccumulator::new();
        acc.record_commit(1000, 0, 7, 3);
        let report = acc.finalize();
        // delete_ratio = 3/10 = 0.3, NOT > 0.3 → not Cleanup
        // modify_ratio = 7/10 = 0.7, NOT > 0.7 → not Maintenance
        // create_ratio = 0/10 = 0.0 → not Feature
        // → Mixed
        assert_eq!(report.commits[0].work_type, WorkType::Mixed);
    }

    #[test]
    fn test_delete_ratio_just_above_boundary() {
        // delete_ratio = 0.31 → Cleanup (confirms strict >0.3)
        // Approximate: 31 deletes out of 100 = 0.31
        let mut acc = WorkTypeAccumulator::new();
        acc.record_commit(1000, 0, 69, 31);
        let report = acc.finalize();
        assert_eq!(report.commits[0].work_type, WorkType::Cleanup);
    }

    #[test]
    fn test_create_ratio_exactly_at_boundary() {
        // create_ratio = 0.5 exactly → NOT Feature (kills `>=` vs `>` mutant)
        // 5 creates out of 10 total = 0.5
        let mut acc = WorkTypeAccumulator::new();
        acc.record_commit(1000, 5, 5, 0);
        let report = acc.finalize();
        // create_ratio = 5/10 = 0.5, NOT > 0.5 → not Feature
        // modify_ratio = 5/10 = 0.5 → not Maintenance (need >0.7)
        // delete_ratio = 0 → not Cleanup
        // → Mixed
        assert_eq!(report.commits[0].work_type, WorkType::Mixed);
    }

    #[test]
    fn test_create_ratio_just_above_boundary() {
        // create_ratio > 0.5 → Feature
        // 51 creates out of 100 = 0.51
        let mut acc = WorkTypeAccumulator::new();
        acc.record_commit(1000, 51, 49, 0);
        let report = acc.finalize();
        assert_eq!(report.commits[0].work_type, WorkType::Feature);
    }

    #[test]
    fn test_modify_ratio_exactly_at_boundary() {
        // modify_ratio = 0.7 exactly → NOT Maintenance (kills `>=` vs `>` mutant)
        // 7 modifies out of 10 = 0.7, 3 creates, 0 deletes
        let mut acc = WorkTypeAccumulator::new();
        acc.record_commit(1000, 3, 7, 0);
        let report = acc.finalize();
        // create_ratio = 3/10 = 0.3 → not Feature
        // modify_ratio = 7/10 = 0.7, NOT > 0.7 → not Maintenance
        // delete_ratio = 0 → not Cleanup
        // → Mixed
        assert_eq!(report.commits[0].work_type, WorkType::Mixed);
    }

    #[test]
    fn test_modify_ratio_just_above_boundary() {
        // modify_ratio > 0.7 → Maintenance
        // 71 modifies out of 100 = 0.71
        let mut acc = WorkTypeAccumulator::new();
        acc.record_commit(1000, 29, 71, 0);
        let report = acc.finalize();
        // create_ratio = 29/100 = 0.29 → not Feature
        // delete_ratio = 0 → not Cleanup
        // modify_ratio = 71/100 = 0.71 > 0.7 → Maintenance
        assert_eq!(report.commits[0].work_type, WorkType::Maintenance);
    }

    #[test]
    fn test_percentage_division_exact() {
        // 1 Feature out of 4 commits = 25.0% exactly
        // Kills `/` vs `*` mutant in percentage calculation
        let mut acc = WorkTypeAccumulator::new();
        acc.record_commit(1000, 10, 0, 0); // Feature
        acc.record_commit(2000, 0, 10, 0); // Maintenance
        acc.record_commit(3000, 0, 0, 10); // Cleanup
        acc.record_commit(4000, 2, 3, 1); // Mixed
        let report = acc.finalize();
        assert!(
            (report.feature_pct - 25.0).abs() < f64::EPSILON,
            "feature_pct={}, expected=25.0",
            report.feature_pct
        );
        assert!(
            (report.maintenance_pct - 25.0).abs() < f64::EPSILON,
            "maintenance_pct={}, expected=25.0",
            report.maintenance_pct
        );
        assert!(
            (report.cleanup_pct - 25.0).abs() < f64::EPSILON,
            "cleanup_pct={}, expected=25.0",
            report.cleanup_pct
        );
        assert!(
            (report.mixed_pct - 25.0).abs() < f64::EPSILON,
            "mixed_pct={}, expected=25.0",
            report.mixed_pct
        );
    }

    #[test]
    fn test_file_count_stored_correctly() {
        let mut acc = WorkTypeAccumulator::new();
        acc.record_commit(1000, 3, 4, 5);
        let report = acc.finalize();
        assert_eq!(report.commits[0].file_count, 12);
    }

    #[test]
    fn test_dominant_type_tie_breaking() {
        // When two types tie, max_by_key picks the first with max count.
        // Feature and Maintenance each have 1 commit.
        let mut acc = WorkTypeAccumulator::new();
        acc.record_commit(1000, 10, 0, 0); // Feature
        acc.record_commit(2000, 0, 10, 0); // Maintenance
        let report = acc.finalize();
        // Both have count 1; dominant should be one of them (deterministic via order)
        assert!(
            report.dominant_type == WorkType::Feature
                || report.dominant_type == WorkType::Maintenance
        );
    }

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Percentages always sum to approximately 100.
            #[test]
            fn prop_percentages_sum_to_100(
                n_commits in 1usize..20,
                seed in 0u64..1000
            ) {
                let mut acc = WorkTypeAccumulator::new();
                for i in 0..n_commits {
                    let v = (seed + u64::try_from(i).unwrap()) % 4;
                    let (c, m, d) = match v {
                        0 => (10u32, 0u32, 0u32),   // Feature
                        1 => (0, 10, 0),              // Maintenance
                        2 => (0, 0, 10),              // Cleanup
                        _ => (3, 3, 4),               // Mixed
                    };
                    acc.record_commit(i64::try_from(i).unwrap() * 1000, c, m, d);
                }
                let report = acc.finalize();
                let sum = report.feature_pct + report.maintenance_pct
                    + report.cleanup_pct + report.mixed_pct;
                prop_assert!(
                    (sum - 100.0).abs() < 1e-6,
                    "pct sum={}, expected 100.0", sum
                );
            }

            /// All percentages are in [0, 100].
            #[test]
            fn prop_percentages_bounded(
                n_commits in 1usize..20,
                seed in 0u64..1000
            ) {
                let mut acc = WorkTypeAccumulator::new();
                for i in 0..n_commits {
                    let v = (seed + u64::try_from(i).unwrap()) % 3;
                    let (c, m, d) = match v {
                        0 => (8u32, 1u32, 1u32),
                        1 => (1, 8, 1),
                        _ => (1, 1, 8),
                    };
                    acc.record_commit(i64::try_from(i).unwrap() * 1000, c, m, d);
                }
                let report = acc.finalize();
                for pct in [report.feature_pct, report.maintenance_pct,
                            report.cleanup_pct, report.mixed_pct] {
                    prop_assert!((0.0..=100.0).contains(&pct), "pct={} out of [0,100]", pct);
                }
            }

            /// Ratios in each commit sum to 1.0.
            #[test]
            fn prop_ratios_sum_to_one(creates in 0u32..20, modifies in 0u32..20, deletes in 0u32..20) {
                prop_assume!(creates + modifies + deletes > 0);
                let mut acc = WorkTypeAccumulator::new();
                acc.record_commit(1000, creates, modifies, deletes);
                let report = acc.finalize();
                let commit = &report.commits[0];
                let sum = commit.create_ratio + commit.modify_ratio + commit.delete_ratio;
                prop_assert!(
                    (sum - 1.0).abs() < 1e-10,
                    "ratio sum={}, expected 1.0", sum
                );
            }

            /// Total commits matches expected count.
            #[test]
            fn prop_total_commits(n_commits in 1usize..30) {
                let mut acc = WorkTypeAccumulator::new();
                for i in 0..n_commits {
                    acc.record_commit(i64::try_from(i).unwrap() * 1000, 5, 3, 2);
                }
                let report = acc.finalize();
                prop_assert_eq!(report.total_commits, n_commits);
            }
        }
    }
}
