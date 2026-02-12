// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Commit Complexity Score — identifies tangled commits that are difficult to
//! review and more likely to introduce defects.
//!
//! Scores each commit by the entropy of its actions multiplied by the number
//! of files and directories touched. Tangled commits (many files, many dirs,
//! mixed action types) are harder to review and empirically more error-prone.
//!
//! # Research Basis
//!
//! - Herzig & Zeller (2013) "The Impact of Tangled Changes on Bug Prediction
//!   Models" (MSR) — tangled changes reduce prediction accuracy by 10-40%
//! - Kirinuki et al. (2014) "Hey! Are You Committing Tangled Changes?"
//!   (ICPC) — automated detection of tangled commits
//!
//! # Algorithm
//!
//! ```text
//! complexity(c) = H(actions) × |files| × |directories|
//!
//! where:
//!   H(actions) = Shannon entropy of action distribution:
//!     H = -Σ p_i × log2(p_i) for action types {Create, Modify, Delete}
//!     max H ≈ 1.585 when all 3 action types equally present
//!
//!   |files| = number of files in the commit
//!   |directories| = number of distinct directories touched
//! ```
//!
//! Commits above the 95th percentile of complexity are flagged as "tangled."
//!
//! # Complexity
//!
//! - O(C) single pass where C = total commits

use rustc_hash::FxHashSet;

use super::FileActionKind;

/// Percentile threshold for flagging tangled commits.
const TANGLED_PERCENTILE: f64 = 0.95;

/// Commit complexity report for the repository.
#[derive(Debug, Clone)]
pub struct CommitComplexityReport {
    /// Per-commit complexity scores (all commits, sorted descending by score).
    pub commits: Vec<CommitComplexityEntry>,
    /// Average complexity score across all commits.
    pub avg_complexity: f64,
    /// Median complexity score.
    pub median_complexity: f64,
    /// 95th percentile complexity score (threshold for "tangled").
    pub p95_complexity: f64,
    /// Number of commits flagged as tangled.
    pub tangled_count: usize,
    /// Most complex commit's score.
    pub max_complexity: f64,
}

/// Complexity analysis for a single commit.
#[derive(Debug, Clone)]
pub struct CommitComplexityEntry {
    /// Commit index in the original sequence.
    pub commit_idx: usize,
    /// Author of the commit.
    pub author: String,
    /// Commit timestamp.
    pub timestamp: i64,
    /// Number of files in the commit.
    pub file_count: u32,
    /// Number of distinct directories touched.
    pub dir_count: u32,
    /// Shannon entropy of action types.
    pub action_entropy: f64,
    /// Overall complexity score.
    pub complexity_score: f64,
    /// Whether this commit exceeds the tangled threshold.
    pub is_tangled: bool,
}

/// Accumulates per-commit complexity data.
pub struct CommitComplexityAccumulator {
    /// Collected commit data: (index, author, timestamp, files, dirs, actions).
    entries: Vec<RawCommitEntry>,
}

/// Raw data for a single commit during accumulation.
struct RawCommitEntry {
    idx: usize,
    author: String,
    timestamp: i64,
    file_count: u32,
    dir_count: u32,
    creates: u32,
    modifies: u32,
    deletes: u32,
}

impl Default for CommitComplexityAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl CommitComplexityAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Records a commit for complexity analysis.
    pub fn record_commit(
        &mut self,
        author: &str,
        timestamp: i64,
        files: &[(&str, FileActionKind)],
    ) {
        let idx = self.entries.len();

        let mut dirs: FxHashSet<&str> = FxHashSet::default();
        let mut creates: u32 = 0;
        let mut modifies: u32 = 0;
        let mut deletes: u32 = 0;

        for (path, action) in files {
            // Extract directory
            if let Some(dir) = path.rsplit_once('/').map(|(d, _)| d) {
                dirs.insert(dir);
            } else {
                dirs.insert(".");
            }

            match action {
                FileActionKind::Create => creates += 1,
                FileActionKind::Modify => modifies += 1,
                FileActionKind::Delete => deletes += 1,
            }
        }

        self.entries.push(RawCommitEntry {
            idx,
            author: author.to_string(),
            timestamp,
            file_count: files.len() as u32,
            dir_count: dirs.len() as u32,
            creates,
            modifies,
            deletes,
        });
    }

    /// Finalizes the commit complexity report.
    #[must_use]
    pub fn finalize(self) -> CommitComplexityReport {
        if self.entries.is_empty() {
            return CommitComplexityReport {
                commits: Vec::new(),
                avg_complexity: 0.0,
                median_complexity: 0.0,
                p95_complexity: 0.0,
                tangled_count: 0,
                max_complexity: 0.0,
            };
        }

        // Compute complexity for each commit
        let mut scores: Vec<f64> = Vec::with_capacity(self.entries.len());
        let mut commits: Vec<CommitComplexityEntry> = Vec::with_capacity(self.entries.len());

        for entry in &self.entries {
            let entropy = action_entropy(entry.creates, entry.modifies, entry.deletes);
            let score = entropy * f64::from(entry.file_count) * f64::from(entry.dir_count);
            scores.push(score);

            commits.push(CommitComplexityEntry {
                commit_idx: entry.idx,
                author: entry.author.clone(),
                timestamp: entry.timestamp,
                file_count: entry.file_count,
                dir_count: entry.dir_count,
                action_entropy: entropy,
                complexity_score: score,
                is_tangled: false, // set below
            });
        }

        // Compute statistics
        let avg_complexity = scores.iter().sum::<f64>() / scores.len() as f64;

        let mut sorted_scores = scores.clone();
        sorted_scores.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

        let median_complexity = sorted_scores[sorted_scores.len() / 2];
        let p95_idx = ((sorted_scores.len() as f64 * TANGLED_PERCENTILE) as usize)
            .min(sorted_scores.len() - 1);
        let p95_complexity = sorted_scores[p95_idx];
        let max_complexity = sorted_scores.last().copied().unwrap_or(0.0);

        // Flag tangled commits
        let mut tangled_count = 0;
        for commit in &mut commits {
            if commit.complexity_score > p95_complexity {
                commit.is_tangled = true;
                tangled_count += 1;
            }
        }

        // Sort by complexity descending (most complex first)
        commits.sort_by(|a, b| {
            b.complexity_score
                .partial_cmp(&a.complexity_score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        // Truncate to top 100 for display
        commits.truncate(100);

        CommitComplexityReport {
            commits,
            avg_complexity,
            median_complexity,
            p95_complexity,
            tangled_count,
            max_complexity,
        }
    }
}

/// Computes Shannon entropy of the action distribution.
///
/// H = -Σ `p_i` × `log2(p_i)` for Create/Modify/Delete proportions.
///
/// Returns 0 if only one action type present.
fn action_entropy(creates: u32, modifies: u32, deletes: u32) -> f64 {
    let total = creates + modifies + deletes;
    if total == 0 {
        return 0.0;
    }

    let total_f = f64::from(total);
    let mut entropy = 0.0;

    for &count in &[creates, modifies, deletes] {
        if count > 0 {
            let p = f64::from(count) / total_f;
            entropy -= p * p.log2();
        }
    }

    entropy
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = CommitComplexityAccumulator::new();
        let report = acc.finalize();
        assert!(report.commits.is_empty());
        assert!((report.avg_complexity - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_default_impl() {
        let acc = CommitComplexityAccumulator::default();
        let report = acc.finalize();
        assert!(report.commits.is_empty());
    }

    #[test]
    fn test_single_file_commit() {
        let mut acc = CommitComplexityAccumulator::new();
        acc.record_commit("Alice", 1000, &[("a.rs", FileActionKind::Modify)]);
        let report = acc.finalize();
        assert_eq!(report.commits.len(), 1);
        let c = &report.commits[0];
        assert_eq!(c.file_count, 1);
        assert_eq!(c.dir_count, 1);
        // Single action type → entropy = 0
        assert!((c.action_entropy - 0.0).abs() < f64::EPSILON);
        // Score = 0 × 1 × 1 = 0
        assert!((c.complexity_score - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_mixed_actions_entropy() {
        // Equal distribution of 3 action types → max entropy
        let entropy = action_entropy(1, 1, 1);
        let expected = (3.0_f64).log2(); // ≈ 1.585
        assert!(
            (entropy - expected).abs() < 1e-10,
            "entropy={}, expected={}",
            entropy,
            expected
        );
    }

    #[test]
    fn test_single_action_type_zero_entropy() {
        assert!((action_entropy(5, 0, 0) - 0.0).abs() < f64::EPSILON);
        assert!((action_entropy(0, 5, 0) - 0.0).abs() < f64::EPSILON);
        assert!((action_entropy(0, 0, 5) - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_two_action_types_entropy() {
        // Equal split of 2 types → entropy = log2(2) = 1.0
        let entropy = action_entropy(5, 5, 0);
        assert!(
            (entropy - 1.0).abs() < 1e-10,
            "entropy={}, expected=1.0",
            entropy
        );
    }

    #[test]
    fn test_tangled_commit_detection() {
        let mut acc = CommitComplexityAccumulator::new();

        // 20 simple commits (1 file, 1 action type)
        for i in 0..20 {
            acc.record_commit("Alice", 1000 + i, &[("a.rs", FileActionKind::Modify)]);
        }

        // 1 complex commit (many files, mixed actions, many dirs)
        acc.record_commit(
            "Bob",
            2000,
            &[
                ("src/main.rs", FileActionKind::Modify),
                ("src/lib.rs", FileActionKind::Modify),
                ("tests/test.rs", FileActionKind::Create),
                ("docs/readme.md", FileActionKind::Create),
                ("old/legacy.rs", FileActionKind::Delete),
            ],
        );

        let report = acc.finalize();
        assert!(report.tangled_count >= 1, "should detect tangled commit");
        assert!(
            report.max_complexity > 0.0,
            "max complexity should be > 0 for mixed-action commit"
        );
    }

    #[test]
    fn test_directory_extraction() {
        let mut acc = CommitComplexityAccumulator::new();
        acc.record_commit(
            "Alice",
            1000,
            &[
                ("src/a.rs", FileActionKind::Modify),
                ("src/b.rs", FileActionKind::Modify),
                ("tests/t.rs", FileActionKind::Create),
            ],
        );
        let report = acc.finalize();
        let c = &report.commits[0];
        assert_eq!(c.file_count, 3);
        assert_eq!(c.dir_count, 2); // "src" and "tests"
    }

    #[test]
    fn test_root_files_dir_dot() {
        let mut acc = CommitComplexityAccumulator::new();
        acc.record_commit(
            "Alice",
            1000,
            &[
                ("Cargo.toml", FileActionKind::Modify),
                (".gitignore", FileActionKind::Modify),
            ],
        );
        let report = acc.finalize();
        let c = &report.commits[0];
        assert_eq!(c.dir_count, 1); // both root → "."
    }

    #[test]
    fn test_sorted_by_complexity_descending() {
        let mut acc = CommitComplexityAccumulator::new();
        // Simple commit
        acc.record_commit("Alice", 1000, &[("a.rs", FileActionKind::Modify)]);
        // Complex commit
        acc.record_commit(
            "Bob",
            2000,
            &[
                ("src/a.rs", FileActionKind::Create),
                ("src/b.rs", FileActionKind::Modify),
                ("tests/c.rs", FileActionKind::Delete),
            ],
        );
        let report = acc.finalize();
        for w in report.commits.windows(2) {
            assert!(
                w[0].complexity_score >= w[1].complexity_score - 1e-10,
                "not sorted: {} < {}",
                w[0].complexity_score,
                w[1].complexity_score
            );
        }
    }

    #[test]
    fn test_statistics_computed() {
        let mut acc = CommitComplexityAccumulator::new();
        for i in 0..10 {
            acc.record_commit("Alice", 1000 + i, &[("a.rs", FileActionKind::Modify)]);
        }
        let report = acc.finalize();
        assert!(report.avg_complexity >= 0.0);
        assert!(report.median_complexity >= 0.0);
        assert!(report.p95_complexity >= 0.0);
        assert!(report.max_complexity >= 0.0);
    }

    #[test]
    fn test_zero_files_entropy() {
        let entropy = action_entropy(0, 0, 0);
        assert!((entropy - 0.0).abs() < f64::EPSILON);
    }

    // ── Property-based tests ──

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Action entropy is in [0, log2(3)] ≈ [0, 1.585].
            #[test]
            fn prop_entropy_bounded(c in 0u32..20, m in 0u32..20, d in 0u32..20) {
                let h = action_entropy(c, m, d);
                prop_assert!(h >= 0.0, "negative entropy: {}", h);
                prop_assert!(h <= 3.0_f64.log2() + 1e-10,
                    "entropy {} exceeds max log2(3)={}", h, 3.0_f64.log2());
            }

            /// Complexity score is non-negative.
            #[test]
            fn prop_complexity_non_negative(n_commits in 1usize..20) {
                let mut acc = CommitComplexityAccumulator::new();
                for i in 0..n_commits {
                    acc.record_commit(
                        "Alice",
                        i64::try_from(i).unwrap() * 1000,
                        &[("a.rs", FileActionKind::Modify)],
                    );
                }
                let report = acc.finalize();
                for c in &report.commits {
                    prop_assert!(c.complexity_score >= 0.0,
                        "negative score: {}", c.complexity_score);
                }
            }
        }
    }
}
