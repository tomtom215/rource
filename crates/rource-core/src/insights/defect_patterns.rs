// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Defect-Introducing Change Patterns — identifies files that exhibit
//! burst-edit patterns following large commits, which are empirical
//! proxies for defect-introducing changes.
//!
//! Without explicit bug labels, we use a proxy heuristic: files that receive
//! rapid consecutive edits (a "burst") shortly after a large commit are likely
//! undergoing fix-up for defects introduced by that large commit.
//!
//! # Research Basis
//!
//! - Kim et al. (2008) "Classifying Software Changes: Clean or Buggy?" (TSE)
//!   — change classification using process metrics
//! - Sliwerski et al. (2005) "When Do Changes Induce Fixes?" (MSR)
//!   — SZZ algorithm for identifying defect-introducing changes
//!
//! # Algorithm
//!
//! 1. For each author, compute mean and σ of `files_per_commit`.
//! 2. A "large commit" is one where `files_per_commit` > mean + 2σ for that author.
//! 3. A "burst" is ≥ 2 edits to the same file within `BURST_WINDOW_SECS`.
//! 4. Score = P(`burst_follows_large_commit` | file) for each file.
//! 5. Files with high scores are defect-introducing hotspots.
//!
//! # Complexity
//!
//! - O(C × `F_avg`) single pass with lookback

use rustc_hash::FxHashMap;

/// Time window for detecting burst edits (3 days in seconds).
const BURST_WINDOW_SECS: i64 = 3 * 86400;

/// Minimum commits to compute meaningful statistics for an author.
const MIN_AUTHOR_COMMITS: usize = 3;

/// Defect-introducing change patterns report.
#[derive(Debug, Clone)]
pub struct DefectPatternsReport {
    /// Per-file defect-introducing pattern scores.
    pub files: Vec<FileDefectPattern>,
    /// Total large commits detected.
    pub large_commit_count: usize,
    /// Total burst-after-large events detected.
    pub burst_after_large_count: usize,
    /// Average defect pattern score across files.
    pub avg_score: f64,
    /// Number of files with high defect pattern risk (score > 0.5).
    pub high_risk_count: usize,
}

/// Defect-introducing pattern analysis for a single file.
#[derive(Debug, Clone)]
pub struct FileDefectPattern {
    /// File path.
    pub path: String,
    /// Number of times a burst followed a large commit touching this file.
    pub burst_after_large: u32,
    /// Total times this file was in a large commit.
    pub large_commit_appearances: u32,
    /// Defect pattern score: `burst_after_large` / `large_commit_appearances`.
    pub score: f64,
    /// Total edits to this file.
    pub total_edits: u32,
}

/// Accumulates commit data for defect pattern detection.
pub struct DefectPatternsAccumulator {
    /// Per-author commit sizes for computing mean / σ.
    author_commit_sizes: FxHashMap<String, Vec<u32>>,
    /// Commit log: (timestamp, author, `file_count`, `file_paths`).
    commits: Vec<CommitEntry>,
}

struct FileEdit {
    timestamp: i64,
    from_large_commit: bool,
}

struct CommitEntry {
    timestamp: i64,
    author: String,
    file_count: u32,
    paths: Vec<String>,
}

impl Default for DefectPatternsAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl DefectPatternsAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            author_commit_sizes: FxHashMap::default(),
            commits: Vec::new(),
        }
    }

    /// Records a commit for defect pattern analysis.
    pub fn record_commit(&mut self, author: &str, timestamp: i64, file_paths: &[&str]) {
        let file_count = file_paths.len() as u32;

        self.author_commit_sizes
            .entry(author.to_string())
            .or_default()
            .push(file_count);

        let paths: Vec<String> = file_paths.iter().copied().map(String::from).collect();
        self.commits.push(CommitEntry {
            timestamp,
            author: author.to_string(),
            file_count,
            paths,
        });
    }

    /// Finalizes the defect patterns report.
    #[must_use]
    pub fn finalize(self) -> DefectPatternsReport {
        if self.commits.is_empty() {
            return DefectPatternsReport {
                files: Vec::new(),
                large_commit_count: 0,
                burst_after_large_count: 0,
                avg_score: 0.0,
                high_risk_count: 0,
            };
        }

        // Step 1: Compute per-author thresholds for "large commit"
        let thresholds: FxHashMap<String, f64> = self
            .author_commit_sizes
            .iter()
            .filter(|(_, sizes)| sizes.len() >= MIN_AUTHOR_COMMITS)
            .map(|(author, sizes)| {
                let mean = sizes.iter().map(|&s| f64::from(s)).sum::<f64>() / sizes.len() as f64;
                let variance = sizes
                    .iter()
                    .map(|&s| (f64::from(s) - mean).powi(2))
                    .sum::<f64>()
                    / sizes.len() as f64;
                let std_dev = variance.sqrt();
                (author.clone(), mean + 2.0 * std_dev)
            })
            .collect();

        // Step 2: Tag each commit as large or not, build per-file edit timeline
        let mut file_edits: FxHashMap<String, Vec<FileEdit>> = FxHashMap::default();
        let mut large_commit_count = 0;

        for commit in &self.commits {
            let is_large = thresholds
                .get(&commit.author)
                .is_some_and(|&threshold| f64::from(commit.file_count) > threshold);

            if is_large {
                large_commit_count += 1;
            }

            for path in &commit.paths {
                file_edits.entry(path.clone()).or_default().push(FileEdit {
                    timestamp: commit.timestamp,
                    from_large_commit: is_large,
                });
            }
        }

        // Step 3: For each file, detect bursts following large commits
        let mut files: Vec<FileDefectPattern> = Vec::new();
        let mut total_burst_after_large = 0;

        for (path, edits) in &file_edits {
            let total_edits = edits.len() as u32;
            let large_commit_appearances =
                edits.iter().filter(|e| e.from_large_commit).count() as u32;

            if large_commit_appearances == 0 {
                continue;
            }

            // Count burst-after-large events
            let mut burst_after_large: u32 = 0;

            for (i, edit) in edits.iter().enumerate() {
                if !edit.from_large_commit {
                    continue;
                }

                // Look ahead for burst edits within BURST_WINDOW_SECS
                let mut burst_edits = 0;
                for subsequent in edits.iter().skip(i + 1) {
                    if subsequent.timestamp - edit.timestamp > BURST_WINDOW_SECS {
                        break;
                    }
                    if !subsequent.from_large_commit {
                        burst_edits += 1;
                    }
                }

                if burst_edits >= 2 {
                    burst_after_large += 1;
                }
            }

            total_burst_after_large += burst_after_large as usize;

            let score = if large_commit_appearances > 0 {
                f64::from(burst_after_large) / f64::from(large_commit_appearances)
            } else {
                0.0
            };

            files.push(FileDefectPattern {
                path: path.clone(),
                burst_after_large,
                large_commit_appearances,
                score,
                total_edits,
            });
        }

        // Sort by score descending
        files.sort_by(|a, b| {
            b.score
                .partial_cmp(&a.score)
                .unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| b.burst_after_large.cmp(&a.burst_after_large))
        });

        let avg_score = if files.is_empty() {
            0.0
        } else {
            files.iter().map(|f| f.score).sum::<f64>() / files.len() as f64
        };
        let high_risk_count = files.iter().filter(|f| f.score > 0.5).count();

        DefectPatternsReport {
            files,
            large_commit_count,
            burst_after_large_count: total_burst_after_large,
            avg_score,
            high_risk_count,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = DefectPatternsAccumulator::new();
        let report = acc.finalize();
        assert!(report.files.is_empty());
        assert_eq!(report.large_commit_count, 0);
    }

    #[test]
    fn test_default_impl() {
        let acc = DefectPatternsAccumulator::default();
        let report = acc.finalize();
        assert!(report.files.is_empty());
    }

    #[test]
    fn test_no_large_commits() {
        let mut acc = DefectPatternsAccumulator::new();
        // All commits have 1 file → none are "large"
        for i in 0..5 {
            acc.record_commit("Alice", i * 1000, &["a.rs"]);
        }
        let report = acc.finalize();
        assert_eq!(report.large_commit_count, 0);
    }

    #[test]
    fn test_large_commit_detection() {
        let mut acc = DefectPatternsAccumulator::new();
        // 5 normal commits with 1 file each
        for i in 0..5 {
            acc.record_commit("Alice", i * 86400, &["a.rs"]);
        }
        // 1 large commit with 20 files
        let paths: Vec<String> = (0..20).map(|i| format!("f{i}.rs")).collect();
        let path_refs: Vec<&str> = paths.iter().map(String::as_str).collect();
        acc.record_commit("Alice", 6 * 86400, &path_refs);

        let report = acc.finalize();
        assert!(report.large_commit_count >= 1, "should detect large commit");
    }

    #[test]
    fn test_burst_after_large() {
        let mut acc = DefectPatternsAccumulator::new();
        // Build up statistics: 10 normal commits
        for i in 0..10 {
            acc.record_commit("Alice", i * 86400, &["a.rs"]);
        }
        // Large commit touching a.rs and many other files
        let mut paths: Vec<String> = (0..15).map(|i| format!("f{i}.rs")).collect();
        paths.push("a.rs".to_string());
        let path_refs: Vec<&str> = paths.iter().map(String::as_str).collect();
        acc.record_commit("Alice", 15 * 86400, &path_refs);

        // Burst edits to a.rs within 3 days
        acc.record_commit("Alice", 15 * 86400 + 3600, &["a.rs"]);
        acc.record_commit("Alice", 15 * 86400 + 7200, &["a.rs"]);
        acc.record_commit("Alice", 15 * 86400 + 10800, &["a.rs"]);

        let report = acc.finalize();
        // a.rs should have burst-after-large detected
        let a_file = report.files.iter().find(|f| f.path == "a.rs");
        if let Some(a) = a_file {
            assert!(
                a.burst_after_large > 0,
                "should detect burst after large commit"
            );
        }
    }

    #[test]
    fn test_score_bounded() {
        let mut acc = DefectPatternsAccumulator::new();
        for i in 0..10 {
            acc.record_commit("Alice", i * 86400, &["a.rs"]);
        }
        let report = acc.finalize();
        for f in &report.files {
            assert!(
                (0.0..=1.0).contains(&f.score),
                "score={} out of [0,1]",
                f.score
            );
        }
    }

    #[test]
    fn test_sorted_descending() {
        let mut acc = DefectPatternsAccumulator::new();
        // Build stats for Alice
        for i in 0..10 {
            acc.record_commit("Alice", i * 86400, &["a.rs", "b.rs"]);
        }
        let report = acc.finalize();
        for w in report.files.windows(2) {
            assert!(
                w[0].score >= w[1].score - 1e-10,
                "not sorted: {} < {}",
                w[0].score,
                w[1].score
            );
        }
    }

    #[test]
    fn test_insufficient_author_commits() {
        let mut acc = DefectPatternsAccumulator::new();
        // Only 2 commits → below MIN_AUTHOR_COMMITS → no threshold computed
        acc.record_commit("Alice", 0, &["a.rs"]);
        acc.record_commit("Alice", 86400, &["a.rs", "b.rs", "c.rs", "d.rs", "e.rs"]);
        let report = acc.finalize();
        // No large commits detected because threshold not computed
        assert_eq!(report.large_commit_count, 0);
    }

    #[test]
    fn test_high_risk_count() {
        let mut acc = DefectPatternsAccumulator::new();
        // Create enough data to have some results
        for i in 0..20 {
            acc.record_commit("Alice", i * 86400, &["a.rs"]);
        }
        let report = acc.finalize();
        assert!(
            report.high_risk_count <= report.files.len(),
            "high_risk_count exceeds total files"
        );
    }

    // ── Property-based tests ──

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Average score is non-negative.
            #[test]
            fn prop_avg_score_non_negative(n_commits in 3usize..20) {
                let mut acc = DefectPatternsAccumulator::new();
                for i in 0..n_commits {
                    acc.record_commit("Alice", i64::try_from(i).unwrap() * 86400, &["a.rs"]);
                }
                let report = acc.finalize();
                prop_assert!(report.avg_score >= 0.0,
                    "negative avg_score: {}", report.avg_score);
            }

            /// File scores are in [0, 1].
            #[test]
            fn prop_file_scores_bounded(n_commits in 5usize..30) {
                let mut acc = DefectPatternsAccumulator::new();
                for i in 0..n_commits {
                    let n_files = if i % 5 == 0 { 10 } else { 1 };
                    let paths: Vec<String> = (0..n_files).map(|j| format!("f{j}.rs")).collect();
                    let refs: Vec<&str> = paths.iter().map(String::as_str).collect();
                    acc.record_commit("Alice", i64::try_from(i).unwrap() * 86400, &refs);
                }
                let report = acc.finalize();
                for f in &report.files {
                    prop_assert!((0.0..=1.0).contains(&f.score),
                        "score={} out of [0,1]", f.score);
                }
            }
        }
    }
}
