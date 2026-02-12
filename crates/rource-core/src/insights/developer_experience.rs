// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Developer Experience Score (`DExp`) — composite developer expertise metric.
//!
//! Combines tenure, total activity, and file-level familiarity into a single
//! score that predicts a developer's likelihood of introducing defects when
//! modifying a given file. Less experienced developers working on unfamiliar
//! files are significantly more likely to introduce bugs.
//!
//! # Research Basis
//!
//! - Mockus & Votta (2000) "Identifying Reasons for Software Changes Using
//!   Historic Databases" (ICSM) — developer experience predicts change quality
//! - Eyolfson et al. (2014) "Correlations Between Bugginess and Time-Varying
//!   Factors" (MSR) — tenure and commit volume correlate with defect rate
//! - Bird et al. (2011) "Don't Touch My Code!" (FSE) — file familiarity
//!   reduces defects
//!
//! # Algorithm
//!
//! ```text
//! DExp(dev, file) = tenure_days × ln(1 + total_commits) × file_familiarity
//!
//! where:
//!   tenure_days     = (last_commit - first_commit) / 86400
//!   total_commits   = number of commits by this developer
//!   file_familiarity = commits_to_this_file / total_commits_to_all_files
//! ```
//!
//! # Complexity
//!
//! - Pre-computation: O(C) where C = total commits (single pass)
//! - Lookup: O(1) per (developer, file) pair via `FxHashMap`
//! - Memory: O(D × `F_avg`) where D = developers, `F_avg` = avg files per developer

use rustc_hash::FxHashMap;

/// Developer experience report for the repository.
#[derive(Debug, Clone)]
pub struct DeveloperExperienceReport {
    /// Per-developer aggregate experience scores.
    pub developers: Vec<DeveloperExperience>,
    /// Per-(developer, file) familiarity scores for the top pairs.
    pub top_file_familiarities: Vec<FileFamiliarity>,
    /// Repository-wide average experience score.
    pub avg_experience_score: f64,
}

/// Aggregate experience metrics for a single developer.
#[derive(Debug, Clone)]
pub struct DeveloperExperience {
    /// Developer name.
    pub author: String,
    /// Overall experience score (higher = more experienced).
    pub experience_score: f64,
    /// Tenure in days (last commit - first commit).
    pub tenure_days: f64,
    /// Total number of commits.
    pub total_commits: u32,
    /// Number of unique files touched.
    pub unique_files: u32,
}

/// File-level familiarity for a specific developer.
#[derive(Debug, Clone)]
pub struct FileFamiliarity {
    /// Developer name.
    pub author: String,
    /// File path.
    pub path: String,
    /// Familiarity fraction: commits to this file / total commits by developer.
    pub familiarity: f64,
    /// Experience score for this (developer, file) pair.
    pub dexp_score: f64,
}

/// Accumulates developer experience data during the single-pass over commits.
pub struct DeveloperExperienceAccumulator {
    /// Per-developer: first commit timestamp.
    first_commit: FxHashMap<String, i64>,
    /// Per-developer: last commit timestamp.
    last_commit: FxHashMap<String, i64>,
    /// Per-developer: total commits.
    total_commits: FxHashMap<String, u32>,
    /// Per-developer: unique files set (file → commit count).
    dev_file_commits: FxHashMap<String, FxHashMap<String, u32>>,
}

impl Default for DeveloperExperienceAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl DeveloperExperienceAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            first_commit: FxHashMap::default(),
            last_commit: FxHashMap::default(),
            total_commits: FxHashMap::default(),
            dev_file_commits: FxHashMap::default(),
        }
    }

    /// Records a commit for experience tracking.
    pub fn record_commit(&mut self, author: &str, timestamp: i64, file_paths: &[&str]) {
        // Update tenure bounds
        self.first_commit
            .entry(author.to_string())
            .and_modify(|t| *t = (*t).min(timestamp))
            .or_insert(timestamp);
        self.last_commit
            .entry(author.to_string())
            .and_modify(|t| *t = (*t).max(timestamp))
            .or_insert(timestamp);

        // Update commit count
        *self.total_commits.entry(author.to_string()).or_insert(0) += 1;

        // Update per-file commit counts
        let file_map = self.dev_file_commits.entry(author.to_string()).or_default();
        for path in file_paths {
            *file_map.entry((*path).to_string()).or_insert(0) += 1;
        }
    }

    /// Finalizes into the experience report.
    #[must_use]
    pub fn finalize(self) -> DeveloperExperienceReport {
        let mut developers = Vec::new();
        let mut all_familiarities = Vec::new();

        for (author, total) in &self.total_commits {
            let first = self.first_commit.get(author).copied().unwrap_or(0);
            let last = self.last_commit.get(author).copied().unwrap_or(0);
            let tenure_days = (last - first) as f64 / 86400.0;
            let total_f = f64::from(*total);

            // Overall experience: tenure × ln(1 + commits)
            let experience_score = tenure_days * total_f.ln_1p();

            let file_map = self.dev_file_commits.get(author);
            let unique_files = file_map.map_or(0, FxHashMap::len) as u32;

            developers.push(DeveloperExperience {
                author: author.clone(),
                experience_score,
                tenure_days,
                total_commits: *total,
                unique_files,
            });

            // Compute per-file familiarity
            if let Some(files) = file_map {
                for (path, &file_commits) in files {
                    let familiarity = f64::from(file_commits) / total_f;
                    let dexp_score = tenure_days * total_f.ln_1p() * familiarity;
                    all_familiarities.push(FileFamiliarity {
                        author: author.clone(),
                        path: path.clone(),
                        familiarity,
                        dexp_score,
                    });
                }
            }
        }

        // Sort developers by experience descending
        developers.sort_by(|a, b| {
            b.experience_score
                .partial_cmp(&a.experience_score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        // Sort familiarities by dexp_score descending, keep top 100
        all_familiarities.sort_by(|a, b| {
            b.dexp_score
                .partial_cmp(&a.dexp_score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        all_familiarities.truncate(100);

        let avg_experience = if developers.is_empty() {
            0.0
        } else {
            developers.iter().map(|d| d.experience_score).sum::<f64>() / developers.len() as f64
        };

        DeveloperExperienceReport {
            developers,
            top_file_familiarities: all_familiarities,
            avg_experience_score: avg_experience,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = DeveloperExperienceAccumulator::new();
        let report = acc.finalize();
        assert!(report.developers.is_empty());
        assert!(report.top_file_familiarities.is_empty());
        assert!((report.avg_experience_score - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_default_impl() {
        let acc = DeveloperExperienceAccumulator::default();
        let report = acc.finalize();
        assert!(report.developers.is_empty());
    }

    #[test]
    fn test_single_developer_single_commit() {
        let mut acc = DeveloperExperienceAccumulator::new();
        acc.record_commit("Alice", 1000, &["src/main.rs"]);
        let report = acc.finalize();

        assert_eq!(report.developers.len(), 1);
        let dev = &report.developers[0];
        assert_eq!(dev.author, "Alice");
        assert_eq!(dev.total_commits, 1);
        assert_eq!(dev.unique_files, 1);
        // tenure = 0 days (single commit), score = 0 * ln(2) = 0
        assert!((dev.tenure_days - 0.0).abs() < f64::EPSILON);
        assert!((dev.experience_score - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_experience_formula_exact() {
        // Alice: 2 commits, 1 day apart (86400 seconds)
        let mut acc = DeveloperExperienceAccumulator::new();
        acc.record_commit("Alice", 0, &["a.rs"]);
        acc.record_commit("Alice", 86400, &["b.rs"]);
        let report = acc.finalize();

        let dev = &report.developers[0];
        assert_eq!(dev.total_commits, 2);
        assert!((dev.tenure_days - 1.0).abs() < f64::EPSILON);
        // experience = 1.0 * ln(1 + 2) = ln(3) ≈ 1.0986
        let expected = 1.0 * 3.0_f64.ln();
        assert!(
            (dev.experience_score - expected).abs() < 1e-10,
            "score={}, expected={}",
            dev.experience_score,
            expected
        );
    }

    #[test]
    fn test_file_familiarity_calculation() {
        // Alice: 3 commits total, 2 to a.rs, 1 to b.rs
        let mut acc = DeveloperExperienceAccumulator::new();
        acc.record_commit("Alice", 0, &["a.rs"]);
        acc.record_commit("Alice", 86400, &["a.rs"]);
        acc.record_commit("Alice", 2 * 86400, &["b.rs"]);
        let report = acc.finalize();

        // Find a.rs familiarity for Alice
        let fam_a = report
            .top_file_familiarities
            .iter()
            .find(|f| f.author == "Alice" && f.path == "a.rs")
            .expect("should have a.rs familiarity");
        // familiarity = 2/3 ≈ 0.6667
        assert!(
            (fam_a.familiarity - 2.0 / 3.0).abs() < 1e-10,
            "familiarity={}, expected={}",
            fam_a.familiarity,
            2.0 / 3.0
        );

        // Find b.rs familiarity for Alice
        let fam_b = report
            .top_file_familiarities
            .iter()
            .find(|f| f.author == "Alice" && f.path == "b.rs")
            .expect("should have b.rs familiarity");
        // familiarity = 1/3 ≈ 0.3333
        assert!(
            (fam_b.familiarity - 1.0 / 3.0).abs() < 1e-10,
            "familiarity={}, expected={}",
            fam_b.familiarity,
            1.0 / 3.0
        );
    }

    #[test]
    fn test_dexp_score_formula() {
        // Alice: 3 commits over 2 days, 2 to a.rs
        // dexp(Alice, a.rs) = 2.0 * ln(1+3) * (2/3)
        let mut acc = DeveloperExperienceAccumulator::new();
        acc.record_commit("Alice", 0, &["a.rs"]);
        acc.record_commit("Alice", 86400, &["a.rs"]);
        acc.record_commit("Alice", 2 * 86400, &["b.rs"]);
        let report = acc.finalize();

        let fam = report
            .top_file_familiarities
            .iter()
            .find(|f| f.author == "Alice" && f.path == "a.rs")
            .unwrap();
        let expected = 2.0 * 4.0_f64.ln() * (2.0 / 3.0);
        assert!(
            (fam.dexp_score - expected).abs() < 1e-10,
            "dexp={}, expected={}",
            fam.dexp_score,
            expected
        );
    }

    #[test]
    fn test_developers_sorted_descending() {
        let mut acc = DeveloperExperienceAccumulator::new();
        // Alice: 10 commits over 10 days
        for i in 0..10 {
            acc.record_commit("Alice", i * 86400, &["a.rs"]);
        }
        // Bob: 2 commits over 1 day
        acc.record_commit("Bob", 0, &["b.rs"]);
        acc.record_commit("Bob", 86400, &["b.rs"]);

        let report = acc.finalize();
        assert!(report.developers.len() >= 2);
        assert!(report.developers[0].experience_score >= report.developers[1].experience_score);
    }

    #[test]
    fn test_multiple_developers() {
        let mut acc = DeveloperExperienceAccumulator::new();
        acc.record_commit("Alice", 0, &["a.rs"]);
        acc.record_commit("Bob", 86400, &["b.rs"]);
        acc.record_commit("Carol", 2 * 86400, &["c.rs"]);
        let report = acc.finalize();
        assert_eq!(report.developers.len(), 3);
    }

    #[test]
    fn test_average_experience() {
        let mut acc = DeveloperExperienceAccumulator::new();
        acc.record_commit("Alice", 0, &["a.rs"]);
        acc.record_commit("Alice", 86400, &["a.rs"]);
        acc.record_commit("Bob", 0, &["b.rs"]);
        acc.record_commit("Bob", 86400, &["b.rs"]);
        let report = acc.finalize();

        // Both have same tenure and commits, so avg = individual score
        assert!(report.avg_experience_score > 0.0);
        // Since they're identical: avg should equal each individual score
        let alice_score = report
            .developers
            .iter()
            .find(|d| d.author == "Alice")
            .unwrap()
            .experience_score;
        assert!(
            (report.avg_experience_score - alice_score).abs() < 1e-10,
            "avg={}, alice={}",
            report.avg_experience_score,
            alice_score
        );
    }

    #[test]
    fn test_tenure_uses_min_max_timestamps() {
        // Kills: using max instead of min for first_commit, or min instead of max for last_commit
        let mut acc = DeveloperExperienceAccumulator::new();
        acc.record_commit("Alice", 86400, &["a.rs"]); // day 1
        acc.record_commit("Alice", 0, &["a.rs"]); // day 0 (earlier!)
        acc.record_commit("Alice", 3 * 86400, &["a.rs"]); // day 3
        let report = acc.finalize();

        let dev = report
            .developers
            .iter()
            .find(|d| d.author == "Alice")
            .unwrap();
        // tenure = (3*86400 - 0) / 86400 = 3 days
        assert!(
            (dev.tenure_days - 3.0).abs() < f64::EPSILON,
            "tenure={}, expected=3.0",
            dev.tenure_days
        );
    }

    // ── Property-based tests ──

    #[allow(clippy::cast_possible_wrap)]
    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Experience score is always non-negative.
            #[test]
            fn prop_experience_non_negative(
                n_commits in 1usize..20,
                day_span in 0i64..365
            ) {
                let mut acc = DeveloperExperienceAccumulator::new();
                for i in 0..n_commits {
                    let ts = (i as i64 * day_span * 86400) / (n_commits as i64).max(1);
                    acc.record_commit("Dev", ts, &["file.rs"]);
                }
                let report = acc.finalize();
                for dev in &report.developers {
                    prop_assert!(dev.experience_score >= 0.0,
                        "negative score: {}", dev.experience_score);
                }
            }

            /// Familiarity is always in [0, 1].
            #[test]
            fn prop_familiarity_bounded(n_commits in 1usize..10) {
                let mut acc = DeveloperExperienceAccumulator::new();
                for i in 0..n_commits {
                    let file = format!("f{}.rs", i % 3);
                    acc.record_commit("Dev", i as i64 * 86400, &[&file]);
                }
                let report = acc.finalize();
                for fam in &report.top_file_familiarities {
                    prop_assert!(fam.familiarity >= 0.0 && fam.familiarity <= 1.0,
                        "familiarity out of range: {}", fam.familiarity);
                }
            }

            /// DExp score is always non-negative.
            #[test]
            fn prop_dexp_non_negative(n_commits in 1usize..10) {
                let mut acc = DeveloperExperienceAccumulator::new();
                for i in 0..n_commits {
                    acc.record_commit("Dev", i as i64 * 86400, &["file.rs"]);
                }
                let report = acc.finalize();
                for fam in &report.top_file_familiarities {
                    prop_assert!(fam.dexp_score >= 0.0,
                        "negative dexp: {}", fam.dexp_score);
                }
            }
        }
    }
}
