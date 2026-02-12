// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Commit Cohesion Index analysis.
//!
//! Measures whether each commit touches a logically related set of files
//! (cohesive) or a tangled mix of unrelated changes.
//!
//! # Research Basis
//!
//! - Herzig & Zeller (MSR 2013, DOI: 10.1109/MSR.2013.6624018) — tangled changes
//! - Kirinuki et al. (ICSME 2014, DOI: 10.1109/ICSME.2014.36) — commit untangling
//! - Agrawal et al. (SIGMOD 1993, DOI: 10.1145/170035.170072) — association rule lift
//!
//! # Novelty
//!
//! Using historical co-change lift as ground truth for commit atomicity assessment
//! is novel. Existing tangled change detection uses heuristics (file distance,
//! directory membership). This approach uses the repository's own co-change evidence
//! as the objective function — self-calibrating and repository-specific.
//!
//! # Algorithm
//!
//! For commit C touching files {f₁, ..., fₙ}:
//!
//!   Cohesion(C) = (2 / (n × (n-1))) × Σ_{i<j} lift(fᵢ, fⱼ)
//!
//! - Single-file commits: Cohesion = 1.0 (trivially atomic)
//! - lift > 1: files change together more than expected (cohesive)
//! - lift = 1: independent
//! - lift < 1: tangled
//!
//! # Complexity
//!
//! - Per-commit: O(k²) where k = files in commit
//! - Total: O(C × k̄²) where C = commits, k̄ = mean files per commit
//! - Lift lookup: O(1) via `HashMap`

use rustc_hash::FxHashMap;

/// Per-commit cohesion data.
#[derive(Debug, Clone)]
pub struct CommitCohesion {
    /// Author of the commit.
    pub author: String,
    /// Timestamp (Unix epoch seconds).
    pub timestamp: i64,
    /// Number of files in the commit.
    pub file_count: u32,
    /// Cohesion score: average pairwise lift.
    /// > 1.0 = cohesive, = 1.0 = neutral, < 1.0 = tangled.
    pub cohesion: f64,
}

/// Aggregate cohesion report.
#[derive(Debug, Clone)]
pub struct CommitCohesionReport {
    /// Per-commit cohesion scores (most tangled first).
    pub commits: Vec<CommitCohesion>,
    /// Median cohesion across all multi-file commits.
    pub median_cohesion: f64,
    /// Fraction of commits with cohesion < 1.0 (tangled).
    pub tangled_ratio: f64,
    /// Per-developer median cohesion.
    pub developer_cohesion: Vec<DeveloperCohesion>,
    /// Total commits analyzed (only multi-file commits).
    pub total_analyzed: u32,
}

/// Per-developer cohesion summary.
#[derive(Debug, Clone)]
pub struct DeveloperCohesion {
    /// Developer name.
    pub author: String,
    /// Median cohesion of their multi-file commits.
    pub median_cohesion: f64,
    /// Number of multi-file commits analyzed.
    pub commit_count: u32,
    /// Fraction of their commits that are tangled (cohesion < 1.0).
    pub tangled_ratio: f64,
}

/// Accumulates per-commit file lists for cohesion analysis.
pub struct CommitCohesionAccumulator {
    /// Per-commit: `(author, timestamp, file_paths)`.
    commits: Vec<(String, i64, Vec<String>)>,
}

impl Default for CommitCohesionAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl CommitCohesionAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            commits: Vec::new(),
        }
    }

    /// Records a commit for later cohesion analysis.
    pub fn record_commit(&mut self, author: &str, timestamp: i64, file_paths: &[&str]) {
        if file_paths.len() >= 2 {
            self.commits.push((
                author.to_string(),
                timestamp,
                file_paths.iter().map(|s| (*s).to_string()).collect(),
            ));
        }
    }

    /// Finalizes the accumulator using pre-computed lift values.
    ///
    /// # Arguments
    ///
    /// * `lift_map` - A map from sorted file pair `(a, b)` to their lift value.
    ///   Pairs not in the map default to lift 1.0 (independent).
    #[must_use]
    pub fn finalize(self, lift_map: &FxHashMap<(String, String), f64>) -> CommitCohesionReport {
        if self.commits.is_empty() {
            return CommitCohesionReport {
                commits: Vec::new(),
                median_cohesion: 1.0,
                tangled_ratio: 0.0,
                developer_cohesion: Vec::new(),
                total_analyzed: 0,
            };
        }

        let mut results: Vec<CommitCohesion> = Vec::with_capacity(self.commits.len());
        let mut dev_scores: FxHashMap<String, Vec<f64>> = FxHashMap::default();

        for (author, timestamp, files) in &self.commits {
            let n = files.len();
            if n < 2 {
                continue;
            }

            // Compute average pairwise lift
            let mut lift_sum = 0.0;
            let mut pair_count = 0u32;

            for i in 0..n {
                for j in (i + 1)..n {
                    let (a, b) = if files[i] < files[j] {
                        (&files[i], &files[j])
                    } else {
                        (&files[j], &files[i])
                    };
                    let lift = lift_map
                        .get(&(a.clone(), b.clone()))
                        .copied()
                        .unwrap_or(1.0);
                    lift_sum += lift;
                    pair_count += 1;
                }
            }

            let cohesion = if pair_count > 0 {
                lift_sum / f64::from(pair_count)
            } else {
                1.0
            };

            dev_scores.entry(author.clone()).or_default().push(cohesion);

            results.push(CommitCohesion {
                author: author.clone(),
                timestamp: *timestamp,
                file_count: n as u32,
                cohesion,
            });
        }

        // Sort: most tangled (lowest cohesion) first
        results.sort_unstable_by(|a, b| {
            a.cohesion
                .partial_cmp(&b.cohesion)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        let total_analyzed = results.len() as u32;
        let tangled_count = results.iter().filter(|c| c.cohesion < 1.0).count();
        let tangled_ratio = if results.is_empty() {
            0.0
        } else {
            tangled_count as f64 / results.len() as f64
        };

        let median_cohesion =
            compute_median(&results.iter().map(|c| c.cohesion).collect::<Vec<_>>());

        // Per-developer aggregation
        let mut developer_cohesion: Vec<DeveloperCohesion> = dev_scores
            .into_iter()
            .map(|(author, mut scores)| {
                scores
                    .sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
                let tangled = scores.iter().filter(|&&s| s < 1.0).count();
                let dev_tangled_ratio = if scores.is_empty() {
                    0.0
                } else {
                    tangled as f64 / scores.len() as f64
                };
                DeveloperCohesion {
                    author,
                    median_cohesion: compute_median(&scores),
                    commit_count: scores.len() as u32,
                    tangled_ratio: dev_tangled_ratio,
                }
            })
            .collect();
        developer_cohesion.sort_unstable_by(|a, b| {
            a.median_cohesion
                .partial_cmp(&b.median_cohesion)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        CommitCohesionReport {
            commits: results,
            median_cohesion,
            tangled_ratio,
            developer_cohesion,
            total_analyzed,
        }
    }
}

/// Computes the median of a sorted slice.
fn compute_median(sorted: &[f64]) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let mid = sorted.len() / 2;
    if sorted.len() % 2 == 0 {
        (sorted[mid - 1] + sorted[mid]) / 2.0
    } else {
        sorted[mid]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_lift_map(entries: &[(&str, &str, f64)]) -> FxHashMap<(String, String), f64> {
        entries
            .iter()
            .map(|(a, b, lift)| ((a.to_string(), b.to_string()), *lift))
            .collect()
    }

    #[test]
    fn test_empty_commits() {
        let acc = CommitCohesionAccumulator::new();
        let report = acc.finalize(&FxHashMap::default());
        assert_eq!(report.total_analyzed, 0);
        assert_eq!(report.median_cohesion, 1.0);
    }

    #[test]
    fn test_single_file_commits_ignored() {
        let mut acc = CommitCohesionAccumulator::new();
        acc.record_commit("Alice", 1000, &["a.rs"]);
        let report = acc.finalize(&FxHashMap::default());
        assert_eq!(report.total_analyzed, 0);
    }

    #[test]
    fn test_two_cochanging_files_high_lift() {
        let mut acc = CommitCohesionAccumulator::new();
        acc.record_commit("Alice", 1000, &["a.rs", "b.rs"]);
        let lift_map = make_lift_map(&[("a.rs", "b.rs", 3.0)]);
        let report = acc.finalize(&lift_map);

        assert_eq!(report.total_analyzed, 1);
        assert!((report.commits[0].cohesion - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_two_unrelated_files_low_lift() {
        let mut acc = CommitCohesionAccumulator::new();
        acc.record_commit("Alice", 1000, &["a.rs", "b.rs"]);
        let lift_map = make_lift_map(&[("a.rs", "b.rs", 0.3)]);
        let report = acc.finalize(&lift_map);

        assert_eq!(report.total_analyzed, 1);
        assert!(report.commits[0].cohesion < 1.0);
        assert!((report.tangled_ratio - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_unknown_pair_defaults_to_one() {
        let mut acc = CommitCohesionAccumulator::new();
        acc.record_commit("Alice", 1000, &["a.rs", "b.rs"]);
        // Empty lift map — all pairs default to 1.0
        let report = acc.finalize(&FxHashMap::default());

        assert_eq!(report.total_analyzed, 1);
        assert!((report.commits[0].cohesion - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_mixed_commit_partial_coupling() {
        let mut acc = CommitCohesionAccumulator::new();
        // Commit touches a.rs, b.rs, c.rs
        // a↔b have high lift, a↔c have low lift, b↔c unknown (defaults to 1.0)
        acc.record_commit("Alice", 1000, &["a.rs", "b.rs", "c.rs"]);
        let lift_map = make_lift_map(&[("a.rs", "b.rs", 5.0), ("a.rs", "c.rs", 0.2)]);
        let report = acc.finalize(&lift_map);

        // Average of 5.0, 0.2, 1.0 = 6.2 / 3 ≈ 2.0667
        let expected = (5.0 + 0.2 + 1.0) / 3.0;
        assert!((report.commits[0].cohesion - expected).abs() < 0.001);
    }

    #[test]
    fn test_per_developer_aggregation() {
        let mut acc = CommitCohesionAccumulator::new();
        acc.record_commit("Alice", 1000, &["a.rs", "b.rs"]);
        acc.record_commit("Alice", 2000, &["a.rs", "c.rs"]);
        acc.record_commit("Bob", 1500, &["a.rs", "b.rs"]);

        let lift_map = make_lift_map(&[("a.rs", "b.rs", 3.0), ("a.rs", "c.rs", 0.5)]);
        let report = acc.finalize(&lift_map);

        assert_eq!(report.developer_cohesion.len(), 2);
        // Alice has commits with cohesion 3.0 and 0.5, median = 1.75
        // Bob has one commit with cohesion 3.0, median = 3.0
        let alice = report
            .developer_cohesion
            .iter()
            .find(|d| d.author == "Alice")
            .unwrap();
        let bob = report
            .developer_cohesion
            .iter()
            .find(|d| d.author == "Bob")
            .unwrap();
        assert_eq!(alice.commit_count, 2);
        assert_eq!(bob.commit_count, 1);
    }

    #[test]
    fn test_tangled_ratio_bounds() {
        let mut acc = CommitCohesionAccumulator::new();
        acc.record_commit("Alice", 1000, &["a.rs", "b.rs"]);
        let report = acc.finalize(&FxHashMap::default());

        assert!(report.tangled_ratio >= 0.0 && report.tangled_ratio <= 1.0);
    }

    #[test]
    fn test_median_computation() {
        assert_eq!(compute_median(&[]), 0.0);
        assert_eq!(compute_median(&[5.0]), 5.0);
        assert_eq!(compute_median(&[1.0, 3.0]), 2.0);
        assert_eq!(compute_median(&[1.0, 2.0, 3.0]), 2.0);
        assert_eq!(compute_median(&[1.0, 2.0, 3.0, 4.0]), 2.5);
    }
}
