// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Knowledge Distribution Entropy per Directory — measures how knowledge is
//! distributed across developers within each directory/module.
//!
//! Low entropy indicates concentrated knowledge (bus factor risk), while high
//! entropy indicates well-distributed knowledge (organizational resilience).
//! This per-directory analysis complements the per-file knowledge analysis
//! in `knowledge.rs` by providing module-level architectural insight.
//!
//! # Research Basis
//!
//! - Rigby & Hassan (2007) "What Can OSS Mailing Lists Tell Us? A
//!   Preliminary Psychometric Text Analysis" (MSR) — knowledge distribution
//! - Constantinou & Mens (2017) "Socio-technical evolution of the Ruby
//!   ecosystem in GitHub" (SANER) — per-module entropy analysis
//! - Fritz et al. (2010) "A Degree-of-Knowledge Model for Predicting
//!   Defects" (TOSEM) — degree-of-knowledge per component
//!
//! # Algorithm
//!
//! Per directory:
//!
//! ```text
//! H(dir) = -Σ(p_i × log2(p_i))
//!
//! where:
//!   p_i = commits_by_developer_i_in_dir / total_commits_in_dir
//!
//! Normalized: H_norm = H / log2(n) where n = number of contributors
//! ```
//!
//! - `H_norm` = 0: single contributor (maximum bus factor risk)
//! - `H_norm` = 1: perfectly equal distribution (maximum resilience)
//!
//! # Complexity
//!
//! - O(C) where C = total commits (single pass to accumulate per-directory data)
//! - O(D × `k_avg`) for entropy computation where D = directories, `k_avg` = avg devs

use rustc_hash::FxHashMap;

/// Knowledge distribution report for the repository.
#[derive(Debug, Clone)]
pub struct KnowledgeDistributionReport {
    /// Per-directory knowledge distribution data.
    pub directories: Vec<DirectoryKnowledgeDistribution>,
    /// Average normalized entropy across all directories.
    pub avg_normalized_entropy: f64,
    /// Number of directories with concentrated knowledge (`H_norm` < 0.3).
    pub concentrated_count: usize,
    /// Number of directories with well-distributed knowledge (`H_norm` > 0.7).
    pub distributed_count: usize,
}

/// Knowledge distribution for a single directory.
#[derive(Debug, Clone)]
pub struct DirectoryKnowledgeDistribution {
    /// Directory path.
    pub directory: String,
    /// Shannon entropy of developer commit distribution.
    pub knowledge_entropy: f64,
    /// Normalized entropy (0.0–1.0).
    pub normalized_entropy: f64,
    /// Number of distinct contributors in this directory.
    pub contributor_count: u32,
    /// Share of the dominant contributor (0.0–1.0).
    pub dominant_contributor_share: f64,
    /// Name of the dominant contributor.
    pub dominant_contributor: String,
    /// Total commits in this directory.
    pub total_commits: u32,
}

/// Accumulates per-directory developer commit data.
pub struct KnowledgeDistributionAccumulator {
    /// directory → (author → commit count).
    dir_authors: FxHashMap<String, FxHashMap<String, u32>>,
}

impl Default for KnowledgeDistributionAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl KnowledgeDistributionAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            dir_authors: FxHashMap::default(),
        }
    }

    /// Records a commit for knowledge distribution tracking.
    ///
    /// Extracts the directory component from each file path and accumulates
    /// per-directory commit counts per developer.
    pub fn record_commit(&mut self, author: &str, file_paths: &[&str]) {
        for path in file_paths {
            let dir = extract_directory(path);
            *self
                .dir_authors
                .entry(dir.to_string())
                .or_default()
                .entry(author.to_string())
                .or_insert(0) += 1;
        }
    }

    /// Finalizes into the knowledge distribution report.
    #[must_use]
    pub fn finalize(self) -> KnowledgeDistributionReport {
        let mut directories = Vec::with_capacity(self.dir_authors.len());

        for (dir, authors) in &self.dir_authors {
            if authors.is_empty() {
                continue;
            }

            let counts: Vec<u32> = authors.values().copied().collect();
            let total: u32 = counts.iter().sum();
            let total_f = f64::from(total);
            let n = counts.len();

            // Compute Shannon entropy
            let entropy = if n <= 1 || total == 0 {
                0.0
            } else {
                counts
                    .iter()
                    .map(|&c| {
                        let p = f64::from(c) / total_f;
                        if p > 0.0 {
                            -p * p.log2()
                        } else {
                            0.0
                        }
                    })
                    .sum::<f64>()
            };

            // Normalize by log2(n)
            let max_entropy = if n > 1 { (n as f64).log2() } else { 1.0 };
            let normalized = if max_entropy > 0.0 {
                (entropy / max_entropy).clamp(0.0, 1.0)
            } else {
                0.0
            };

            // Find dominant contributor
            let (dominant_author, dominant_count) = authors
                .iter()
                .max_by_key(|(_, &count)| count)
                .map_or_else(|| (String::new(), 0), |(a, &c)| (a.clone(), c));
            let dominant_share = if total > 0 {
                f64::from(dominant_count) / total_f
            } else {
                0.0
            };

            directories.push(DirectoryKnowledgeDistribution {
                directory: dir.clone(),
                knowledge_entropy: entropy,
                normalized_entropy: normalized,
                contributor_count: n as u32,
                dominant_contributor_share: dominant_share,
                dominant_contributor: dominant_author,
                total_commits: total,
            });
        }

        // Sort by normalized entropy ascending (most concentrated first — highest risk)
        directories.sort_by(|a, b| {
            a.normalized_entropy
                .partial_cmp(&b.normalized_entropy)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        let avg = if directories.is_empty() {
            0.0
        } else {
            directories
                .iter()
                .map(|d| d.normalized_entropy)
                .sum::<f64>()
                / directories.len() as f64
        };
        let concentrated = directories
            .iter()
            .filter(|d| d.normalized_entropy < 0.3)
            .count();
        let distributed = directories
            .iter()
            .filter(|d| d.normalized_entropy > 0.7)
            .count();

        KnowledgeDistributionReport {
            directories,
            avg_normalized_entropy: avg,
            concentrated_count: concentrated,
            distributed_count: distributed,
        }
    }
}

/// Extracts the top-level directory from a file path.
///
/// Returns "." for files in the root directory.
fn extract_directory(path: &str) -> &str {
    path.rfind('/').map_or(".", |pos| &path[..pos])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = KnowledgeDistributionAccumulator::new();
        let report = acc.finalize();
        assert!(report.directories.is_empty());
        assert!((report.avg_normalized_entropy - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_default_impl() {
        let acc = KnowledgeDistributionAccumulator::default();
        let report = acc.finalize();
        assert!(report.directories.is_empty());
    }

    #[test]
    fn test_extract_directory() {
        assert_eq!(extract_directory("src/main.rs"), "src");
        assert_eq!(extract_directory("src/lib/mod.rs"), "src/lib");
        assert_eq!(extract_directory("main.rs"), ".");
        assert_eq!(extract_directory("a/b/c/d.rs"), "a/b/c");
    }

    #[test]
    fn test_single_contributor_entropy_zero() {
        let mut acc = KnowledgeDistributionAccumulator::new();
        acc.record_commit("Alice", &["src/main.rs", "src/lib.rs"]);
        acc.record_commit("Alice", &["src/utils.rs"]);
        let report = acc.finalize();

        let src = report.directories.iter().find(|d| d.directory == "src");
        assert!(src.is_some());
        let src = src.unwrap();
        assert!(
            (src.knowledge_entropy - 0.0).abs() < f64::EPSILON,
            "single contributor entropy should be 0"
        );
        assert!(
            (src.normalized_entropy - 0.0).abs() < f64::EPSILON,
            "single contributor normalized entropy should be 0"
        );
        assert_eq!(src.contributor_count, 1);
        assert!(
            (src.dominant_contributor_share - 1.0).abs() < f64::EPSILON,
            "single contributor should have 100% share"
        );
    }

    #[test]
    fn test_two_equal_contributors_max_entropy() {
        let mut acc = KnowledgeDistributionAccumulator::new();
        acc.record_commit("Alice", &["src/a.rs"]);
        acc.record_commit("Bob", &["src/b.rs"]);
        let report = acc.finalize();

        let src = report
            .directories
            .iter()
            .find(|d| d.directory == "src")
            .unwrap();
        // H = -2*(0.5*log2(0.5)) = 1.0, max = log2(2) = 1.0
        // normalized = 1.0
        assert!(
            (src.normalized_entropy - 1.0).abs() < 1e-10,
            "equal contributors should have normalized entropy 1.0, got {}",
            src.normalized_entropy
        );
    }

    #[test]
    fn test_entropy_formula_exact() {
        // 3 contributors with [1, 2, 3] commits → total = 6
        // p = [1/6, 2/6, 3/6]
        // H = -(1/6 * log2(1/6) + 2/6 * log2(2/6) + 3/6 * log2(3/6))
        let mut acc = KnowledgeDistributionAccumulator::new();
        acc.record_commit("Alice", &["src/a.rs"]);
        for _ in 0..2 {
            acc.record_commit("Bob", &["src/a.rs"]);
        }
        for _ in 0..3 {
            acc.record_commit("Carol", &["src/a.rs"]);
        }
        let report = acc.finalize();

        let src = report
            .directories
            .iter()
            .find(|d| d.directory == "src")
            .unwrap();
        let p1: f64 = 1.0 / 6.0;
        let p2: f64 = 2.0 / 6.0;
        let p3: f64 = 3.0 / 6.0;
        let expected_h = -(p1 * p1.log2() + p2 * p2.log2() + p3 * p3.log2());
        assert!(
            (src.knowledge_entropy - expected_h).abs() < 1e-10,
            "entropy={}, expected={}",
            src.knowledge_entropy,
            expected_h
        );
    }

    #[test]
    fn test_multiple_directories() {
        let mut acc = KnowledgeDistributionAccumulator::new();
        acc.record_commit("Alice", &["src/a.rs"]);
        acc.record_commit("Bob", &["tests/t.rs"]);
        let report = acc.finalize();
        assert!(report.directories.len() >= 2);
    }

    #[test]
    fn test_root_directory_files() {
        let mut acc = KnowledgeDistributionAccumulator::new();
        acc.record_commit("Alice", &["README.md"]);
        let report = acc.finalize();
        assert!(report.directories.iter().any(|d| d.directory == "."));
    }

    #[test]
    fn test_sorted_ascending_by_entropy() {
        let mut acc = KnowledgeDistributionAccumulator::new();
        // src: single contributor → entropy 0
        for _ in 0..5 {
            acc.record_commit("Alice", &["src/a.rs"]);
        }
        // tests: two equal contributors → entropy 1.0
        acc.record_commit("Alice", &["tests/t.rs"]);
        acc.record_commit("Bob", &["tests/t.rs"]);
        let report = acc.finalize();

        // Sorted ascending: most concentrated (lowest entropy) first
        if report.directories.len() >= 2 {
            assert!(
                report.directories[0].normalized_entropy
                    <= report.directories[1].normalized_entropy,
                "not sorted ascending"
            );
        }
    }

    #[test]
    fn test_concentrated_distributed_counts() {
        let mut acc = KnowledgeDistributionAccumulator::new();
        // Concentrated directory (1 contributor)
        for _ in 0..5 {
            acc.record_commit("Alice", &["concentrated/a.rs"]);
        }
        // Distributed directory (2 equal contributors)
        acc.record_commit("Alice", &["distributed/a.rs"]);
        acc.record_commit("Bob", &["distributed/b.rs"]);
        let report = acc.finalize();

        // concentrated should have normalized_entropy = 0 (< 0.3)
        assert!(
            report.concentrated_count >= 1,
            "concentrated_count={}",
            report.concentrated_count
        );
    }

    #[test]
    fn test_dominant_contributor() {
        let mut acc = KnowledgeDistributionAccumulator::new();
        acc.record_commit("Alice", &["src/a.rs"]);
        acc.record_commit("Alice", &["src/a.rs"]);
        acc.record_commit("Bob", &["src/a.rs"]);
        let report = acc.finalize();

        let src = report
            .directories
            .iter()
            .find(|d| d.directory == "src")
            .unwrap();
        assert_eq!(src.dominant_contributor, "Alice");
        // Alice: 2/3 ≈ 0.667
        assert!(
            (src.dominant_contributor_share - 2.0 / 3.0).abs() < 1e-10,
            "dominant share={}, expected={}",
            src.dominant_contributor_share,
            2.0 / 3.0
        );
    }

    // ── Property-based tests ──

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Normalized entropy is always in [0, 1].
            #[test]
            fn prop_normalized_entropy_bounded(n_devs in 1usize..10) {
                let mut acc = KnowledgeDistributionAccumulator::new();
                for i in 0..n_devs {
                    let author = format!("dev{i}");
                    acc.record_commit(&author, &["src/file.rs"]);
                }
                let report = acc.finalize();
                for d in &report.directories {
                    prop_assert!(
                        d.normalized_entropy >= 0.0 && d.normalized_entropy <= 1.0,
                        "normalized_entropy={} out of [0,1]",
                        d.normalized_entropy
                    );
                }
            }

            /// Dominant contributor share is always in [0, 1].
            #[test]
            fn prop_dominant_share_bounded(n_devs in 1usize..10, n_commits in 1usize..20) {
                let mut acc = KnowledgeDistributionAccumulator::new();
                for i in 0..n_commits {
                    let dev_idx = i % n_devs;
                    let author = format!("dev{dev_idx}");
                    acc.record_commit(&author, &["src/file.rs"]);
                }
                let report = acc.finalize();
                for d in &report.directories {
                    prop_assert!(
                        d.dominant_contributor_share >= 0.0 && d.dominant_contributor_share <= 1.0,
                        "dominant_share={} out of [0,1]",
                        d.dominant_contributor_share
                    );
                }
            }
        }
    }
}
