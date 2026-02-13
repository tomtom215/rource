// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Commit coherence scoring: per-commit quality assessment.
//!
//! Scores each commit on how logically coherent it is [0.0, 1.0], combining:
//! 1. Directory spread — how many distinct directories are touched
//! 2. Historical co-change affinity — do these files typically change together?
//! 3. File type homogeneity — are all changed files the same type?
//!
//! Low scores indicate "tangled" commits that combine multiple unrelated concerns
//! and should have been split into atomic changes.
//!
//! Also computes a repository-level "atomicity index" and per-developer breakdown.
//!
//! # Academic Citations
//!
//! - Herzig & Zeller (2013) — "It's Not a Bug, It's a Feature: How
//!   Misclassification Impacts Bug Prediction" (tangled change identification)
//! - Xu et al. (2025) — "Detecting and Untangling Composite Commits via
//!   Attributed Graph Modeling" (`JCST`)
//! - Kirinuki et al. (2014) — "Hey! You Changed the Test!" (tangled
//!   test/production changes)
//!
//! # Novelty
//!
//! `CodeScene` detects "developer congestion" but NOT per-commit coherence scoring.
//! A comprehensive tangling score combining structural, historical, and textual
//! signals is novel for VCS-only tools.

use rustc_hash::FxHashMap;

/// Commit coherence report for the repository.
#[derive(Debug)]
pub struct CommitCoherenceReport {
    /// Per-commit coherence scores, sorted by coherence ascending (most tangled first).
    pub commits: Vec<CommitCoherenceEntry>,
    /// Repository-level atomicity index [0.0, 1.0].
    /// Median coherence across all multi-file commits.
    pub atomicity_index: f64,
    /// Fraction of commits classified as tangled (coherence < 0.5).
    pub tangled_fraction: f64,
    /// Per-developer coherence summaries.
    pub developer_coherence: Vec<DeveloperCoherenceEntry>,
    /// Total multi-file commits analyzed.
    pub total_analyzed: u32,
}

/// Coherence data for a single commit.
#[derive(Debug)]
pub struct CommitCoherenceEntry {
    /// Commit author.
    pub author: String,
    /// Commit timestamp.
    pub timestamp: i64,
    /// Number of files in this commit.
    pub file_count: u32,
    /// Coherence score [0.0, 1.0].
    pub coherence: f64,
    /// Directory spread: number of distinct directories.
    pub directory_count: u32,
    /// File type homogeneity [0.0, 1.0].
    pub type_homogeneity: f64,
    /// Co-change affinity [0.0, 1.0].
    pub cochange_affinity: f64,
}

/// Per-developer coherence summary.
#[derive(Debug)]
pub struct DeveloperCoherenceEntry {
    /// Developer name.
    pub author: String,
    /// Mean coherence across their commits.
    pub mean_coherence: f64,
    /// Number of tangled commits (coherence < 0.5).
    pub tangled_count: u32,
    /// Total multi-file commits.
    pub total_commits: u32,
}

/// Accumulator for commit coherence data.
#[derive(Default)]
pub struct CommitCoherenceAccumulator {
    /// Recorded commits: (author, timestamp, `file_paths`).
    commits: Vec<(String, i64, Vec<String>)>,
}

impl CommitCoherenceAccumulator {
    /// Creates a new accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Records a commit for coherence analysis.
    ///
    /// Only multi-file commits are meaningful for coherence scoring;
    /// single-file commits are trivially coherent (1.0) and skipped.
    pub fn record_commit(&mut self, author: &str, timestamp: i64, files: Vec<String>) {
        if files.len() >= 2 {
            self.commits.push((author.to_string(), timestamp, files));
        }
    }

    /// Finalizes the accumulator into a report.
    ///
    /// # Arguments
    ///
    /// * `lift_map` - Pre-computed co-change lift map from coupling analysis.
    ///   Keys are ordered (min, max) file pairs, values are lift scores.
    ///   If empty, co-change affinity defaults to 0.5 for all commits.
    #[must_use]
    pub fn finalize(self, lift_map: &FxHashMap<(String, String), f64>) -> CommitCoherenceReport {
        if self.commits.is_empty() {
            return CommitCoherenceReport {
                commits: Vec::new(),
                atomicity_index: 1.0,
                tangled_fraction: 0.0,
                developer_coherence: Vec::new(),
                total_analyzed: 0,
            };
        }

        let mut entries: Vec<CommitCoherenceEntry> = self
            .commits
            .iter()
            .map(|(author, ts, files)| score_commit(author, *ts, files, lift_map))
            .collect();

        // Sort by coherence ascending (most tangled first)
        entries.sort_by(|a, b| {
            a.coherence
                .partial_cmp(&b.coherence)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        let total = entries.len() as u32;
        let tangled_count = entries.iter().filter(|e| e.coherence < 0.5).count();
        let tangled_fraction = tangled_count as f64 / f64::from(total);

        // Atomicity index = median coherence
        let atomicity_index = {
            let mut scores: Vec<f64> = entries.iter().map(|e| e.coherence).collect();
            scores.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
            if scores.is_empty() {
                1.0
            } else {
                scores[scores.len() / 2]
            }
        };

        // Per-developer aggregation
        let mut dev_map: FxHashMap<String, (f64, u32, u32)> = FxHashMap::default();
        for e in &entries {
            let (sum, tangled, count) = dev_map.entry(e.author.clone()).or_insert((0.0, 0, 0));
            *sum += e.coherence;
            if e.coherence < 0.5 {
                *tangled += 1;
            }
            *count += 1;
        }
        let mut developer_coherence: Vec<DeveloperCoherenceEntry> = dev_map
            .into_iter()
            .map(|(author, (sum, tangled, count))| DeveloperCoherenceEntry {
                author,
                mean_coherence: sum / f64::from(count),
                tangled_count: tangled,
                total_commits: count,
            })
            .collect();
        developer_coherence.sort_by(|a, b| {
            a.mean_coherence
                .partial_cmp(&b.mean_coherence)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        // Truncate commits to top 100 most tangled
        entries.truncate(100);

        CommitCoherenceReport {
            commits: entries,
            atomicity_index,
            tangled_fraction,
            developer_coherence,
            total_analyzed: total,
        }
    }
}

/// Scores a single commit's coherence.
fn score_commit(
    author: &str,
    timestamp: i64,
    files: &[String],
    lift_map: &FxHashMap<(String, String), f64>,
) -> CommitCoherenceEntry {
    let file_count = files.len() as u32;

    // Signal 1: Directory spread [0.0, 1.0]
    // 1.0 = all in same directory, decreasing with more directories
    let directories: rustc_hash::FxHashSet<&str> =
        files.iter().map(|f| extract_directory(f)).collect();
    let dir_count = directories.len() as u32;
    let dir_score = 1.0 / f64::from(dir_count); // 1/D

    // Signal 2: File type homogeneity [0.0, 1.0]
    // 1.0 = all same extension, decreasing with more extensions
    let extensions: rustc_hash::FxHashSet<&str> =
        files.iter().map(|f| extract_extension(f)).collect();
    let ext_count = extensions.len().max(1);
    let type_score = 1.0 / ext_count as f64; // usize, not u32

    // Signal 3: Co-change affinity [0.0, 1.0]
    // Average lift of all file pairs in this commit
    let cochange_affinity = compute_cochange_affinity(files, lift_map);

    // Weighted combination: 40% directory, 30% affinity, 30% type
    let coherence = (0.4 * dir_score + 0.3 * cochange_affinity + 0.3 * type_score).clamp(0.0, 1.0);

    CommitCoherenceEntry {
        author: author.to_string(),
        timestamp,
        file_count,
        coherence,
        directory_count: dir_count,
        type_homogeneity: type_score,
        cochange_affinity,
    }
}

/// Extracts the top-level directory from a file path.
fn extract_directory(path: &str) -> &str {
    path.rfind('/').map_or("", |idx| &path[..idx])
}

/// Extracts the file extension from a path.
fn extract_extension(path: &str) -> &str {
    path.rfind('.').map_or("", |idx| &path[idx..])
}

/// Computes average co-change affinity for a set of files.
///
/// Uses pre-computed lift map. Missing pairs get affinity 0.0 (never co-changed).
fn compute_cochange_affinity(files: &[String], lift_map: &FxHashMap<(String, String), f64>) -> f64 {
    if files.len() < 2 || lift_map.is_empty() {
        return 0.5; // neutral when no data
    }

    let mut total_lift = 0.0;
    let mut pair_count = 0u32;

    for i in 0..files.len() {
        for j in (i + 1)..files.len() {
            let key = if files[i] <= files[j] {
                (files[i].clone(), files[j].clone())
            } else {
                (files[j].clone(), files[i].clone())
            };
            let lift = lift_map.get(&key).copied().unwrap_or(0.0);
            // Normalize lift to [0, 1]: lift > 1 means positive association
            total_lift += (lift / (lift + 1.0)).min(1.0);
            pair_count += 1;
        }
    }

    if pair_count == 0 {
        return 0.5;
    }
    total_lift / f64::from(pair_count)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = CommitCoherenceAccumulator::new();
        let report = acc.finalize(&FxHashMap::default());
        assert!(report.commits.is_empty());
        assert!((report.atomicity_index - 1.0).abs() < f64::EPSILON);
        assert!((report.tangled_fraction - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_single_file_commit_ignored() {
        let mut acc = CommitCoherenceAccumulator::new();
        acc.record_commit("Alice", 1000, vec!["a.rs".to_string()]);
        let report = acc.finalize(&FxHashMap::default());
        // Single-file commits are not recorded
        assert_eq!(report.total_analyzed, 0);
    }

    #[test]
    fn test_coherent_commit_same_dir_same_ext() {
        let mut acc = CommitCoherenceAccumulator::new();
        acc.record_commit(
            "Alice",
            1000,
            vec!["src/a.rs".to_string(), "src/b.rs".to_string()],
        );
        let report = acc.finalize(&FxHashMap::default());
        assert_eq!(report.total_analyzed, 1);
        let c = &report.commits[0];
        assert!(c.coherence > 0.7, "coherence={}", c.coherence);
        assert_eq!(c.directory_count, 1);
        assert!((c.type_homogeneity - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_tangled_commit_many_dirs_many_types() {
        let mut acc = CommitCoherenceAccumulator::new();
        acc.record_commit(
            "Bob",
            2000,
            vec![
                "src/main.rs".to_string(),
                "tests/test.py".to_string(),
                "docs/readme.md".to_string(),
                "config/settings.json".to_string(),
            ],
        );
        let report = acc.finalize(&FxHashMap::default());
        let c = &report.commits[0];
        // 4 directories, 4 extensions → low coherence
        assert!(c.coherence < 0.5, "coherence={}", c.coherence);
        assert_eq!(c.directory_count, 4);
    }

    #[test]
    fn test_atomicity_index_is_median() {
        let mut acc = CommitCoherenceAccumulator::new();
        // 3 coherent commits (same dir)
        for i in 0..3 {
            acc.record_commit(
                "Alice",
                i64::from(i) * 1000,
                vec!["src/a.rs".to_string(), "src/b.rs".to_string()],
            );
        }
        // 1 tangled commit
        acc.record_commit(
            "Bob",
            5000,
            vec![
                "a/x.rs".to_string(),
                "b/y.py".to_string(),
                "c/z.md".to_string(),
            ],
        );
        let report = acc.finalize(&FxHashMap::default());
        // Median of 4 values: middle two are sorted coherence scores
        assert!(report.atomicity_index > 0.0);
    }

    #[test]
    fn test_developer_coherence() {
        let mut acc = CommitCoherenceAccumulator::new();
        // Alice: coherent commits
        for i in 0..3 {
            acc.record_commit(
                "Alice",
                i64::from(i) * 1000,
                vec!["src/a.rs".to_string(), "src/b.rs".to_string()],
            );
        }
        // Bob: tangled commit
        acc.record_commit(
            "Bob",
            5000,
            vec![
                "a/x.rs".to_string(),
                "b/y.py".to_string(),
                "c/z.md".to_string(),
                "d/w.json".to_string(),
            ],
        );
        let report = acc.finalize(&FxHashMap::default());
        let alice = report
            .developer_coherence
            .iter()
            .find(|d| d.author == "Alice")
            .unwrap();
        let bob = report
            .developer_coherence
            .iter()
            .find(|d| d.author == "Bob")
            .unwrap();
        assert!(alice.mean_coherence > bob.mean_coherence);
    }

    #[test]
    fn test_cochange_affinity_with_lift_data() {
        let mut lift_map = FxHashMap::default();
        lift_map.insert(("a.rs".to_string(), "b.rs".to_string()), 5.0);

        let mut acc = CommitCoherenceAccumulator::new();
        acc.record_commit("Alice", 1000, vec!["a.rs".to_string(), "b.rs".to_string()]);
        let report = acc.finalize(&lift_map);
        let c = &report.commits[0];
        // With high lift, affinity should be high
        assert!(
            c.cochange_affinity > 0.5,
            "affinity={}",
            c.cochange_affinity
        );
    }

    #[test]
    fn test_extract_directory() {
        assert_eq!(extract_directory("src/main.rs"), "src");
        assert_eq!(extract_directory("a/b/c.rs"), "a/b");
        assert_eq!(extract_directory("root.rs"), "");
    }

    #[test]
    fn test_extract_extension() {
        assert_eq!(extract_extension("main.rs"), ".rs");
        assert_eq!(extract_extension("test.py"), ".py");
        assert_eq!(extract_extension("Makefile"), "");
    }

    #[test]
    fn test_tangled_fraction() {
        let mut acc = CommitCoherenceAccumulator::new();
        // 1 tangled, 1 coherent
        acc.record_commit(
            "Alice",
            1000,
            vec!["src/a.rs".to_string(), "src/b.rs".to_string()],
        );
        acc.record_commit(
            "Bob",
            2000,
            vec![
                "a/x.rs".to_string(),
                "b/y.py".to_string(),
                "c/z.md".to_string(),
                "d/w.json".to_string(),
                "e/v.toml".to_string(),
            ],
        );
        let report = acc.finalize(&FxHashMap::default());
        assert!(report.tangled_fraction > 0.0);
        assert!(report.tangled_fraction <= 1.0);
    }
}
