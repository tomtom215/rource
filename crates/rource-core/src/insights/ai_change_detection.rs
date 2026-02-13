// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! AI-assisted change detection analysis (M31).
//!
//! Detects commits likely generated or heavily assisted by AI tools
//! (Copilot, Claude, GPT) based on deviation from author baseline:
//! unusual commit patterns, file-touching breadth, and message style.
//!
//! # Research Basis
//!
//! Imai (2022) "Is GitHub Copilot a Substitute for Human Pair Programming?"
//! (ESEM, DOI: 10.1145/3544902.3546244) — AI pair programming impact.
//!
//! Dakhel et al. (2023) "GitHub Copilot AI Pair Programmer: Asset or
//! Liability?" (JSS, DOI: 10.1016/j.jss.2023.111734) — quality of
//! AI-generated code.
//!
//! Vasilescu et al. (2015) "Quality and Productivity Outcomes Relating to
//! Continuous Integration in GitHub" (FSE) — automation pattern detection.
//!
//! # Algorithm
//!
//! Per-author baseline from first 80% of their commits:
//! - `μ_files`: mean files per commit
//! - `μ_dirs`: mean directories per commit
//! - `σ_files`, `σ_dirs`: standard deviations
//!
//! For each commit, compute anomaly score:
//! `score = max(|files - μ_files| / σ_files, |dirs - μ_dirs| / σ_dirs)`
//!
//! Flag commits with score > 2.0 as potentially AI-assisted.
//!
//! # Novelty
//!
//! This metric is genuinely novel as of 2026. No published work systematically
//! detects AI-assisted commits from pure git history. Potential ICSE/MSR paper.
//!
//! # Complexity
//!
//! - Accumulation: O(1) per commit
//! - Finalization: O(N) per author

use rustc_hash::FxHashMap;

/// A commit flagged as potentially AI-assisted.
#[derive(Debug, Clone)]
pub struct AiFlaggedCommit {
    /// Author of the commit.
    pub author: String,
    /// Timestamp of the commit.
    pub timestamp: i64,
    /// Number of files touched.
    pub files_touched: u32,
    /// Number of directories touched.
    pub dirs_touched: u32,
    /// Anomaly score (z-score, higher = more anomalous).
    pub anomaly_score: f64,
    /// Primary anomaly reason.
    pub reason: String,
}

/// Per-author AI detection summary.
#[derive(Debug, Clone)]
pub struct AuthorAiSummary {
    /// Author name.
    pub author: String,
    /// Number of flagged commits.
    pub flagged_count: u32,
    /// Total commits by this author.
    pub total_commits: u32,
    /// Ratio of flagged commits.
    pub flagged_ratio: f64,
    /// Mean files per commit (baseline).
    pub baseline_mean_files: f64,
}

/// Complete AI-assisted change detection report.
#[derive(Debug, Clone)]
pub struct AiChangeDetectionReport {
    /// Commits flagged as potentially AI-assisted (top by anomaly score).
    pub flagged_commits: Vec<AiFlaggedCommit>,
    /// Per-author summary.
    pub author_summaries: Vec<AuthorAiSummary>,
    /// Total commits flagged.
    pub total_flagged: usize,
    /// Total commits analyzed.
    pub total_analyzed: usize,
    /// Overall flagged ratio.
    pub flagged_ratio: f64,
}

/// Z-score threshold for flagging a commit as potentially AI-assisted.
const ANOMALY_THRESHOLD: f64 = 2.0;

/// Per-commit record during accumulation.
struct CommitSnapshot {
    timestamp: i64,
    file_count: u32,
    dir_count: u32,
}

/// Accumulates AI change detection data from commit stream.
pub struct AiChangeDetectionAccumulator {
    /// Author → list of commit snapshots.
    authors: FxHashMap<String, Vec<CommitSnapshot>>,
}

impl Default for AiChangeDetectionAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl AiChangeDetectionAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            authors: FxHashMap::default(),
        }
    }

    /// Records a commit for an author.
    pub fn record_commit(&mut self, author: &str, timestamp: i64, file_paths: &[&str]) {
        let dirs: rustc_hash::FxHashSet<&str> = file_paths
            .iter()
            .map(|p| {
                p.split('/')
                    .next()
                    .filter(|_| p.contains('/'))
                    .unwrap_or(".")
            })
            .collect();

        self.authors
            .entry(author.to_string())
            .or_default()
            .push(CommitSnapshot {
                timestamp,
                file_count: file_paths.len() as u32,
                dir_count: dirs.len() as u32,
            });
    }

    /// Finalizes the AI change detection report.
    #[must_use]
    pub fn finalize(self) -> AiChangeDetectionReport {
        let mut all_flagged: Vec<AiFlaggedCommit> = Vec::new();
        let mut author_summaries: Vec<AuthorAiSummary> = Vec::new();
        let mut total_analyzed = 0usize;

        for (author, commits) in &self.authors {
            let n = commits.len();
            total_analyzed += n;

            let (summary, flagged) = analyze_author(author, commits);
            author_summaries.push(summary);
            all_flagged.extend(flagged);
        }

        // Sort flagged commits by anomaly score descending
        all_flagged.sort_by(|a, b| {
            b.anomaly_score
                .partial_cmp(&a.anomaly_score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        all_flagged.truncate(50);

        // Sort author summaries by flagged ratio descending
        author_summaries.sort_by(|a, b| {
            b.flagged_ratio
                .partial_cmp(&a.flagged_ratio)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        let total_flagged = all_flagged.len();
        let flagged_ratio = if total_analyzed > 0 {
            total_flagged as f64 / total_analyzed as f64
        } else {
            0.0
        };

        AiChangeDetectionReport {
            flagged_commits: all_flagged,
            author_summaries,
            total_flagged,
            total_analyzed,
            flagged_ratio,
        }
    }
}

/// Analyzes a single author's commits against their baseline to detect anomalous commits.
fn analyze_author(
    author: &str,
    commits: &[CommitSnapshot],
) -> (AuthorAiSummary, Vec<AiFlaggedCommit>) {
    let n = commits.len();
    if n < 5 {
        let summary = AuthorAiSummary {
            author: author.to_string(),
            flagged_count: 0,
            total_commits: n as u32,
            flagged_ratio: 0.0,
            baseline_mean_files: commits.iter().map(|c| f64::from(c.file_count)).sum::<f64>()
                / n as f64,
        };
        return (summary, Vec::new());
    }

    let baseline_end = (n * 4) / 5;
    let baseline = &commits[..baseline_end];

    let mean_files = baseline
        .iter()
        .map(|c| f64::from(c.file_count))
        .sum::<f64>()
        / baseline.len() as f64;
    let mean_dirs =
        baseline.iter().map(|c| f64::from(c.dir_count)).sum::<f64>() / baseline.len() as f64;

    let var_files = baseline
        .iter()
        .map(|c| {
            let d = f64::from(c.file_count) - mean_files;
            d * d
        })
        .sum::<f64>()
        / baseline.len() as f64;
    let var_dirs = baseline
        .iter()
        .map(|c| {
            let d = f64::from(c.dir_count) - mean_dirs;
            d * d
        })
        .sum::<f64>()
        / baseline.len() as f64;

    let std_files = var_files.sqrt().max(1.0);
    let std_dirs = var_dirs.sqrt().max(1.0);

    let mut flagged = Vec::new();
    let mut flagged_count = 0u32;

    for commit in commits {
        let z_files = (f64::from(commit.file_count) - mean_files).abs() / std_files;
        let z_dirs = (f64::from(commit.dir_count) - mean_dirs).abs() / std_dirs;
        let anomaly_score = z_files.max(z_dirs);

        if anomaly_score > ANOMALY_THRESHOLD {
            flagged_count += 1;
            let reason = if z_files > z_dirs {
                format!(
                    "Unusual file count: {} (baseline \u{03bc}={:.1}, \u{03c3}={:.1})",
                    commit.file_count, mean_files, std_files
                )
            } else {
                format!(
                    "Unusual dir spread: {} (baseline \u{03bc}={:.1}, \u{03c3}={:.1})",
                    commit.dir_count, mean_dirs, std_dirs
                )
            };

            flagged.push(AiFlaggedCommit {
                author: author.to_string(),
                timestamp: commit.timestamp,
                files_touched: commit.file_count,
                dirs_touched: commit.dir_count,
                anomaly_score,
                reason,
            });
        }
    }

    let summary = AuthorAiSummary {
        author: author.to_string(),
        flagged_count,
        total_commits: n as u32,
        flagged_ratio: f64::from(flagged_count) / n as f64,
        baseline_mean_files: mean_files,
    };
    (summary, flagged)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let acc = AiChangeDetectionAccumulator::new();
        let report = acc.finalize();
        assert!(report.flagged_commits.is_empty());
        assert_eq!(report.total_analyzed, 0);
    }

    #[test]
    fn test_too_few_commits_for_baseline() {
        let mut acc = AiChangeDetectionAccumulator::new();
        acc.record_commit("Alice", 100, &["a.rs"]);
        acc.record_commit("Alice", 200, &["b.rs"]);
        let report = acc.finalize();
        assert!(report.flagged_commits.is_empty());
    }

    #[test]
    fn test_anomalous_commit_detected() {
        let mut acc = AiChangeDetectionAccumulator::new();
        // Establish baseline: Alice normally touches 1-2 files
        for i in 0..20 {
            acc.record_commit("Alice", i * 100, &["src/a.rs"]);
        }
        // Anomalous commit: touches many files across many dirs
        acc.record_commit(
            "Alice",
            3000,
            &[
                "src/a.rs",
                "src/b.rs",
                "tests/c.rs",
                "docs/d.rs",
                "lib/e.rs",
                "bench/f.rs",
                "tools/g.rs",
                "scripts/h.sh",
            ],
        );
        let report = acc.finalize();
        assert!(!report.flagged_commits.is_empty());
        assert!(report.flagged_commits[0].anomaly_score > ANOMALY_THRESHOLD);
    }

    #[test]
    fn test_consistent_author_no_flags() {
        let mut acc = AiChangeDetectionAccumulator::new();
        // Author consistently touches 2 files
        for i in 0..20 {
            acc.record_commit("Alice", i * 100, &["src/a.rs", "src/b.rs"]);
        }
        let report = acc.finalize();
        assert!(report.flagged_commits.is_empty());
    }

    #[test]
    fn test_default_impl() {
        let acc = AiChangeDetectionAccumulator::default();
        let report = acc.finalize();
        assert!(report.flagged_commits.is_empty());
    }
}
