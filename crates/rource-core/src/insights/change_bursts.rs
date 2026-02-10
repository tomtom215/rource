// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Per-file change burst detection for defect risk prediction.
//!
//! Detects rapid consecutive changes to individual files within short time
//! windows. Files undergoing many rapid changes in succession are significantly
//! more defect-prone, especially when multiple authors are involved.
//!
//! # Research Basis
//!
//! Nagappan, Zeller, Zimmermann, Herzig & Murphy (2010) "Change Bursts as Defect
//! Predictors" (ISSRE 2010, pp. 309–318) validated on Windows Vista (3,404 binaries,
//! 50M+ LOC). Change burst features had the highest predictive power with precision
//! and recall above 90%, outperforming complexity metrics, code churn, and
//! organizational structure measures.
//!
//! # Distinction from Temporal Bursts
//!
//! The existing `temporal.rs` module detects bursts of commit ACTIVITY across the
//! entire project. This module detects bursts of changes to INDIVIDUAL FILES, which
//! is the Nagappan (2010) definition. These are complementary metrics.
//!
//! # Algorithm
//!
//! For each file:
//! 1. Sort all (timestamp, author) pairs by timestamp
//! 2. Identify bursts: consecutive commits separated by < `BURST_GAP_THRESHOLD`
//! 3. Only count sequences of ≥ `MIN_BURST_LENGTH` commits as bursts
//! 4. Compute risk: `burst_count × log₂(1 + max_burst_length) × (1 + multi_author_factor)`
//!
//! # Complexity
//!
//! - Accumulation: O(N) to collect per-file events
//! - Finalization: O(F × K log K) where F = files, K = avg commits per file

use rustc_hash::{FxHashMap, FxHashSet};

/// Maximum gap (in seconds) between consecutive commits to the same file
/// for them to be considered part of the same burst (48 hours).
const BURST_GAP_THRESHOLD: i64 = 48 * 3600;

/// Minimum number of commits in a sequence to constitute a burst.
const MIN_BURST_LENGTH: u32 = 3;

/// Additional risk factor per extra author in a burst beyond the first.
/// Multi-author bursts indicate handoff during rapid changes, increasing risk.
const MULTI_AUTHOR_RISK_FACTOR: f64 = 0.5;

/// A single detected burst for a file.
#[derive(Debug, Clone)]
pub struct FileBurst {
    /// Burst start timestamp.
    pub start: i64,
    /// Burst end timestamp.
    pub end: i64,
    /// Number of commits in this burst.
    pub commit_count: u32,
    /// Distinct authors contributing to this burst.
    pub unique_authors: u32,
    /// Duration in seconds (`end` − `start`).
    pub duration_seconds: i64,
}

/// Burst metrics for a single file.
#[derive(Debug, Clone)]
pub struct FileBurstMetrics {
    /// File path.
    pub path: String,
    /// Total distinct bursts detected.
    pub burst_count: u32,
    /// Longest burst (by commit count).
    pub max_burst_length: u32,
    /// Total commits across all bursts.
    pub total_burst_commits: u32,
    /// Most authors in any single burst.
    pub max_burst_authors: u32,
    /// Composite risk score.
    pub risk_score: f64,
}

/// Complete change burst report.
#[derive(Debug, Clone)]
pub struct ChangeBurstReport {
    /// Per-file burst analysis, sorted by `risk_score` descending.
    pub files: Vec<FileBurstMetrics>,
    /// Total bursts detected across all files.
    pub total_bursts: u32,
    /// Mean commits per burst (across all bursts in all files).
    pub avg_burst_length: f64,
    /// Number of files with at least one burst.
    pub files_with_bursts: u32,
    /// Bursts involving 2+ authors (handoff risk).
    pub multi_author_burst_count: u32,
}

/// Accumulates per-file change events for burst detection.
pub struct ChangeBurstAccumulator {
    /// `file_path` → Vec of `(timestamp, author)`.
    file_events: FxHashMap<String, Vec<(i64, String)>>,
}

impl Default for ChangeBurstAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl ChangeBurstAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            file_events: FxHashMap::default(),
        }
    }

    /// Records a file modification event.
    pub fn record_file(&mut self, path: &str, timestamp: i64, author: &str) {
        self.file_events
            .entry(path.to_string())
            .or_default()
            .push((timestamp, author.to_string()));
    }

    /// Finalizes the accumulator into a [`ChangeBurstReport`].
    #[must_use]
    pub fn finalize(self) -> ChangeBurstReport {
        let mut all_files: Vec<FileBurstMetrics> = Vec::new();
        let mut total_bursts: u32 = 0;
        let mut total_burst_commits: u32 = 0;
        let mut files_with_bursts: u32 = 0;
        let mut multi_author_burst_count: u32 = 0;

        for (path, mut events) in self.file_events {
            events.sort_unstable_by_key(|(ts, _)| *ts);
            let bursts = detect_bursts(&events);

            if bursts.is_empty() {
                continue;
            }

            files_with_bursts += 1;
            let burst_count = bursts.len() as u32;
            total_bursts += burst_count;

            let max_burst_length = bursts.iter().map(|b| b.commit_count).max().unwrap_or(0);
            let file_burst_commits: u32 = bursts.iter().map(|b| b.commit_count).sum();
            total_burst_commits += file_burst_commits;
            let max_burst_authors = bursts.iter().map(|b| b.unique_authors).max().unwrap_or(0);
            multi_author_burst_count +=
                bursts.iter().filter(|b| b.unique_authors >= 2).count() as u32;

            let multi_author_factor = if max_burst_authors > 1 {
                f64::from(max_burst_authors - 1) * MULTI_AUTHOR_RISK_FACTOR
            } else {
                0.0
            };
            let risk_score = f64::from(burst_count)
                * (1.0 + f64::from(max_burst_length)).log2()
                * (1.0 + multi_author_factor);

            all_files.push(FileBurstMetrics {
                path,
                burst_count,
                max_burst_length,
                total_burst_commits: file_burst_commits,
                max_burst_authors,
                risk_score,
            });
        }

        all_files.sort_by(|a, b| {
            b.risk_score
                .partial_cmp(&a.risk_score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        let avg_burst_length = if total_bursts > 0 {
            f64::from(total_burst_commits) / f64::from(total_bursts)
        } else {
            0.0
        };

        ChangeBurstReport {
            files: all_files,
            total_bursts,
            avg_burst_length,
            files_with_bursts,
            multi_author_burst_count,
        }
    }
}

/// Detects bursts in a sorted sequence of (timestamp, author) events.
///
/// A burst is a sequence of ≥ `MIN_BURST_LENGTH` consecutive events where each
/// pair is separated by strictly less than `BURST_GAP_THRESHOLD` seconds.
fn detect_bursts(events: &[(i64, String)]) -> Vec<FileBurst> {
    if events.len() < MIN_BURST_LENGTH as usize {
        return Vec::new();
    }

    let mut bursts = Vec::new();
    let mut burst_start_idx = 0;

    for i in 1..events.len() {
        let gap = events[i].0 - events[i - 1].0;
        if gap >= BURST_GAP_THRESHOLD {
            // Close current burst if long enough
            maybe_emit_burst(events, burst_start_idx, i, &mut bursts);
            burst_start_idx = i;
        }
    }
    // Check final segment
    maybe_emit_burst(events, burst_start_idx, events.len(), &mut bursts);

    bursts
}

/// Emits a burst if the segment \[`start_idx`, `end_idx`) meets `MIN_BURST_LENGTH`.
fn maybe_emit_burst(
    events: &[(i64, String)],
    start_idx: usize,
    end_idx: usize,
    bursts: &mut Vec<FileBurst>,
) {
    let length = (end_idx - start_idx) as u32;
    if length >= MIN_BURST_LENGTH {
        let authors: FxHashSet<&str> = events[start_idx..end_idx]
            .iter()
            .map(|(_, a)| a.as_str())
            .collect();
        bursts.push(FileBurst {
            start: events[start_idx].0,
            end: events[end_idx - 1].0,
            commit_count: length,
            unique_authors: authors.len() as u32,
            duration_seconds: events[end_idx - 1].0 - events[start_idx].0,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = ChangeBurstAccumulator::new();
        let report = acc.finalize();
        assert!(report.files.is_empty());
        assert_eq!(report.total_bursts, 0);
        assert_eq!(report.files_with_bursts, 0);
        assert!((report.avg_burst_length - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_no_bursts_sparse_commits() {
        // Commits 7 days apart → well beyond 48h threshold → 0 bursts
        let mut acc = ChangeBurstAccumulator::new();
        for i in 0..5 {
            acc.record_file("a.rs", i * 7 * 86400, "Alice");
        }
        let report = acc.finalize();
        assert!(report.files.is_empty());
        assert_eq!(report.total_bursts, 0);
    }

    #[test]
    fn test_single_burst_detection() {
        // 5 commits to same file 1 hour apart → 1 burst, length 5
        let mut acc = ChangeBurstAccumulator::new();
        for i in 0..5 {
            acc.record_file("a.rs", i * 3600, "Alice");
        }
        let report = acc.finalize();
        assert_eq!(report.files.len(), 1);
        assert_eq!(report.files[0].burst_count, 1);
        assert_eq!(report.files[0].max_burst_length, 5);
        assert_eq!(report.files[0].total_burst_commits, 5);
        assert_eq!(report.total_bursts, 1);
        assert_eq!(report.files_with_bursts, 1);
    }

    #[test]
    fn test_two_bursts_separated() {
        // 5 rapid commits, 7-day gap, 3 rapid commits → 2 bursts
        let mut acc = ChangeBurstAccumulator::new();
        for i in 0..5 {
            acc.record_file("a.rs", i * 3600, "Alice");
        }
        let gap = 7 * 86400; // 7 days
        for i in 0..3 {
            acc.record_file("a.rs", gap + i * 3600, "Alice");
        }
        let report = acc.finalize();
        assert_eq!(report.files[0].burst_count, 2);
        assert_eq!(report.files[0].max_burst_length, 5);
        assert_eq!(report.files[0].total_burst_commits, 8);
        assert_eq!(report.total_bursts, 2);
    }

    #[test]
    fn test_burst_below_min_length() {
        // 2 rapid commits (below MIN_BURST_LENGTH=3) → 0 bursts
        let mut acc = ChangeBurstAccumulator::new();
        acc.record_file("a.rs", 0, "Alice");
        acc.record_file("a.rs", 3600, "Alice");
        let report = acc.finalize();
        assert!(report.files.is_empty());
        assert_eq!(report.total_bursts, 0);
    }

    #[test]
    fn test_multi_author_burst() {
        // 3 rapid commits by Alice, Bob, Carol → unique_authors=3, risk boosted
        let mut acc = ChangeBurstAccumulator::new();
        acc.record_file("a.rs", 0, "Alice");
        acc.record_file("a.rs", 3600, "Bob");
        acc.record_file("a.rs", 7200, "Carol");
        let report = acc.finalize();
        assert_eq!(report.files[0].max_burst_authors, 3);
        assert_eq!(report.multi_author_burst_count, 1);
        // Risk: 1 * log2(1+3) * (1 + 2*0.5) = 1 * log2(4) * 2 = 1 * 2 * 2 = 4.0
        let expected_risk = 1.0 * (1.0 + 3.0_f64).log2() * (1.0 + 2.0 * MULTI_AUTHOR_RISK_FACTOR);
        assert!(
            (report.files[0].risk_score - expected_risk).abs() < 1e-10,
            "risk={}, expected={}",
            report.files[0].risk_score,
            expected_risk
        );
    }

    #[test]
    fn test_risk_score_exact() {
        // 2 bursts: max_length=5, max_authors=2
        // Risk = 2 * log2(1+5) * (1 + 1*0.5) = 2 * log2(6) * 1.5
        let mut acc = ChangeBurstAccumulator::new();
        // Burst 1: 5 commits, 2 authors
        for i in 0..3 {
            acc.record_file("a.rs", i * 3600, "Alice");
        }
        for i in 3..5 {
            acc.record_file("a.rs", i * 3600, "Bob");
        }
        // Gap
        let gap = 7 * 86400;
        // Burst 2: 3 commits, 1 author
        for i in 0..3 {
            acc.record_file("a.rs", gap + i * 3600, "Alice");
        }
        let report = acc.finalize();
        let f = &report.files[0];
        assert_eq!(f.burst_count, 2);
        assert_eq!(f.max_burst_length, 5);
        assert_eq!(f.max_burst_authors, 2); // from first burst
        let expected = 2.0 * (1.0 + 5.0_f64).log2() * (1.0 + 1.0 * MULTI_AUTHOR_RISK_FACTOR);
        assert!(
            (f.risk_score - expected).abs() < 1e-10,
            "risk={}, expected={}",
            f.risk_score,
            expected
        );
    }

    #[test]
    fn test_multiple_files() {
        // Two files: one with bursts, one without
        let mut acc = ChangeBurstAccumulator::new();
        // File A: 4 rapid commits → 1 burst
        for i in 0..4 {
            acc.record_file("high_risk.rs", i * 3600, "Alice");
        }
        // File B: 2 commits spread apart → 0 bursts
        acc.record_file("low_risk.rs", 0, "Bob");
        acc.record_file("low_risk.rs", 10 * 86400, "Bob");
        let report = acc.finalize();
        assert_eq!(report.files_with_bursts, 1);
        assert_eq!(report.files[0].path, "high_risk.rs");
    }

    #[test]
    fn test_avg_burst_length() {
        // 3 bursts of length 3, 5, 4 → avg = 12/3 = 4.0
        let mut acc = ChangeBurstAccumulator::new();
        let mut ts = 0;
        // Burst 1: 3 commits
        for _ in 0..3 {
            acc.record_file("a.rs", ts, "Alice");
            ts += 3600;
        }
        ts += 7 * 86400; // gap
                         // Burst 2: 5 commits
        for _ in 0..5 {
            acc.record_file("a.rs", ts, "Alice");
            ts += 3600;
        }
        ts += 7 * 86400;
        // Burst 3: 4 commits
        for _ in 0..4 {
            acc.record_file("a.rs", ts, "Alice");
            ts += 3600;
        }
        let report = acc.finalize();
        assert_eq!(report.total_bursts, 3);
        assert!(
            (report.avg_burst_length - 4.0).abs() < 1e-10,
            "avg={}, expected=4.0",
            report.avg_burst_length
        );
    }

    #[test]
    fn test_boundary_at_threshold() {
        // Commits exactly BURST_GAP_THRESHOLD apart → NOT in same burst (exclusive)
        let mut acc = ChangeBurstAccumulator::new();
        acc.record_file("a.rs", 0, "Alice");
        acc.record_file("a.rs", BURST_GAP_THRESHOLD, "Alice");
        acc.record_file("a.rs", 2 * BURST_GAP_THRESHOLD, "Alice");
        let report = acc.finalize();
        // Each commit is separated by exactly the threshold → each is its own segment
        // Segments of length 1 < MIN_BURST_LENGTH → no bursts
        assert!(report.files.is_empty());
        assert_eq!(report.total_bursts, 0);
    }

    #[test]
    fn test_default_impl() {
        let acc = ChangeBurstAccumulator::default();
        let report = acc.finalize();
        assert!(report.files.is_empty());
    }

    #[test]
    fn test_just_below_threshold_in_same_burst() {
        // Commits just below threshold should be in same burst
        let mut acc = ChangeBurstAccumulator::new();
        acc.record_file("a.rs", 0, "Alice");
        acc.record_file("a.rs", BURST_GAP_THRESHOLD - 1, "Alice");
        acc.record_file("a.rs", 2 * (BURST_GAP_THRESHOLD - 1), "Alice");
        let report = acc.finalize();
        assert_eq!(report.files.len(), 1);
        assert_eq!(report.files[0].burst_count, 1);
        assert_eq!(report.files[0].max_burst_length, 3);
    }
}
