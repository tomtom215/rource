// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Sliding-window change entropy for defect risk prediction.
//!
//! Measures the Shannon entropy of file modification distribution within
//! sliding time windows. High entropy (scattered changes across many files)
//! correlates with higher defect risk; low entropy (focused changes) with lower risk.
//!
//! # Research Basis
//!
//! Hassan, A.E. (2009) "Predicting Faults Using the Complexity of Code Changes"
//! (ICSE 2009, pp. 78–88) validated change entropy on 6 large open-source projects.
//! Change entropy outperforms many product metrics for defect prediction.
//!
//! Ethari et al. (2025) "Co-Change Graph Entropy: A New Process Metric for Defect
//! Prediction" (EASE 2025, arXiv:2504.18511) extended this with co-change graph
//! entropy, achieving statistically significant AUROC improvements in 82.5% of cases.
//!
//! # Distinction from Per-Commit Entropy
//!
//! The existing `compute_commit_entropy()` in `mod.rs` computes `log2(N)` per commit
//! (how many files a single commit touches). This module measures the DISTRIBUTION
//! of modifications across files within TIME WINDOWS. Hassan's (2009) file-level
//! change entropy is the one validated for defect prediction. The two metrics are
//! complementary, not duplicative.
//!
//! # Algorithm
//!
//! For each 30-day window:
//! 1. Count modifications per file: `freq(f)`
//! 2. Compute probability: `p(f) = freq(f) / total_modifications`
//! 3. Raw entropy: `H(W) = -Σ p(f) × log₂(p(f))`
//! 4. Normalized: `H_norm(W) = H(W) / log₂(files_modified)` ∈ \[0, 1\]
//!
//! # Complexity
//!
//! - Accumulation: O(N) where N = total file modifications
//! - Finalization: O(W × Fᵥ) where W = windows, Fᵥ = avg files per window

use rustc_hash::FxHashMap;

use super::FileActionKind;

/// Default sliding window duration: 30 days in seconds.
const DEFAULT_WINDOW_SECONDS: i64 = 30 * 86400;

/// Entropy trend direction over the project lifetime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EntropyTrend {
    /// Entropy increasing over time (changes becoming more scattered).
    Increasing,
    /// Entropy roughly stable over time.
    Stable,
    /// Entropy decreasing over time (changes becoming more focused).
    Decreasing,
}

/// Entropy measurements for a single time window.
#[derive(Debug, Clone)]
pub struct ChangeEntropyWindow {
    /// Start timestamp of this window.
    pub window_start: i64,
    /// End timestamp of this window.
    pub window_end: i64,
    /// Raw Shannon entropy H(W) in bits.
    pub raw_entropy: f64,
    /// Normalized entropy `H_norm`(W) in \[0, 1\].
    pub normalized_entropy: f64,
    /// Distinct files modified in this window.
    pub files_modified: u32,
    /// Total modification events in this window.
    pub total_modifications: u32,
}

/// Complete change entropy report.
#[derive(Debug, Clone)]
pub struct ChangeEntropyReport {
    /// Time series of entropy per window.
    pub windows: Vec<ChangeEntropyWindow>,
    /// Mean normalized entropy across all windows.
    pub avg_normalized_entropy: f64,
    /// Index of the peak-scatter window (highest normalized entropy).
    pub max_entropy_window_idx: Option<usize>,
    /// Trend direction over the project lifetime.
    pub trend: EntropyTrend,
}

/// Accumulates file modification events for change entropy computation.
pub struct ChangeEntropyAccumulator {
    /// (timestamp, `file_path`) pairs for Modify and Create actions.
    events: Vec<(i64, String)>,
}

impl Default for ChangeEntropyAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl ChangeEntropyAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self { events: Vec::new() }
    }

    /// Records a file action. Only `Modify` and `Create` actions contribute to
    /// change entropy (deletions remove files from the codebase).
    pub fn record_file(&mut self, path: &str, action: FileActionKind, timestamp: i64) {
        if matches!(action, FileActionKind::Modify | FileActionKind::Create) {
            self.events.push((timestamp, path.to_string()));
        }
    }

    /// Finalizes the accumulator into a [`ChangeEntropyReport`].
    #[must_use]
    pub fn finalize(self, t_min: i64, t_max: i64) -> ChangeEntropyReport {
        if self.events.is_empty() || t_min >= t_max {
            return ChangeEntropyReport {
                windows: Vec::new(),
                avg_normalized_entropy: 0.0,
                max_entropy_window_idx: None,
                trend: EntropyTrend::Stable,
            };
        }

        let mut windows = Vec::new();
        let mut window_start = t_min;

        while window_start < t_max {
            let window_end = (window_start + DEFAULT_WINDOW_SECONDS).min(t_max);
            let mut file_counts: FxHashMap<&str, u32> = FxHashMap::default();

            for (ts, path) in &self.events {
                if *ts >= window_start && *ts < window_end {
                    *file_counts.entry(path.as_str()).or_insert(0) += 1;
                }
            }

            let files_modified = file_counts.len() as u32;
            let total_modifications: u32 = file_counts.values().sum();

            if total_modifications > 0 {
                let total_f = f64::from(total_modifications);
                let raw_entropy: f64 = file_counts
                    .values()
                    .map(|&count| {
                        let p = f64::from(count) / total_f;
                        if p > 0.0 {
                            -p * p.log2()
                        } else {
                            0.0
                        }
                    })
                    .sum();

                let normalized_entropy = if files_modified > 1 {
                    raw_entropy / (f64::from(files_modified)).log2()
                } else {
                    0.0
                };

                windows.push(ChangeEntropyWindow {
                    window_start,
                    window_end,
                    raw_entropy,
                    normalized_entropy,
                    files_modified,
                    total_modifications,
                });
            }

            window_start += DEFAULT_WINDOW_SECONDS;
        }

        let avg_normalized_entropy = if windows.is_empty() {
            0.0
        } else {
            windows.iter().map(|w| w.normalized_entropy).sum::<f64>() / windows.len() as f64
        };

        let max_entropy_window_idx = windows
            .iter()
            .enumerate()
            .max_by(|(_, a), (_, b)| {
                a.normalized_entropy
                    .partial_cmp(&b.normalized_entropy)
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
            .map(|(i, _)| i);

        let trend = compute_trend(&windows);

        ChangeEntropyReport {
            windows,
            avg_normalized_entropy,
            max_entropy_window_idx,
            trend,
        }
    }
}

/// Determines entropy trend by comparing first-half and second-half averages.
fn compute_trend(windows: &[ChangeEntropyWindow]) -> EntropyTrend {
    if windows.len() < 2 {
        return EntropyTrend::Stable;
    }

    let mid = windows.len() / 2;
    let first_half_avg: f64 = windows[..mid]
        .iter()
        .map(|w| w.normalized_entropy)
        .sum::<f64>()
        / mid as f64;
    let second_half_avg: f64 = windows[mid..]
        .iter()
        .map(|w| w.normalized_entropy)
        .sum::<f64>()
        / (windows.len() - mid) as f64;

    let diff = second_half_avg - first_half_avg;
    if diff > 0.05 {
        EntropyTrend::Increasing
    } else if diff < -0.05 {
        EntropyTrend::Decreasing
    } else {
        EntropyTrend::Stable
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = ChangeEntropyAccumulator::new();
        let report = acc.finalize(0, 0);
        assert!(report.windows.is_empty());
        assert!((report.avg_normalized_entropy - 0.0).abs() < f64::EPSILON);
        assert!(report.max_entropy_window_idx.is_none());
        assert_eq!(report.trend, EntropyTrend::Stable);
    }

    #[test]
    fn test_single_file_entropy_zero() {
        // All modifications to one file → H_norm = 0.0
        let mut acc = ChangeEntropyAccumulator::new();
        for i in 0..10 {
            acc.record_file("a.rs", FileActionKind::Modify, i * 86400);
        }
        let report = acc.finalize(0, DEFAULT_WINDOW_SECONDS);
        assert_eq!(report.windows.len(), 1);
        assert!(
            report.windows[0].normalized_entropy.abs() < f64::EPSILON,
            "H_norm={}, expected=0.0",
            report.windows[0].normalized_entropy
        );
        assert_eq!(report.windows[0].files_modified, 1);
    }

    #[test]
    fn test_two_files_equal_entropy_one() {
        // Equal modifications to 2 files → H_norm = 1.0
        let mut acc = ChangeEntropyAccumulator::new();
        for i in 0..5 {
            acc.record_file("a.rs", FileActionKind::Modify, i * 86400);
            acc.record_file("b.rs", FileActionKind::Modify, i * 86400 + 100);
        }
        let report = acc.finalize(0, DEFAULT_WINDOW_SECONDS);
        assert_eq!(report.windows.len(), 1);
        // H = -(0.5*log2(0.5) + 0.5*log2(0.5)) = 1.0
        // H_norm = 1.0 / log2(2) = 1.0
        assert!(
            (report.windows[0].normalized_entropy - 1.0).abs() < 1e-10,
            "H_norm={}, expected=1.0",
            report.windows[0].normalized_entropy
        );
    }

    #[test]
    fn test_three_files_unequal() {
        // 3 files: a=4, b=2, c=2 → total=8
        // p(a)=0.5, p(b)=0.25, p(c)=0.25
        // H = -(0.5*log2(0.5) + 0.25*log2(0.25) + 0.25*log2(0.25))
        //   = -(0.5*(-1) + 0.25*(-2) + 0.25*(-2))
        //   = 0.5 + 0.5 + 0.5 = 1.5
        // H_norm = 1.5 / log2(3) ≈ 1.5 / 1.585 ≈ 0.9464
        let mut acc = ChangeEntropyAccumulator::new();
        for i in 0..4 {
            acc.record_file("a.rs", FileActionKind::Modify, i * 86400);
        }
        for i in 0..2 {
            acc.record_file("b.rs", FileActionKind::Modify, i * 86400 + 50);
        }
        for i in 0..2 {
            acc.record_file("c.rs", FileActionKind::Modify, i * 86400 + 100);
        }
        let report = acc.finalize(0, DEFAULT_WINDOW_SECONDS);
        assert_eq!(report.windows.len(), 1);
        let expected_h = 1.5;
        let expected_h_norm = expected_h / 3.0_f64.log2();
        assert!(
            (report.windows[0].raw_entropy - expected_h).abs() < 1e-10,
            "H={}, expected={}",
            report.windows[0].raw_entropy,
            expected_h
        );
        assert!(
            (report.windows[0].normalized_entropy - expected_h_norm).abs() < 1e-10,
            "H_norm={}, expected={}",
            report.windows[0].normalized_entropy,
            expected_h_norm
        );
    }

    #[test]
    fn test_normalization_range() {
        // 5 files, uniform distribution → H_norm = 1.0 (maximum)
        let mut acc = ChangeEntropyAccumulator::new();
        for i in 0..5 {
            acc.record_file(&format!("file{i}.rs"), FileActionKind::Modify, i * 86400);
        }
        let report = acc.finalize(0, DEFAULT_WINDOW_SECONDS);
        let h_norm = report.windows[0].normalized_entropy;
        assert!(
            (0.0..=1.0 + f64::EPSILON).contains(&h_norm),
            "H_norm={} out of [0, 1]",
            h_norm
        );
        assert!(
            (h_norm - 1.0).abs() < 1e-10,
            "uniform dist should give H_norm=1.0, got {}",
            h_norm
        );
    }

    #[test]
    fn test_multiple_windows() {
        // Events spanning 90 days → 3 windows of 30 days each
        let mut acc = ChangeEntropyAccumulator::new();
        // Window 1: days 0-29 — single file (entropy 0)
        for i in 0..5 {
            acc.record_file("a.rs", FileActionKind::Modify, i * 86400);
        }
        // Window 2: days 30-59 — two files (entropy 1.0)
        let w2_start = DEFAULT_WINDOW_SECONDS;
        for i in 0..5 {
            acc.record_file("a.rs", FileActionKind::Modify, w2_start + i * 86400);
            acc.record_file("b.rs", FileActionKind::Modify, w2_start + i * 86400 + 100);
        }
        // Window 3: days 60-89 — three files (entropy ~1.585)
        let w3_start = 2 * DEFAULT_WINDOW_SECONDS;
        for i in 0..3 {
            acc.record_file("a.rs", FileActionKind::Modify, w3_start + i * 86400);
            acc.record_file("b.rs", FileActionKind::Modify, w3_start + i * 86400 + 50);
            acc.record_file("c.rs", FileActionKind::Modify, w3_start + i * 86400 + 100);
        }
        let report = acc.finalize(0, 3 * DEFAULT_WINDOW_SECONDS);
        assert_eq!(report.windows.len(), 3, "expected 3 windows");
        assert!(
            report.windows[0].normalized_entropy < report.windows[1].normalized_entropy,
            "w0={} should be < w1={}",
            report.windows[0].normalized_entropy,
            report.windows[1].normalized_entropy
        );
    }

    #[test]
    fn test_peak_window_index() {
        let mut acc = ChangeEntropyAccumulator::new();
        // Window 1: low entropy
        acc.record_file("a.rs", FileActionKind::Modify, 86400);
        // Window 2: high entropy (many files)
        let w2_start = DEFAULT_WINDOW_SECONDS;
        for i in 0..10 {
            acc.record_file(
                &format!("file{i}.rs"),
                FileActionKind::Modify,
                w2_start + i * 86400,
            );
        }
        let report = acc.finalize(0, 2 * DEFAULT_WINDOW_SECONDS);
        assert_eq!(report.max_entropy_window_idx, Some(1));
    }

    #[test]
    fn test_trend_increasing() {
        let mut acc = ChangeEntropyAccumulator::new();
        // First half: 1 file (low entropy)
        for i in 0..10 {
            acc.record_file("a.rs", FileActionKind::Modify, i * 86400);
        }
        // Second half: 5 files (high entropy)
        let w2_start = DEFAULT_WINDOW_SECONDS;
        for i in 0..5 {
            for j in 0..5 {
                acc.record_file(
                    &format!("file{j}.rs"),
                    FileActionKind::Modify,
                    w2_start + i * 86400 + j * 100,
                );
            }
        }
        let report = acc.finalize(0, 2 * DEFAULT_WINDOW_SECONDS);
        assert_eq!(report.trend, EntropyTrend::Increasing);
    }

    #[test]
    fn test_trend_decreasing() {
        let mut acc = ChangeEntropyAccumulator::new();
        // First half: 5 files (high entropy)
        for i in 0..5 {
            for j in 0..5 {
                acc.record_file(
                    &format!("file{j}.rs"),
                    FileActionKind::Modify,
                    i * 86400 + j * 100,
                );
            }
        }
        // Second half: 1 file (low entropy)
        let w2_start = DEFAULT_WINDOW_SECONDS;
        for i in 0..10 {
            acc.record_file("a.rs", FileActionKind::Modify, w2_start + i * 86400);
        }
        let report = acc.finalize(0, 2 * DEFAULT_WINDOW_SECONDS);
        assert_eq!(report.trend, EntropyTrend::Decreasing);
    }

    #[test]
    fn test_default_impl() {
        let acc = ChangeEntropyAccumulator::default();
        let report = acc.finalize(0, 0);
        assert!(report.windows.is_empty());
    }

    #[test]
    fn test_delete_action_excluded() {
        // Delete actions should not contribute to change entropy
        let mut acc = ChangeEntropyAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Delete, 86400);
        let report = acc.finalize(0, DEFAULT_WINDOW_SECONDS);
        assert!(report.windows.is_empty());
    }

    #[test]
    fn test_create_action_included() {
        let mut acc = ChangeEntropyAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create, 86400);
        let report = acc.finalize(0, DEFAULT_WINDOW_SECONDS);
        assert_eq!(report.windows.len(), 1);
        assert_eq!(report.windows[0].total_modifications, 1);
    }
}
