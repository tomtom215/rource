// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Commit rhythm and cadence analysis.
//!
//! Analyzes the distribution of inter-commit intervals per developer to
//! identify contribution patterns and engagement trends.
//!
//! # Research Basis
//!
//! Eyolfson et al. (2014) "Correlations Between Bugginess and Time" (MSR)
//! showed that commit timing patterns correlate with code quality. Sliwerski
//! et al. (2005) "When Do Changes Induce Fixes?" found that temporal patterns
//! predict fix-inducing changes.
//!
//! # Algorithm
//!
//! For each author, compute inter-commit intervals (time between consecutive
//! commits). From these intervals, derive:
//! - Mean and median interval
//! - Standard deviation and coefficient of variation (CV)
//! - Trend classification based on CV:
//!   - `Regular` (CV < 0.5): consistent contributor
//!   - `Bursty` (CV > 1.5): long gaps followed by burst activity
//!   - `Moderate`: between regular and bursty
//!
//! # Complexity
//!
//! - Accumulation: O(1) per commit
//! - Finalization: O(N log N) per author for sorting timestamps

use rustc_hash::FxHashMap;

/// Cadence classification based on coefficient of variation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CadenceType {
    /// Consistent commit intervals (CV < 0.5).
    Regular,
    /// Moderate variation in commit intervals (0.5 ≤ CV ≤ 1.5).
    Moderate,
    /// Long gaps followed by intense bursts (CV > 1.5).
    Bursty,
}

/// Cadence profile for a single developer.
#[derive(Debug, Clone)]
pub struct AuthorCadence {
    /// Author name.
    pub author: String,
    /// Total number of commits.
    pub commit_count: usize,
    /// Mean inter-commit interval in seconds.
    pub mean_interval: f64,
    /// Median inter-commit interval in seconds.
    pub median_interval: f64,
    /// Standard deviation of inter-commit intervals.
    pub std_dev: f64,
    /// Coefficient of variation (`std_dev` / mean).
    pub cv: f64,
    /// Cadence classification.
    pub cadence_type: CadenceType,
    /// First commit timestamp.
    pub first_commit: i64,
    /// Last commit timestamp.
    pub last_commit: i64,
    /// Active span in seconds (last - first commit).
    pub active_span: i64,
}

/// Aggregate cadence report for all developers.
#[derive(Debug, Clone)]
pub struct CadenceReport {
    /// Per-author cadence profiles, sorted by commit count descending.
    pub authors: Vec<AuthorCadence>,
    /// Team-wide mean inter-commit interval.
    pub team_mean_interval: f64,
    /// Number of regular contributors.
    pub regular_count: usize,
    /// Number of bursty contributors.
    pub bursty_count: usize,
    /// Number of moderate contributors.
    pub moderate_count: usize,
}

/// Accumulates per-author timestamps during commit processing.
pub struct CadenceAccumulator {
    /// Author → sorted list of commit timestamps.
    author_timestamps: FxHashMap<String, Vec<i64>>,
}

impl Default for CadenceAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl CadenceAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            author_timestamps: FxHashMap::default(),
        }
    }

    /// Records a commit timestamp for an author.
    pub fn record_commit(&mut self, author: &str, timestamp: i64) {
        self.author_timestamps
            .entry(author.to_string())
            .or_default()
            .push(timestamp);
    }

    /// Finalizes the accumulator into a [`CadenceReport`].
    #[must_use]
    pub fn finalize(self) -> CadenceReport {
        let mut authors: Vec<AuthorCadence> = self
            .author_timestamps
            .into_iter()
            .filter(|(_, ts)| ts.len() >= 2)
            .map(|(author, mut timestamps)| {
                timestamps.sort_unstable();
                compute_author_cadence(author, &timestamps)
            })
            .collect();

        // Sort by commit count descending
        authors.sort_by(|a, b| b.commit_count.cmp(&a.commit_count));

        let team_mean_interval = compute_team_mean(&authors);
        let regular_count = authors
            .iter()
            .filter(|a| a.cadence_type == CadenceType::Regular)
            .count();
        let bursty_count = authors
            .iter()
            .filter(|a| a.cadence_type == CadenceType::Bursty)
            .count();
        let moderate_count = authors
            .iter()
            .filter(|a| a.cadence_type == CadenceType::Moderate)
            .count();

        CadenceReport {
            authors,
            team_mean_interval,
            regular_count,
            bursty_count,
            moderate_count,
        }
    }
}

/// Computes cadence profile for a single author from sorted timestamps.
fn compute_author_cadence(author: String, timestamps: &[i64]) -> AuthorCadence {
    let commit_count = timestamps.len();
    let first_commit = timestamps[0];
    let last_commit = timestamps[timestamps.len() - 1];
    let active_span = last_commit - first_commit;

    // Compute inter-commit intervals
    let intervals: Vec<f64> = timestamps
        .windows(2)
        .map(|w| (w[1] - w[0]) as f64)
        .collect();

    let mean_interval = intervals.iter().sum::<f64>() / intervals.len() as f64;

    let mut sorted_intervals = intervals.clone();
    sorted_intervals.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let median_interval = if sorted_intervals.len() % 2 == 0 {
        let mid = sorted_intervals.len() / 2;
        (sorted_intervals[mid - 1] + sorted_intervals[mid]) / 2.0
    } else {
        sorted_intervals[sorted_intervals.len() / 2]
    };

    // Standard deviation
    let variance = intervals
        .iter()
        .map(|&x| (x - mean_interval).powi(2))
        .sum::<f64>()
        / intervals.len() as f64;
    let std_dev = variance.sqrt();

    // Coefficient of variation
    let cv = if mean_interval > 0.0 {
        std_dev / mean_interval
    } else {
        0.0
    };

    let cadence_type = if cv < 0.5 {
        CadenceType::Regular
    } else if cv > 1.5 {
        CadenceType::Bursty
    } else {
        CadenceType::Moderate
    };

    AuthorCadence {
        author,
        commit_count,
        mean_interval,
        median_interval,
        std_dev,
        cv,
        cadence_type,
        first_commit,
        last_commit,
        active_span,
    }
}

/// Computes team-wide mean interval (weighted by author commit count).
fn compute_team_mean(authors: &[AuthorCadence]) -> f64 {
    if authors.is_empty() {
        return 0.0;
    }
    let total_weight: usize = authors.iter().map(|a| a.commit_count).sum();
    if total_weight == 0 {
        return 0.0;
    }
    let weighted_sum: f64 = authors
        .iter()
        .map(|a| a.mean_interval * a.commit_count as f64)
        .sum();
    weighted_sum / total_weight as f64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = CadenceAccumulator::new();
        let report = acc.finalize();
        assert!(report.authors.is_empty());
        assert!((report.team_mean_interval - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_single_commit_author_excluded() {
        let mut acc = CadenceAccumulator::new();
        acc.record_commit("Alice", 1000);
        let report = acc.finalize();
        // Authors with < 2 commits are excluded (no intervals to analyze)
        assert!(report.authors.is_empty());
    }

    #[test]
    fn test_regular_cadence() {
        let mut acc = CadenceAccumulator::new();
        // Perfectly regular: every 1000 seconds
        for i in 0..10 {
            acc.record_commit("Alice", i * 1000);
        }
        let report = acc.finalize();
        assert_eq!(report.authors.len(), 1);
        let alice = &report.authors[0];
        assert_eq!(alice.commit_count, 10);
        assert!((alice.mean_interval - 1000.0).abs() < f64::EPSILON);
        assert!((alice.std_dev - 0.0).abs() < f64::EPSILON);
        assert!((alice.cv - 0.0).abs() < f64::EPSILON);
        assert_eq!(alice.cadence_type, CadenceType::Regular);
    }

    #[test]
    fn test_bursty_cadence() {
        let mut acc = CadenceAccumulator::new();
        // Long gap followed by rapid burst
        acc.record_commit("Bob", 0);
        acc.record_commit("Bob", 100_000); // 100k seconds gap
        acc.record_commit("Bob", 100_001); // 1 second gap
        acc.record_commit("Bob", 100_002); // 1 second gap
        acc.record_commit("Bob", 100_003); // 1 second gap
        let report = acc.finalize();
        let bob = &report.authors[0];
        assert!(
            bob.cv > 1.5,
            "bursty pattern should have CV > 1.5, got {}",
            bob.cv
        );
        assert_eq!(bob.cadence_type, CadenceType::Bursty);
    }

    #[test]
    fn test_multiple_authors() {
        let mut acc = CadenceAccumulator::new();
        // Regular Alice: every 1000 seconds
        for i in 0..5 {
            acc.record_commit("Alice", i * 1000);
        }
        // Bursty Bob: huge gap then rapid fire (CV >> 1.5)
        acc.record_commit("Bob", 0);
        acc.record_commit("Bob", 1_000_000); // 1M second gap
        acc.record_commit("Bob", 1_000_001); // 1 second gap
        acc.record_commit("Bob", 1_000_002); // 1 second gap
        acc.record_commit("Bob", 1_000_003); // 1 second gap
        acc.record_commit("Bob", 1_000_004); // 1 second gap

        let report = acc.finalize();
        assert_eq!(report.authors.len(), 2);
        // Sorted by commit count: Bob (6) > Alice (5)
        assert_eq!(report.authors[0].author, "Bob");
        assert_eq!(report.authors[1].author, "Alice");
        assert_eq!(report.regular_count, 1);
        assert_eq!(report.bursty_count, 1);
    }

    #[test]
    fn test_median_even_intervals() {
        let mut acc = CadenceAccumulator::new();
        // Intervals: 100, 200, 300, 400 → median = (200+300)/2 = 250
        acc.record_commit("Alice", 0);
        acc.record_commit("Alice", 100);
        acc.record_commit("Alice", 300);
        acc.record_commit("Alice", 600);
        acc.record_commit("Alice", 1000);

        let report = acc.finalize();
        let alice = &report.authors[0];
        // Intervals: 100, 200, 300, 400
        // Sorted: 100, 200, 300, 400
        // Median (even): (200 + 300) / 2 = 250
        assert!(
            (alice.median_interval - 250.0).abs() < f64::EPSILON,
            "median={}, expected=250.0",
            alice.median_interval
        );
    }

    #[test]
    fn test_median_odd_intervals() {
        let mut acc = CadenceAccumulator::new();
        // Intervals: 100, 200, 300 → median = 200
        acc.record_commit("Alice", 0);
        acc.record_commit("Alice", 100);
        acc.record_commit("Alice", 300);
        acc.record_commit("Alice", 600);

        let report = acc.finalize();
        let alice = &report.authors[0];
        // Intervals: 100, 200, 300
        // Sorted: 100, 200, 300
        // Median (odd): 200
        assert!(
            (alice.median_interval - 200.0).abs() < f64::EPSILON,
            "median={}, expected=200.0",
            alice.median_interval
        );
    }

    #[test]
    fn test_active_span() {
        let mut acc = CadenceAccumulator::new();
        acc.record_commit("Alice", 1000);
        acc.record_commit("Alice", 5000);
        let report = acc.finalize();
        let alice = &report.authors[0];
        assert_eq!(alice.first_commit, 1000);
        assert_eq!(alice.last_commit, 5000);
        assert_eq!(alice.active_span, 4000);
    }

    #[test]
    fn test_team_mean_interval() {
        let mut acc = CadenceAccumulator::new();
        // Alice: 5 commits, mean interval = 1000
        for i in 0..5 {
            acc.record_commit("Alice", i * 1000);
        }
        // Bob: 3 commits, mean interval = 2000
        for i in 0..3 {
            acc.record_commit("Bob", i * 2000);
        }

        let report = acc.finalize();
        // Weighted mean: (1000*5 + 2000*3) / (5+3) = 11000/8 = 1375
        assert!(
            (report.team_mean_interval - 1375.0).abs() < f64::EPSILON,
            "team_mean={}, expected=1375.0",
            report.team_mean_interval
        );
    }

    #[test]
    fn test_unsorted_timestamps() {
        let mut acc = CadenceAccumulator::new();
        // Timestamps arrive out of order
        acc.record_commit("Alice", 5000);
        acc.record_commit("Alice", 1000);
        acc.record_commit("Alice", 3000);

        let report = acc.finalize();
        let alice = &report.authors[0];
        // After sorting: [1000, 3000, 5000]
        // Intervals: [2000, 2000]
        assert!(
            (alice.mean_interval - 2000.0).abs() < f64::EPSILON,
            "mean_interval={}, expected=2000.0",
            alice.mean_interval
        );
        assert_eq!(alice.first_commit, 1000);
        assert_eq!(alice.last_commit, 5000);
    }

    #[test]
    fn test_default() {
        let acc = CadenceAccumulator::default();
        let report = acc.finalize();
        assert!(report.authors.is_empty());
    }

    #[test]
    fn test_zero_interval_cv() {
        let mut acc = CadenceAccumulator::new();
        // All commits at the same timestamp
        acc.record_commit("Alice", 5000);
        acc.record_commit("Alice", 5000);
        acc.record_commit("Alice", 5000);

        let report = acc.finalize();
        let alice = &report.authors[0];
        assert!((alice.mean_interval - 0.0).abs() < f64::EPSILON);
        assert!((alice.cv - 0.0).abs() < f64::EPSILON);
        assert_eq!(alice.cadence_type, CadenceType::Regular);
    }
}
