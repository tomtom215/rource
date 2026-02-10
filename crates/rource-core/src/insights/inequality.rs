// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Contribution inequality analysis via the Gini coefficient.
//!
//! Measures how unevenly commits are distributed across developers using the
//! Gini coefficient — the standard measure of inequality from economics, applied
//! to software engineering contributions.
//!
//! # Research Basis
//!
//! Chelkowski, Gloor & Jemielniak (2016) "Inequalities in Open Source Software
//! Development: Analysis of Contributor's Commits in Apache Software Foundation
//! Projects" (PLOS ONE 11(4)) validated the Gini coefficient on 263 Apache
//! projects. 88.97% had Gini between 0.6–0.9, with only 3.35% of committers
//! contributing 50.13% of all commits.
//!
//! # Algorithm
//!
//! Given sorted commit counts c = \[c₁, c₂, …, cₙ\] (ascending):
//!
//! Gini = (2 × Σ(i × cᵢ)) / (n × Σ(c)) − (n + 1) / n
//!
//! Also computes:
//! - Lorenz curve points: (cumulative share of developers, cumulative share of commits)
//! - Top-K% share: what fraction of commits come from the top K% of developers
//! - Gini over sliding 90-day windows for trend analysis
//!
//! # Complexity
//!
//! - Computation: O(A log A) where A = number of unique authors (for sorting)
//! - Windowed Gini: O(W × Aᵥ log Aᵥ) where W = windows, Aᵥ = avg authors per window

use rustc_hash::FxHashMap;

/// Sliding window size for Gini trend analysis: 90 days (quarterly).
const GINI_WINDOW_SECONDS: i64 = 90 * 86400;

/// Number of evenly-spaced points on the Lorenz curve.
const LORENZ_CURVE_POINTS: usize = 20;

/// Contribution inequality report for the repository.
#[derive(Debug, Clone)]
pub struct InequalityReport {
    /// Overall Gini coefficient in \[0, 1\].
    /// 0.0 = perfect equality; 1.0 = total inequality.
    pub gini_coefficient: f64,
    /// Fraction of commits by top 1% of developers.
    pub top_1_pct_share: f64,
    /// Fraction of commits by top 10% of developers.
    pub top_10_pct_share: f64,
    /// Fraction of commits by top 20% of developers.
    pub top_20_pct_share: f64,
    /// Number of unique developers.
    pub total_developers: u32,
    /// Total commits.
    pub total_commits: u32,
    /// Lorenz curve points as (`developer_share`, `commit_share`) pairs.
    /// Both values in \[0, 1\].
    pub lorenz_curve: Vec<(f64, f64)>,
    /// Gini coefficient over sliding time windows.
    pub windows: Vec<InequalityWindow>,
}

/// Gini coefficient for a sliding time window.
#[derive(Debug, Clone)]
pub struct InequalityWindow {
    /// Start timestamp of this window.
    pub window_start: i64,
    /// End timestamp of this window.
    pub window_end: i64,
    /// Gini coefficient for this window.
    pub gini: f64,
    /// Active developers in this window.
    pub developer_count: u32,
}

/// Accumulates per-window author commit counts for Gini trend analysis.
pub struct InequalityAccumulator {
    /// (timestamp, author) pairs for windowed computation.
    events: Vec<(i64, String)>,
}

impl Default for InequalityAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl InequalityAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self { events: Vec::new() }
    }

    /// Records a commit event for windowed Gini analysis.
    pub fn record_commit(&mut self, author: &str, timestamp: i64) {
        self.events.push((timestamp, author.to_string()));
    }

    /// Finalizes into windowed Gini data.
    #[must_use]
    pub fn finalize(self, t_min: i64, t_max: i64) -> Vec<InequalityWindow> {
        if self.events.is_empty() || t_min >= t_max {
            return Vec::new();
        }

        let mut windows = Vec::new();
        let mut window_start = t_min;

        while window_start < t_max {
            let window_end = (window_start + GINI_WINDOW_SECONDS).min(t_max);
            let mut author_counts: FxHashMap<&str, u32> = FxHashMap::default();

            for (ts, author) in &self.events {
                if *ts >= window_start && *ts < window_end {
                    *author_counts.entry(author.as_str()).or_insert(0) += 1;
                }
            }

            if !author_counts.is_empty() {
                let counts: Vec<u32> = author_counts.values().copied().collect();
                let gini = compute_gini_from_counts(&counts);
                windows.push(InequalityWindow {
                    window_start,
                    window_end,
                    gini,
                    developer_count: author_counts.len() as u32,
                });
            }

            window_start += GINI_WINDOW_SECONDS;
        }

        windows
    }
}

/// Computes the full inequality report from author commit counts.
///
/// # Arguments
///
/// * `unique_authors` - Map of author name → total commit count
/// * `windows` - Pre-computed windowed Gini data from accumulator
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn compute_inequality(
    unique_authors: &FxHashMap<String, u32>,
    windows: Vec<InequalityWindow>,
) -> InequalityReport {
    if unique_authors.is_empty() {
        return InequalityReport {
            gini_coefficient: 0.0,
            top_1_pct_share: 0.0,
            top_10_pct_share: 0.0,
            top_20_pct_share: 0.0,
            total_developers: 0,
            total_commits: 0,
            lorenz_curve: Vec::new(),
            windows,
        };
    }

    let mut counts: Vec<u32> = unique_authors.values().copied().collect();
    counts.sort_unstable();

    let n = counts.len();
    let total: u32 = counts.iter().sum();
    let total_f = f64::from(total);

    let gini_coefficient = compute_gini_from_counts(&counts);

    // Compute top-K% shares
    let top_1_pct_share = compute_top_k_share(&counts, total_f, 1);
    let top_10_pct_share = compute_top_k_share(&counts, total_f, 10);
    let top_20_pct_share = compute_top_k_share(&counts, total_f, 20);

    // Compute Lorenz curve
    let lorenz_curve = compute_lorenz_curve(&counts, total_f, n);

    InequalityReport {
        gini_coefficient,
        top_1_pct_share,
        top_10_pct_share,
        top_20_pct_share,
        total_developers: n as u32,
        total_commits: total,
        lorenz_curve,
        windows,
    }
}

/// Computes the Gini coefficient from a slice of (possibly unsorted) counts.
///
/// Formula (sorted ascending): Gini = (2 × Σ(i × cᵢ)) / (n × Σ(c)) − (n + 1) / n
/// where i is 1-indexed.
fn compute_gini_from_counts(counts: &[u32]) -> f64 {
    if counts.is_empty() {
        return 0.0;
    }

    let n = counts.len();
    if n == 1 {
        return 0.0;
    }

    let mut sorted = counts.to_vec();
    sorted.sort_unstable();

    let total: f64 = sorted.iter().map(|&c| f64::from(c)).sum();
    if total == 0.0 {
        return 0.0;
    }

    let n_f = n as f64;
    let weighted_sum: f64 = sorted
        .iter()
        .enumerate()
        .map(|(i, &c)| (i as f64 + 1.0) * f64::from(c))
        .sum();

    let gini = (2.0 * weighted_sum) / (n_f * total) - (n_f + 1.0) / n_f;

    // Clamp to [0, 1] to handle floating-point edge cases
    gini.clamp(0.0, 1.0)
}

/// Computes the share of commits from the top `k_pct`% of developers.
fn compute_top_k_share(sorted_counts: &[u32], total: f64, k_pct: usize) -> f64 {
    if sorted_counts.is_empty() || total == 0.0 {
        return 0.0;
    }

    let n = sorted_counts.len();
    // At least 1 developer in the top-K%
    let top_k_count = ((n * k_pct) as f64 / 100.0).ceil().max(1.0) as usize;
    let top_k_count = top_k_count.min(n);

    let top_sum: f64 = sorted_counts[n - top_k_count..]
        .iter()
        .map(|&c| f64::from(c))
        .sum();
    top_sum / total
}

/// Computes Lorenz curve points from sorted commit counts.
fn compute_lorenz_curve(sorted_counts: &[u32], total: f64, n: usize) -> Vec<(f64, f64)> {
    if n == 0 || total == 0.0 {
        return Vec::new();
    }

    let mut curve = Vec::with_capacity(LORENZ_CURVE_POINTS + 1);
    // Always include origin
    curve.push((0.0, 0.0));

    let cumulative: Vec<f64> = sorted_counts
        .iter()
        .scan(0.0, |acc, &c| {
            *acc += f64::from(c);
            Some(*acc)
        })
        .collect();

    for i in 1..=LORENZ_CURVE_POINTS {
        let dev_share = i as f64 / LORENZ_CURVE_POINTS as f64;
        // Map dev_share to an index in the sorted counts
        let idx = ((dev_share * n as f64).ceil() as usize).min(n) - 1;
        let commit_share = cumulative[idx] / total;
        curve.push((dev_share, commit_share));
    }

    curve
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_authors(entries: &[(&str, u32)]) -> FxHashMap<String, u32> {
        entries
            .iter()
            .map(|(name, count)| (name.to_string(), *count))
            .collect()
    }

    #[test]
    fn test_empty_report() {
        let report = compute_inequality(&FxHashMap::default(), Vec::new());
        assert!((report.gini_coefficient - 0.0).abs() < f64::EPSILON);
        assert_eq!(report.total_developers, 0);
        assert_eq!(report.total_commits, 0);
        assert!(report.lorenz_curve.is_empty());
    }

    #[test]
    fn test_perfect_equality() {
        // 4 developers, 10 commits each → Gini = 0.0
        let authors = make_authors(&[("A", 10), ("B", 10), ("C", 10), ("D", 10)]);
        let report = compute_inequality(&authors, Vec::new());
        assert!(
            report.gini_coefficient.abs() < 1e-10,
            "gini={}, expected=0.0",
            report.gini_coefficient
        );
        assert_eq!(report.total_developers, 4);
        assert_eq!(report.total_commits, 40);
    }

    #[test]
    fn test_total_inequality() {
        // 1 developer: 100 commits, 3 developers: 0 commits
        // sorted: [0, 0, 0, 100], n=4, sum=100
        // Gini = (2*(1*0+2*0+3*0+4*100))/(4*100) - 5/4
        //      = 800/400 - 1.25 = 2.0 - 1.25 = 0.75
        let authors = make_authors(&[("A", 100), ("B", 0), ("C", 0), ("D", 0)]);
        let report = compute_inequality(&authors, Vec::new());
        assert!(
            (report.gini_coefficient - 0.75).abs() < 1e-10,
            "gini={}, expected=0.75",
            report.gini_coefficient
        );
    }

    #[test]
    fn test_known_gini_value() {
        // Commits [1, 2, 3, 4] → sorted ascending
        // Gini = (2*(1*1+2*2+3*3+4*4))/(4*10) - 5/4
        //      = (2*30)/40 - 1.25 = 1.5 - 1.25 = 0.25
        let authors = make_authors(&[("A", 1), ("B", 2), ("C", 3), ("D", 4)]);
        let report = compute_inequality(&authors, Vec::new());
        assert!(
            (report.gini_coefficient - 0.25).abs() < 1e-10,
            "gini={}, expected=0.25",
            report.gini_coefficient
        );
    }

    #[test]
    fn test_single_developer() {
        // 1 developer → Gini = 0.0 (trivially equal)
        let authors = make_authors(&[("A", 50)]);
        let report = compute_inequality(&authors, Vec::new());
        assert!(
            report.gini_coefficient.abs() < f64::EPSILON,
            "gini={}, expected=0.0",
            report.gini_coefficient
        );
        assert_eq!(report.total_developers, 1);
        assert_eq!(report.total_commits, 50);
    }

    #[test]
    fn test_two_developers_equal() {
        let authors = make_authors(&[("A", 50), ("B", 50)]);
        let report = compute_inequality(&authors, Vec::new());
        assert!(
            report.gini_coefficient.abs() < 1e-10,
            "gini={}, expected=0.0",
            report.gini_coefficient
        );
    }

    #[test]
    fn test_two_developers_unequal() {
        // [10, 90], n=2, sum=100
        // Gini = (2*(1*10+2*90))/(2*100) - 3/2
        //      = (2*190)/200 - 1.5 = 1.9 - 1.5 = 0.4
        let authors = make_authors(&[("A", 90), ("B", 10)]);
        let report = compute_inequality(&authors, Vec::new());
        assert!(
            (report.gini_coefficient - 0.4).abs() < 1e-10,
            "gini={}, expected=0.4",
            report.gini_coefficient
        );
    }

    #[test]
    fn test_top_percentile_shares() {
        // 10 developers: 9 with 1 commit, 1 with 91 commits
        // Top 10% = 1 person = 91/100 = 0.91
        let authors = make_authors(&[
            ("A", 1),
            ("B", 1),
            ("C", 1),
            ("D", 1),
            ("E", 1),
            ("F", 1),
            ("G", 1),
            ("H", 1),
            ("I", 1),
            ("J", 91),
        ]);
        let report = compute_inequality(&authors, Vec::new());
        assert!(
            (report.top_10_pct_share - 0.91).abs() < 1e-10,
            "top_10_pct_share={}, expected=0.91",
            report.top_10_pct_share
        );
        // Top 20% = 2 people = (91+1)/100 = 0.92
        assert!(
            (report.top_20_pct_share - 0.92).abs() < 1e-10,
            "top_20_pct_share={}, expected=0.92",
            report.top_20_pct_share
        );
    }

    #[test]
    fn test_lorenz_curve_endpoints() {
        let authors = make_authors(&[("A", 10), ("B", 20), ("C", 30)]);
        let report = compute_inequality(&authors, Vec::new());
        // First point is always (0, 0)
        assert!(
            (report.lorenz_curve[0].0).abs() < f64::EPSILON,
            "first x={}",
            report.lorenz_curve[0].0
        );
        assert!(
            (report.lorenz_curve[0].1).abs() < f64::EPSILON,
            "first y={}",
            report.lorenz_curve[0].1
        );
        // Last point is always (1, 1)
        let last = report.lorenz_curve.last().unwrap();
        assert!((last.0 - 1.0).abs() < f64::EPSILON, "last x={}", last.0);
        assert!((last.1 - 1.0).abs() < f64::EPSILON, "last y={}", last.1);
    }

    #[test]
    fn test_lorenz_curve_monotonic() {
        let authors = make_authors(&[("A", 5), ("B", 15), ("C", 30), ("D", 50)]);
        let report = compute_inequality(&authors, Vec::new());
        for i in 1..report.lorenz_curve.len() {
            assert!(
                report.lorenz_curve[i].0 >= report.lorenz_curve[i - 1].0,
                "x not monotonic at i={}: {} < {}",
                i,
                report.lorenz_curve[i].0,
                report.lorenz_curve[i - 1].0
            );
            assert!(
                report.lorenz_curve[i].1 >= report.lorenz_curve[i - 1].1,
                "y not monotonic at i={}: {} < {}",
                i,
                report.lorenz_curve[i].1,
                report.lorenz_curve[i - 1].1
            );
        }
    }

    #[test]
    fn test_default_impl() {
        let acc = InequalityAccumulator::default();
        let windows = acc.finalize(0, 0);
        assert!(windows.is_empty());
    }

    #[test]
    fn test_windowed_gini() {
        let mut acc = InequalityAccumulator::new();
        // Window 1: 0 to 90 days — equal distribution
        for i in 0..10 {
            acc.record_commit("Alice", i * 86400);
            acc.record_commit("Bob", i * 86400 + 100);
        }
        // Window 2: 90 to 180 days — unequal distribution
        let w2_start = GINI_WINDOW_SECONDS;
        for i in 0..20 {
            acc.record_commit("Alice", w2_start + i * 86400);
        }
        acc.record_commit("Bob", w2_start + 100);

        let windows = acc.finalize(0, 2 * GINI_WINDOW_SECONDS);
        assert_eq!(
            windows.len(),
            2,
            "expected 2 windows, got {}",
            windows.len()
        );
        // Window 1 should be more equal than window 2
        assert!(
            windows[0].gini < windows[1].gini,
            "window[0].gini={} should be < window[1].gini={}",
            windows[0].gini,
            windows[1].gini
        );
    }

    #[test]
    fn test_gini_arithmetic_not_mutation_fragile() {
        // Verify the exact formula step by step to kill arithmetic mutants
        // [2, 8], n=2, sum=10
        // weighted_sum = 1*2 + 2*8 = 18
        // Gini = 2*18/(2*10) - 3/2 = 36/20 - 1.5 = 1.8 - 1.5 = 0.3
        let gini = compute_gini_from_counts(&[2, 8]);
        assert!((gini - 0.3).abs() < 1e-10, "gini={}, expected=0.3", gini);
        // If * were +: 2*(2+8)/(2*10) - 3/2 = 20/20 - 1.5 = -0.5 → clamped to 0
        // If * were /: would produce different result
        // If - were +: 1.8 + 1.5 = 3.3 → clamped to 1
        // The exact value 0.3 kills all these mutants
    }

    // --- Mutation-killing tests ---

    #[test]
    fn test_gini_single_element_returns_zero() {
        // Kills: replace == with != in `if n == 1`
        let gini = compute_gini_from_counts(&[42]);
        assert!(
            gini.abs() < f64::EPSILON,
            "single element gini={}, expected=0.0",
            gini
        );
    }

    #[test]
    fn test_gini_all_zeros_returns_zero() {
        // Kills: replace == with != in `if total == 0.0`
        let gini = compute_gini_from_counts(&[0, 0, 0]);
        assert!(
            gini.abs() < f64::EPSILON,
            "all zeros gini={}, expected=0.0",
            gini
        );
    }

    #[test]
    fn test_top_k_share_division_exact() {
        // Kills: replace / with * in `top_sum / total`
        // [1, 1, 1, 7], total=10, top 1 = 7 → 7/10 = 0.7
        let counts = [1, 1, 1, 7];
        let share = compute_top_k_share(&counts, 10.0, 10);
        // top 10% of 4 = ceil(0.4) = 1 → top 1 developer
        assert!((share - 0.7).abs() < 1e-10, "share={}, expected=0.7", share);
    }

    #[test]
    fn test_top_k_at_least_one_developer() {
        // Top 1% of 3 developers → ceil(0.03) = 1 (at least 1)
        // [10, 20, 70], top 1 = 70 → 70/100 = 0.7
        let counts = [10, 20, 70];
        let share = compute_top_k_share(&counts, 100.0, 1);
        assert!((share - 0.7).abs() < 1e-10, "share={}, expected=0.7", share);
    }

    #[test]
    fn test_lorenz_curve_point_count() {
        // Lorenz curve should have LORENZ_CURVE_POINTS + 1 points (including origin)
        let authors = make_authors(&[("A", 10), ("B", 20), ("C", 30)]);
        let report = compute_inequality(&authors, Vec::new());
        assert_eq!(
            report.lorenz_curve.len(),
            LORENZ_CURVE_POINTS + 1,
            "curve should have {} points",
            LORENZ_CURVE_POINTS + 1
        );
    }

    #[test]
    fn test_windowed_gini_tmin_gte_tmax() {
        // Kills: replace >= with > in `if t_min >= t_max`
        let mut acc = InequalityAccumulator::new();
        acc.record_commit("Alice", 100);
        let windows = acc.finalize(100, 100); // t_min == t_max
        assert!(windows.is_empty(), "t_min == t_max should produce empty");
    }

    #[test]
    fn test_windowed_gini_division_arithmetic() {
        // Verify windowed Gini uses correct arithmetic (kills + vs * in formula)
        // Window with [5, 15] → gini = 0.25
        // sorted: [5, 15], n=2, sum=20
        // weighted = 1*5 + 2*15 = 35
        // gini = 2*35/(2*20) - 3/2 = 70/40 - 1.5 = 1.75 - 1.5 = 0.25
        let mut acc = InequalityAccumulator::new();
        for _ in 0..5 {
            acc.record_commit("Alice", 86400);
        }
        for _ in 0..15 {
            acc.record_commit("Bob", 2 * 86400);
        }
        let windows = acc.finalize(0, GINI_WINDOW_SECONDS);
        assert_eq!(windows.len(), 1);
        assert!(
            (windows[0].gini - 0.25).abs() < 1e-10,
            "gini={}, expected=0.25",
            windows[0].gini
        );
    }

    #[test]
    fn test_gini_weighted_sum_indexing() {
        // Kills: replace + 1.0 with - 1.0 in `(i as f64 + 1.0)`
        // [1, 3], n=2, sum=4
        // Correct: weighted = 1*1 + 2*3 = 7, gini = 2*7/(2*4) - 3/2 = 14/8 - 1.5 = 0.25
        // If + → -: weighted = (-1)*1 + 0*3 = -1, gini = 2*(-1)/(2*4) - 3/2 = -0.25 - 1.5
        let gini = compute_gini_from_counts(&[1, 3]);
        assert!((gini - 0.25).abs() < 1e-10, "gini={}, expected=0.25", gini);
    }

    #[test]
    fn test_gini_clamp_prevents_negative() {
        // All equal → formula gives exactly 0 (or tiny negative from FP)
        let gini = compute_gini_from_counts(&[10, 10, 10, 10]);
        assert!(gini >= 0.0, "gini should be clamped to >= 0, got {}", gini);
        assert!(gini.abs() < 1e-10);
    }

    // ── Property-based tests ────────────────────────────────────────

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Gini coefficient is always in [0, 1] for any non-empty input.
            #[test]
            fn prop_gini_bounded(counts in proptest::collection::vec(0u32..1000, 1..50)) {
                let gini = compute_gini_from_counts(&counts);
                prop_assert!(gini >= 0.0, "gini={} < 0", gini);
                prop_assert!(gini <= 1.0, "gini={} > 1", gini);
            }

            /// Equal counts always produce Gini = 0.
            #[test]
            fn prop_gini_zero_for_equal(val in 1u32..1000, n in 2usize..20) {
                let counts = vec![val; n];
                let gini = compute_gini_from_counts(&counts);
                prop_assert!(gini.abs() < 1e-10, "equal counts: gini={}, expected≈0", gini);
            }

            /// Lorenz curve is monotonically non-decreasing in both coordinates.
            #[test]
            fn prop_lorenz_monotonic(
                entries in proptest::collection::vec((1u32..100,), 2..20)
            ) {
                let mut authors: FxHashMap<String, u32> = FxHashMap::default();
                for (i, (c,)) in entries.iter().enumerate() {
                    authors.insert(format!("dev{i}"), *c);
                }
                let report = compute_inequality(&authors, Vec::new());
                for i in 1..report.lorenz_curve.len() {
                    prop_assert!(
                        report.lorenz_curve[i].0 >= report.lorenz_curve[i - 1].0,
                        "x not monotonic at i={}", i
                    );
                    prop_assert!(
                        report.lorenz_curve[i].1 >= report.lorenz_curve[i - 1].1,
                        "y not monotonic at i={}", i
                    );
                }
            }

            /// Top-K share is always in [0, 1] and non-decreasing as K increases.
            #[test]
            fn prop_top_k_share_bounded_and_monotonic(
                entries in proptest::collection::vec(1u32..100, 2..30)
            ) {
                let mut sorted = entries;
                sorted.sort_unstable();
                let total: f64 = sorted.iter().map(|&c| f64::from(c)).sum();
                if total > 0.0 {
                    let s1 = compute_top_k_share(&sorted, total, 1);
                    let s10 = compute_top_k_share(&sorted, total, 10);
                    let s20 = compute_top_k_share(&sorted, total, 20);
                    prop_assert!((0.0..=1.0).contains(&s1), "top_1%={}", s1);
                    prop_assert!((0.0..=1.0).contains(&s10), "top_10%={}", s10);
                    prop_assert!((0.0..=1.0).contains(&s20), "top_20%={}", s20);
                    prop_assert!(s20 >= s10, "top_20% < top_10%: {} < {}", s20, s10);
                    prop_assert!(s10 >= s1, "top_10% < top_1%: {} < {}", s10, s1);
                }
            }

            /// Lorenz curve always starts at (0,0) and ends at (1,1).
            #[test]
            fn prop_lorenz_endpoints(
                entries in proptest::collection::vec(1u32..100, 1..20)
            ) {
                let mut authors: FxHashMap<String, u32> = FxHashMap::default();
                for (i, &c) in entries.iter().enumerate() {
                    authors.insert(format!("dev{i}"), c);
                }
                let report = compute_inequality(&authors, Vec::new());
                if !report.lorenz_curve.is_empty() {
                    let first = report.lorenz_curve.first().unwrap();
                    let last = report.lorenz_curve.last().unwrap();
                    prop_assert!(first.0.abs() < f64::EPSILON, "first.x={}", first.0);
                    prop_assert!(first.1.abs() < f64::EPSILON, "first.y={}", first.1);
                    prop_assert!((last.0 - 1.0).abs() < f64::EPSILON, "last.x={}", last.0);
                    prop_assert!((last.1 - 1.0).abs() < f64::EPSILON, "last.y={}", last.1);
                }
            }
        }
    }
}
