// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Technical debt velocity analysis (M25).
//!
//! Tracks whether technical debt is growing or shrinking over time by
//! analyzing the ratio of maintenance commits to feature commits in
//! rolling time windows.
//!
//! # Research Basis
//!
//! Wehaibi et al. (2016) "Examining the Impact of Self-Admitted Technical
//! Debt on Software Quality" (SANER, DOI: 10.1109/SANER.2016.72).
//!
//! Maldonado & Shihab (2015) "Detecting and Quantifying Different Types
//! of Self-Admitted Technical Debt" (MSR, DOI: 10.1109/MSR.2015.25).
//!
//! Bavota & Russo (2016) "A Large-Scale Empirical Study on Self-Admitted
//! Technical Debt" (MSR, DOI: 10.1145/2901739.2901742).
//!
//! # Algorithm
//!
//! 1. Classify commits by message keywords and action pattern:
//!    - Fix/maintenance: message contains fix, bug, patch, repair, hotfix
//!    - Feature: message contains feat, add, implement, new, introduce
//!    - Debt reduction: message contains refactor, clean, rename, simplify
//!    - Unknown: no message or no matching keywords
//! 2. Compute rolling 30-day windows of commit type ratios
//! 3. TD velocity = `d(maintenance_ratio) / dt`
//!    - Positive = debt accumulating
//!    - Negative = debt being paid down
//!
//! # Complexity
//!
//! - Accumulation: O(1) per commit
//! - Finalization: O(N log N) for sorting + O(W) for windowing

/// Classification of a commit's purpose.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommitPurpose {
    /// Bug fix or maintenance.
    Maintenance,
    /// New feature or enhancement.
    Feature,
    /// Refactoring or cleanup (debt reduction).
    DebtReduction,
    /// Cannot be classified.
    Unknown,
}

impl CommitPurpose {
    /// Returns a human-readable label.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Maintenance => "Maintenance",
            Self::Feature => "Feature",
            Self::DebtReduction => "Debt Reduction",
            Self::Unknown => "Unknown",
        }
    }
}

/// A time window with commit type ratios.
#[derive(Debug, Clone)]
pub struct DebtWindow {
    /// Window start timestamp.
    pub start: i64,
    /// Window end timestamp.
    pub end: i64,
    /// Ratio of maintenance commits in this window.
    pub maintenance_ratio: f64,
    /// Ratio of feature commits.
    pub feature_ratio: f64,
    /// Ratio of debt reduction commits.
    pub debt_reduction_ratio: f64,
    /// Total commits in this window.
    pub total_commits: u32,
}

/// Debt velocity trend classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DebtTrend {
    /// Debt is accumulating (maintenance ratio increasing).
    Accumulating,
    /// Debt is being paid down (maintenance ratio decreasing).
    PayingDown,
    /// No clear trend.
    Stable,
}

impl DebtTrend {
    /// Returns a human-readable label.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Accumulating => "Accumulating",
            Self::PayingDown => "Paying Down",
            Self::Stable => "Stable",
        }
    }
}

/// Complete technical debt velocity report.
#[derive(Debug, Clone)]
pub struct TechDebtVelocityReport {
    /// Rolling windows of commit type ratios.
    pub windows: Vec<DebtWindow>,
    /// Overall debt trend.
    pub trend: DebtTrend,
    /// Slope of maintenance ratio over time (positive = accumulating).
    pub velocity_slope: f64,
    /// Overall maintenance ratio.
    pub overall_maintenance_ratio: f64,
    /// Overall feature ratio.
    pub overall_feature_ratio: f64,
    /// Overall debt reduction ratio.
    pub overall_debt_reduction_ratio: f64,
    /// Total commits classified.
    pub total_classified: usize,
}

/// Window size: 30 days in seconds.
const WINDOW_SIZE: i64 = 30 * 86400;

/// Accumulates technical debt velocity data from commit stream.
pub struct TechDebtVelocityAccumulator {
    commits: Vec<(i64, CommitPurpose)>,
}

impl Default for TechDebtVelocityAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl TechDebtVelocityAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            commits: Vec::new(),
        }
    }

    /// Records a commit with optional message for classification.
    pub fn record_commit(&mut self, timestamp: i64, message: Option<&str>) {
        let purpose = classify_commit(message);
        self.commits.push((timestamp, purpose));
    }

    /// Finalizes the technical debt velocity report.
    #[must_use]
    pub fn finalize(mut self) -> TechDebtVelocityReport {
        if self.commits.is_empty() {
            return TechDebtVelocityReport {
                windows: Vec::new(),
                trend: DebtTrend::Stable,
                velocity_slope: 0.0,
                overall_maintenance_ratio: 0.0,
                overall_feature_ratio: 0.0,
                overall_debt_reduction_ratio: 0.0,
                total_classified: 0,
            };
        }

        self.commits.sort_by_key(|&(t, _)| t);

        let t_min = self.commits.first().map_or(0, |&(t, _)| t);
        let t_max = self.commits.last().map_or(0, |&(t, _)| t);

        // Count overall
        let mut maint_count = 0u32;
        let mut feat_count = 0u32;
        let mut debt_count = 0u32;
        let total = self.commits.len() as u32;

        for &(_, purpose) in &self.commits {
            match purpose {
                CommitPurpose::Maintenance => maint_count += 1,
                CommitPurpose::Feature => feat_count += 1,
                CommitPurpose::DebtReduction => debt_count += 1,
                CommitPurpose::Unknown => {}
            }
        }

        let total_f = f64::from(total.max(1));
        let overall_maintenance_ratio = f64::from(maint_count) / total_f;
        let overall_feature_ratio = f64::from(feat_count) / total_f;
        let overall_debt_reduction_ratio = f64::from(debt_count) / total_f;

        // Build rolling windows
        let mut windows = Vec::new();
        let mut win_start = t_min;
        while win_start < t_max {
            let win_end = win_start + WINDOW_SIZE;
            let mut w_maint = 0u32;
            let mut w_feat = 0u32;
            let mut w_debt = 0u32;
            let mut w_total = 0u32;

            for &(t, purpose) in &self.commits {
                if t >= win_start && t < win_end {
                    w_total += 1;
                    match purpose {
                        CommitPurpose::Maintenance => w_maint += 1,
                        CommitPurpose::Feature => w_feat += 1,
                        CommitPurpose::DebtReduction => w_debt += 1,
                        CommitPurpose::Unknown => {}
                    }
                }
            }

            if w_total > 0 {
                let wt = f64::from(w_total);
                windows.push(DebtWindow {
                    start: win_start,
                    end: win_end,
                    maintenance_ratio: f64::from(w_maint) / wt,
                    feature_ratio: f64::from(w_feat) / wt,
                    debt_reduction_ratio: f64::from(w_debt) / wt,
                    total_commits: w_total,
                });
            }

            win_start = win_end;
        }

        // Compute velocity slope via simple linear regression on maintenance_ratio
        let velocity_slope = compute_slope(&windows);
        let trend = if velocity_slope > 0.01 {
            DebtTrend::Accumulating
        } else if velocity_slope < -0.01 {
            DebtTrend::PayingDown
        } else {
            DebtTrend::Stable
        };

        TechDebtVelocityReport {
            windows,
            trend,
            velocity_slope,
            overall_maintenance_ratio,
            overall_feature_ratio,
            overall_debt_reduction_ratio,
            total_classified: total as usize,
        }
    }
}

/// Classifies a commit based on its message keywords.
fn classify_commit(message: Option<&str>) -> CommitPurpose {
    let msg = match message {
        Some(m) => m.to_lowercase(),
        None => return CommitPurpose::Unknown,
    };

    // Check for maintenance keywords
    let maintenance_keywords = [
        "fix",
        "bug",
        "patch",
        "repair",
        "hotfix",
        "revert",
        "regression",
        "crash",
        "error",
        "broken",
        "issue",
    ];
    let feature_keywords = [
        "feat",
        "add",
        "implement",
        "new",
        "introduce",
        "support",
        "enable",
        "create",
    ];
    let debt_keywords = [
        "refactor",
        "clean",
        "rename",
        "simplify",
        "reorganize",
        "extract",
        "move",
        "deprecate",
        "remove unused",
        "dead code",
    ];

    let has_maintenance = maintenance_keywords.iter().any(|k| msg.contains(k));
    let has_feature = feature_keywords.iter().any(|k| msg.contains(k));
    let has_debt = debt_keywords.iter().any(|k| msg.contains(k));

    // Priority: debt reduction > feature > maintenance > unknown
    // Rationale: explicit refactoring markers (refactor:, clean:, simplify:)
    // indicate intentional debt work even if maintenance keywords appear incidentally.
    if has_debt {
        CommitPurpose::DebtReduction
    } else if has_feature {
        CommitPurpose::Feature
    } else if has_maintenance {
        CommitPurpose::Maintenance
    } else {
        CommitPurpose::Unknown
    }
}

/// Computes the slope of `maintenance_ratio` over window indices via linear regression.
fn compute_slope(windows: &[DebtWindow]) -> f64 {
    let n = windows.len();
    if n < 2 {
        return 0.0;
    }
    let n_f = n as f64;
    let mut sum_x = 0.0;
    let mut sum_y = 0.0;
    let mut sum_xy = 0.0;
    let mut sum_x2 = 0.0;

    for (i, w) in windows.iter().enumerate() {
        let x = i as f64;
        let y = w.maintenance_ratio;
        sum_x += x;
        sum_y += y;
        sum_xy += x * y;
        sum_x2 += x * x;
    }

    let sum_x_sq = sum_x * sum_x;
    let denom = n_f * sum_x2 - sum_x_sq;
    if denom.abs() < 1e-15 {
        return 0.0;
    }
    (n_f * sum_xy - sum_x * sum_y) / denom
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let acc = TechDebtVelocityAccumulator::new();
        let report = acc.finalize();
        assert!(report.windows.is_empty());
        assert_eq!(report.trend, DebtTrend::Stable);
    }

    #[test]
    fn test_classify_fix() {
        assert_eq!(
            classify_commit(Some("fix: resolve null pointer crash")),
            CommitPurpose::Maintenance
        );
    }

    #[test]
    fn test_classify_feature() {
        assert_eq!(
            classify_commit(Some("feat: add user authentication")),
            CommitPurpose::Feature
        );
    }

    #[test]
    fn test_classify_refactor() {
        assert_eq!(
            classify_commit(Some("refactor: simplify error handling")),
            CommitPurpose::DebtReduction
        );
    }

    #[test]
    fn test_classify_unknown() {
        assert_eq!(
            classify_commit(Some("update version number")),
            CommitPurpose::Unknown
        );
        assert_eq!(classify_commit(None), CommitPurpose::Unknown);
    }

    #[test]
    fn test_window_generation() {
        let mut acc = TechDebtVelocityAccumulator::new();
        // Spread commits over 60 days
        for i in 0..60 {
            let msg = if i % 3 == 0 {
                Some("fix: something")
            } else {
                Some("feat: something")
            };
            acc.record_commit(i * 86400, msg);
        }
        let report = acc.finalize();
        assert!(!report.windows.is_empty());
    }

    #[test]
    fn test_default_impl() {
        let acc = TechDebtVelocityAccumulator::default();
        let report = acc.finalize();
        assert!(report.windows.is_empty());
    }
}
