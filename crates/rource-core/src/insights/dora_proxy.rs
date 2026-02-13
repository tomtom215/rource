// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! DORA proxy metrics derived purely from VCS commit data.
//!
//! Computes VCS-derivable proxies for the five DORA metrics without requiring
//! CI/CD instrumentation. These are clearly labeled as *proxies*, not exact
//! DORA metrics, since precise measurement requires deployment pipeline data.
//!
//! # Metrics
//!
//! | Proxy | DORA Metric | VCS Signal |
//! |-------|-------------|------------|
//! | Merge frequency | Deployment Frequency | Merge-to-main commit frequency |
//! | Branch duration | Lead Time for Changes | Branch-creation-to-merge duration |
//! | Revert ratio | Change Failure Rate | Ratio of revert commits |
//! | Recovery time | Time to Restore | Time between revert and fix-forward |
//! | Rework ratio | Rework Rate | Ratio of fix/bugfix commits to total |
//!
//! # Academic Citations
//!
//! - Forsgren, Humble & Kim (2018) — "Accelerate" (DORA metrics definition)
//! - Google DORA (2024) — 10-year retrospective, introduction of 5th metric
//! - Google DORA (2025) — Stability over speed finding

use rustc_hash::FxHashMap;

/// Result of DORA proxy metric computation.
#[derive(Debug)]
pub struct DoraProxyReport {
    /// Proxy: merge-to-main frequency (merges per week).
    pub merge_frequency_per_week: f64,
    /// Proxy: average branch duration in hours (estimated from commit gaps).
    pub avg_branch_duration_hours: f64,
    /// Proxy: ratio of revert commits to total commits [0.0, 1.0].
    pub revert_ratio: f64,
    /// Proxy: average time in hours between a revert and subsequent fix-forward.
    pub avg_recovery_hours: f64,
    /// Proxy: ratio of fix/bugfix commits to total commits [0.0, 1.0].
    pub rework_ratio: f64,
    /// Total commits analyzed.
    pub total_commits: u32,
    /// Number of detected revert commits.
    pub revert_count: u32,
    /// Number of detected fix/bugfix commits.
    pub fix_count: u32,
    /// Number of detected merge commits.
    pub merge_count: u32,
    /// DORA performance tier based on proxy signals.
    pub performance_tier: DoraPerformanceTier,
    /// Per-window trend data (4-week sliding windows).
    pub windows: Vec<DoraWindow>,
}

/// A time window of DORA proxy metrics for trend analysis.
#[derive(Debug)]
pub struct DoraWindow {
    /// Window start timestamp (unix epoch seconds).
    pub start_ts: i64,
    /// Window end timestamp (unix epoch seconds).
    pub end_ts: i64,
    /// Merges in this window.
    pub merge_count: u32,
    /// Reverts in this window.
    pub revert_count: u32,
    /// Fix commits in this window.
    pub fix_count: u32,
    /// Total commits in this window.
    pub total_commits: u32,
}

/// DORA performance tier classification.
///
/// Based on Forsgren et al. (2018) "Accelerate" tier definitions,
/// adapted for VCS-proxy signals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DoraPerformanceTier {
    /// Elite: high merge frequency, low revert ratio, fast recovery.
    Elite,
    /// High: good metrics across the board.
    High,
    /// Medium: moderate performance.
    Medium,
    /// Low: infrequent merges, high revert ratio, slow recovery.
    Low,
}

impl std::fmt::Display for DoraPerformanceTier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Elite => write!(f, "elite"),
            Self::High => write!(f, "high"),
            Self::Medium => write!(f, "medium"),
            Self::Low => write!(f, "low"),
        }
    }
}

/// Accumulator for DORA proxy data during single-pass commit processing.
#[derive(Default)]
pub struct DoraProxyAccumulator {
    /// Epoch seconds of detected merge-indicator commits.
    merges: Vec<i64>,
    /// Epoch seconds of detected revert commits.
    reverts: Vec<i64>,
    /// Epoch seconds of detected fix/bugfix commits.
    fixes: Vec<i64>,
    /// All commit epoch seconds for windowing.
    commits: Vec<i64>,
}

impl DoraProxyAccumulator {
    /// Creates a new accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Records a single commit for DORA proxy analysis.
    ///
    /// Classifies based on commit message heuristics:
    /// - Merge: message starts with "Merge" or contains "merge branch"
    /// - Revert: message starts with "Revert" or contains "revert"
    /// - Fix: message contains "fix", "bugfix", "hotfix", "patch"
    pub fn record_commit(&mut self, timestamp: i64, message: Option<&str>) {
        self.commits.push(timestamp);

        let Some(msg) = message else {
            return;
        };

        let lower = msg.to_lowercase();

        if lower.starts_with("merge")
            || lower.contains("merge branch")
            || lower.contains("merge pull request")
        {
            self.merges.push(timestamp);
        }

        if lower.starts_with("revert") || lower.contains("revert \"") || lower.contains("revert '")
        {
            self.reverts.push(timestamp);
        }

        if is_fix_commit(&lower) {
            self.fixes.push(timestamp);
        }
    }

    /// Finalizes the accumulator into a report.
    #[must_use]
    pub fn finalize(self) -> DoraProxyReport {
        let total = self.commits.len() as u32;
        if total == 0 {
            return DoraProxyReport {
                merge_frequency_per_week: 0.0,
                avg_branch_duration_hours: 0.0,
                revert_ratio: 0.0,
                avg_recovery_hours: 0.0,
                rework_ratio: 0.0,
                total_commits: 0,
                revert_count: 0,
                fix_count: 0,
                merge_count: 0,
                performance_tier: DoraPerformanceTier::Low,
                windows: Vec::new(),
            };
        }

        let t_min = self.commits.iter().copied().min().unwrap_or(0);
        let t_max = self.commits.iter().copied().max().unwrap_or(0);
        let span_weeks = ((t_max - t_min) as f64) / (7.0 * 86400.0);
        let span_weeks = span_weeks.max(1.0); // avoid division by zero

        let merge_count = self.merges.len() as u32;
        let revert_count = self.reverts.len() as u32;
        let fix_count = self.fixes.len() as u32;

        let merge_frequency_per_week = f64::from(merge_count) / span_weeks;
        let revert_ratio = f64::from(revert_count) / f64::from(total);
        let rework_ratio = f64::from(fix_count) / f64::from(total);

        // Estimate branch duration from merge gaps
        let avg_branch_duration_hours = compute_avg_branch_duration(&self.merges);

        // Estimate recovery time from revert → next non-revert commit
        let avg_recovery_hours = compute_avg_recovery_time(&self.reverts, &self.commits);

        // Compute sliding windows (4-week windows)
        let windows = compute_windows(
            &self.commits,
            &self.merges,
            &self.reverts,
            &self.fixes,
            t_min,
            t_max,
        );

        let performance_tier =
            classify_tier(merge_frequency_per_week, revert_ratio, avg_recovery_hours);

        DoraProxyReport {
            merge_frequency_per_week,
            avg_branch_duration_hours,
            revert_ratio,
            avg_recovery_hours,
            rework_ratio,
            total_commits: total,
            revert_count,
            fix_count,
            merge_count,
            performance_tier,
            windows,
        }
    }
}

/// Checks if a lowercased commit message indicates a fix/bugfix commit.
fn is_fix_commit(lower: &str) -> bool {
    lower.starts_with("fix")
        || lower.contains("bugfix")
        || lower.contains("hotfix")
        || lower.contains("bug fix")
        || lower.starts_with("patch")
        || (lower.contains("fix(") && lower.contains("):"))
        || (lower.contains("fix:"))
}

/// Computes average branch duration from merge timestamps.
///
/// Uses inter-merge intervals as a proxy for branch lifetime.
fn compute_avg_branch_duration(merge_ts: &[i64]) -> f64 {
    if merge_ts.len() < 2 {
        return 0.0;
    }
    let mut sorted = merge_ts.to_vec();
    sorted.sort_unstable();
    let gaps: Vec<f64> = sorted
        .windows(2)
        .map(|w| (w[1] - w[0]) as f64 / 3600.0)
        .collect();
    if gaps.is_empty() {
        return 0.0;
    }
    gaps.iter().sum::<f64>() / gaps.len() as f64
}

/// Computes average recovery time: time from revert to next non-revert commit.
fn compute_avg_recovery_time(revert_ts: &[i64], all_ts: &[i64]) -> f64 {
    if revert_ts.is_empty() || all_ts.is_empty() {
        return 0.0;
    }
    let mut sorted_all = all_ts.to_vec();
    sorted_all.sort_unstable();

    let mut recovery_times = Vec::new();
    let revert_set: rustc_hash::FxHashSet<i64> = revert_ts.iter().copied().collect();

    for &rt in revert_ts {
        // Find the next commit after this revert
        if let Ok(idx) = sorted_all.binary_search(&rt) {
            for &t in &sorted_all[idx + 1..] {
                if !revert_set.contains(&t) {
                    recovery_times.push((t - rt) as f64 / 3600.0);
                    break;
                }
            }
        }
    }

    if recovery_times.is_empty() {
        return 0.0;
    }
    recovery_times.iter().sum::<f64>() / recovery_times.len() as f64
}

/// Computes 4-week sliding windows for trend analysis.
fn compute_windows(
    all_ts: &[i64],
    merge_ts: &[i64],
    revert_ts: &[i64],
    fix_ts: &[i64],
    t_min: i64,
    t_max: i64,
) -> Vec<DoraWindow> {
    const WINDOW_SECS: i64 = 4 * 7 * 86400; // 4 weeks
    const STEP_SECS: i64 = 7 * 86400; // 1 week step

    if t_max - t_min < WINDOW_SECS {
        // Too short for windowing — return single window
        return vec![DoraWindow {
            start_ts: t_min,
            end_ts: t_max,
            merge_count: merge_ts.len() as u32,
            revert_count: revert_ts.len() as u32,
            fix_count: fix_ts.len() as u32,
            total_commits: all_ts.len() as u32,
        }];
    }

    let merge_set: FxHashMap<i64, u32> = count_in_buckets(merge_ts, t_min, STEP_SECS);
    let revert_set: FxHashMap<i64, u32> = count_in_buckets(revert_ts, t_min, STEP_SECS);
    let fix_set: FxHashMap<i64, u32> = count_in_buckets(fix_ts, t_min, STEP_SECS);
    let all_set: FxHashMap<i64, u32> = count_in_buckets(all_ts, t_min, STEP_SECS);

    let mut windows = Vec::new();
    let mut start = t_min;
    while start + WINDOW_SECS <= t_max + STEP_SECS {
        let end = start + WINDOW_SECS;
        let weeks_in_window = WINDOW_SECS / STEP_SECS;
        let mut m = 0u32;
        let mut r = 0u32;
        let mut f = 0u32;
        let mut t = 0u32;
        for i in 0..weeks_in_window {
            let bucket = start + i * STEP_SECS;
            m += merge_set.get(&bucket).copied().unwrap_or(0);
            r += revert_set.get(&bucket).copied().unwrap_or(0);
            f += fix_set.get(&bucket).copied().unwrap_or(0);
            t += all_set.get(&bucket).copied().unwrap_or(0);
        }
        windows.push(DoraWindow {
            start_ts: start,
            end_ts: end,
            merge_count: m,
            revert_count: r,
            fix_count: f,
            total_commits: t,
        });
        start += STEP_SECS;
    }
    // Limit to last 52 windows (1 year)
    if windows.len() > 52 {
        windows = windows.split_off(windows.len() - 52);
    }
    windows
}

/// Counts items falling into weekly buckets.
fn count_in_buckets(timestamps: &[i64], t_min: i64, step: i64) -> FxHashMap<i64, u32> {
    let mut map = FxHashMap::default();
    for &t in timestamps {
        let bucket = t_min + ((t - t_min) / step) * step;
        *map.entry(bucket).or_insert(0) += 1;
    }
    map
}

/// Classifies DORA performance tier based on proxy signals.
///
/// Adapted from Forsgren et al. (2018) "Accelerate" tier definitions:
/// - Elite: merges daily+, <5% revert rate, <1h recovery
/// - High: merges weekly, <10% revert rate, <24h recovery
/// - Medium: merges bi-weekly, <15% revert rate, <72h recovery
/// - Low: everything else
fn classify_tier(
    merge_freq_per_week: f64,
    revert_ratio: f64,
    avg_recovery_hours: f64,
) -> DoraPerformanceTier {
    // Score each dimension 0-3 (elite=3, high=2, medium=1, low=0)
    let freq_score = if merge_freq_per_week >= 5.0 {
        3
    } else if merge_freq_per_week >= 1.0 {
        2
    } else {
        u32::from(merge_freq_per_week >= 0.5)
    };

    let revert_score = if revert_ratio < 0.05 {
        3
    } else if revert_ratio < 0.10 {
        2
    } else {
        u32::from(revert_ratio < 0.15)
    };

    let recovery_score = if avg_recovery_hours > 0.0 && avg_recovery_hours < 1.0 {
        3
    } else if avg_recovery_hours <= 0.0 || avg_recovery_hours < 24.0 {
        2
    } else {
        u32::from(avg_recovery_hours < 72.0)
    };

    let total = freq_score + revert_score + recovery_score;
    match total {
        7..=9 => DoraPerformanceTier::Elite,
        5..=6 => DoraPerformanceTier::High,
        3..=4 => DoraPerformanceTier::Medium,
        _ => DoraPerformanceTier::Low,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = DoraProxyAccumulator::new();
        let report = acc.finalize();
        assert_eq!(report.total_commits, 0);
        assert_eq!(report.merge_count, 0);
        assert_eq!(report.revert_count, 0);
        assert_eq!(report.fix_count, 0);
        assert_eq!(report.performance_tier, DoraPerformanceTier::Low);
    }

    #[test]
    fn test_merge_detection() {
        let mut acc = DoraProxyAccumulator::new();
        acc.record_commit(1000, Some("Merge branch 'feature'"));
        acc.record_commit(2000, Some("Merge pull request #42"));
        acc.record_commit(3000, Some("feat: add button"));
        let report = acc.finalize();
        assert_eq!(report.merge_count, 2);
        assert_eq!(report.total_commits, 3);
    }

    #[test]
    fn test_revert_detection() {
        let mut acc = DoraProxyAccumulator::new();
        acc.record_commit(1000, Some("Revert \"feat: broken feature\""));
        acc.record_commit(2000, Some("Revert 'buggy commit'"));
        acc.record_commit(3000, Some("fix: something"));
        let report = acc.finalize();
        assert_eq!(report.revert_count, 2);
    }

    #[test]
    fn test_fix_detection() {
        let mut acc = DoraProxyAccumulator::new();
        acc.record_commit(1000, Some("fix: resolve crash"));
        acc.record_commit(2000, Some("fix(auth): token expiry"));
        acc.record_commit(3000, Some("bugfix: handle null"));
        acc.record_commit(4000, Some("hotfix: emergency patch"));
        acc.record_commit(5000, Some("feat: new feature"));
        let report = acc.finalize();
        assert_eq!(report.fix_count, 4);
        let expected_ratio = 4.0 / 5.0;
        assert!((report.rework_ratio - expected_ratio).abs() < 1e-10);
    }

    #[test]
    fn test_no_messages_no_classification() {
        let mut acc = DoraProxyAccumulator::new();
        acc.record_commit(1000, None);
        acc.record_commit(2000, None);
        let report = acc.finalize();
        assert_eq!(report.total_commits, 2);
        assert_eq!(report.merge_count, 0);
        assert_eq!(report.revert_count, 0);
        assert_eq!(report.fix_count, 0);
    }

    #[test]
    fn test_revert_ratio_calculation() {
        let mut acc = DoraProxyAccumulator::new();
        for i in 0..10 {
            let msg = if i < 2 {
                "Revert \"some change\""
            } else {
                "feat: normal commit"
            };
            acc.record_commit(i64::from(i) * 86400, Some(msg));
        }
        let report = acc.finalize();
        assert_eq!(report.revert_count, 2);
        assert!((report.revert_ratio - 0.2).abs() < 1e-10);
    }

    #[test]
    fn test_merge_frequency_calculation() {
        let mut acc = DoraProxyAccumulator::new();
        // 7 merges over 7 weeks = 1 merge/week
        for i in 0..7 {
            acc.record_commit(i64::from(i) * 7 * 86400, Some("Merge branch 'feature'"));
        }
        let report = acc.finalize();
        assert_eq!(report.merge_count, 7);
        // 7 merges / 6 weeks span ≈ 1.17 merges/week
        assert!(report.merge_frequency_per_week > 1.0);
    }

    #[test]
    fn test_elite_tier() {
        let tier = classify_tier(7.0, 0.02, 0.5);
        assert_eq!(tier, DoraPerformanceTier::Elite);
    }

    #[test]
    fn test_low_tier() {
        let tier = classify_tier(0.1, 0.25, 200.0);
        assert_eq!(tier, DoraPerformanceTier::Low);
    }

    #[test]
    fn test_recovery_time_computation() {
        let revert_ts = vec![1000];
        let all_ts = vec![500, 1000, 1500, 2000];
        let recovery = compute_avg_recovery_time(&revert_ts, &all_ts);
        // Recovery from 1000 to 1500 = 500s = 500/3600 hours
        assert!((recovery - 500.0 / 3600.0).abs() < 1e-6);
    }

    #[test]
    fn test_display_tiers() {
        assert_eq!(format!("{}", DoraPerformanceTier::Elite), "elite");
        assert_eq!(format!("{}", DoraPerformanceTier::High), "high");
        assert_eq!(format!("{}", DoraPerformanceTier::Medium), "medium");
        assert_eq!(format!("{}", DoraPerformanceTier::Low), "low");
    }

    #[test]
    fn test_windowing_short_span() {
        let mut acc = DoraProxyAccumulator::new();
        acc.record_commit(1000, Some("feat: a"));
        acc.record_commit(2000, Some("feat: b"));
        let report = acc.finalize();
        // Span too short for 4-week windows → single window
        assert_eq!(report.windows.len(), 1);
        assert_eq!(report.windows[0].total_commits, 2);
    }
}
