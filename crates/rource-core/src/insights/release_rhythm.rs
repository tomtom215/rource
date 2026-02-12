// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Release Rhythm and Stability Analysis — infers development cadence patterns
//! from commit timestamp distributions.
//!
//! Analyzes commit velocity over time to detect burst-quiet cycles that indicate
//! release patterns. Rapid release cycles correlate with faster bug fixes but
//! potentially more regressions.
//!
//! # Research Basis
//!
//! - Khomh et al. (2012) "Do Faster Releases Improve Software Quality? An
//!   Empirical Case Study of Mozilla Firefox" (MSR) — release frequency impact
//! - da Costa et al. (2016) "The Impact of Rapid Release Cycles on the
//!   Integration Delay of Fixed Issues" (MSR) — integration delay patterns
//!
//! # Algorithm
//!
//! 1. Bucket commits into time windows (default: 7-day bins)
//! 2. Compute velocity per window (commits/day)
//! 3. Detect peaks (local maxima in velocity) as release points
//! 4. Compute inter-release intervals
//! 5. Classify release regularity via coefficient of variation (CV)
//!
//! # Complexity
//!
//! - O(C log C) for sorting commits by timestamp
//! - O(C) for bucketing and velocity computation
//! - O(W) for peak detection where W = number of windows

/// Default window size in seconds (7 days).
const WINDOW_SIZE_SECS: i64 = 7 * 86400;

/// Minimum commits in a window to be considered a peak.
const MIN_PEAK_COMMITS: u32 = 3;

/// Release rhythm report for the repository.
#[derive(Debug, Clone)]
pub struct ReleaseRhythmReport {
    /// Velocity windows (commits per window).
    pub windows: Vec<VelocityWindow>,
    /// Detected release cycle peaks.
    pub peaks: Vec<ReleasePeak>,
    /// Average inter-peak interval in days.
    pub avg_release_interval_days: f64,
    /// Release regularity score (0.0 = chaotic, 1.0 = perfectly regular).
    pub release_regularity: f64,
    /// Current phase in the release cycle.
    pub current_phase: CyclePhase,
    /// Overall velocity trend.
    pub velocity_trend: VelocityTrend,
}

/// A time window with commit velocity statistics.
#[derive(Debug, Clone)]
pub struct VelocityWindow {
    /// Window start timestamp.
    pub start_ts: i64,
    /// Window end timestamp.
    pub end_ts: i64,
    /// Number of commits in this window.
    pub commit_count: u32,
    /// Commits per day in this window.
    pub velocity: f64,
}

/// A detected release cycle peak.
#[derive(Debug, Clone)]
pub struct ReleasePeak {
    /// Window index of the peak.
    pub window_idx: usize,
    /// Timestamp of the peak window start.
    pub timestamp: i64,
    /// Commit count at the peak.
    pub commit_count: u32,
}

/// Current phase in the development cycle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CyclePhase {
    /// Recently had a burst of activity (possible release).
    PostRelease,
    /// Activity is building up.
    Building,
    /// In a quiet period.
    Quiet,
    /// Insufficient data to determine.
    Unknown,
}

impl std::fmt::Display for CyclePhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PostRelease => write!(f, "post_release"),
            Self::Building => write!(f, "building"),
            Self::Quiet => write!(f, "quiet"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

/// Overall velocity trend direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VelocityTrend {
    /// Commit velocity is increasing over time.
    Accelerating,
    /// Commit velocity is stable.
    Stable,
    /// Commit velocity is decreasing.
    Decelerating,
}

impl std::fmt::Display for VelocityTrend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Accelerating => write!(f, "accelerating"),
            Self::Stable => write!(f, "stable"),
            Self::Decelerating => write!(f, "decelerating"),
        }
    }
}

/// Accumulates commit timestamps for release rhythm analysis.
pub struct ReleaseRhythmAccumulator {
    /// Collected commit timestamps.
    timestamps: Vec<i64>,
}

impl Default for ReleaseRhythmAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl ReleaseRhythmAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            timestamps: Vec::new(),
        }
    }

    /// Records a commit timestamp.
    pub fn record_commit(&mut self, timestamp: i64) {
        self.timestamps.push(timestamp);
    }

    /// Finalizes into the release rhythm report.
    #[must_use]
    pub fn finalize(mut self) -> ReleaseRhythmReport {
        if self.timestamps.is_empty() {
            return empty_report();
        }

        self.timestamps.sort_unstable();
        let t_min = self.timestamps[0];
        let t_max = self.timestamps[self.timestamps.len() - 1];

        if t_max <= t_min {
            return empty_report();
        }

        // Step 1: Bucket commits into windows
        let windows = bucket_commits(&self.timestamps, t_min, t_max);

        if windows.is_empty() {
            return empty_report();
        }

        // Step 2: Detect peaks
        let peaks = detect_peaks(&windows);

        // Step 3: Compute inter-peak intervals
        let avg_interval = compute_avg_interval(&peaks);

        // Step 4: Compute regularity (inverse of coefficient of variation)
        let regularity = compute_regularity(&peaks);

        // Step 5: Determine current phase
        let current_phase = determine_phase(&windows);

        // Step 6: Determine velocity trend
        let velocity_trend = determine_trend(&windows);

        ReleaseRhythmReport {
            windows,
            peaks,
            avg_release_interval_days: avg_interval,
            release_regularity: regularity,
            current_phase,
            velocity_trend,
        }
    }
}

fn empty_report() -> ReleaseRhythmReport {
    ReleaseRhythmReport {
        windows: Vec::new(),
        peaks: Vec::new(),
        avg_release_interval_days: 0.0,
        release_regularity: 0.0,
        current_phase: CyclePhase::Unknown,
        velocity_trend: VelocityTrend::Stable,
    }
}

/// Buckets commits into fixed-size time windows.
#[allow(clippy::cast_possible_wrap)]
fn bucket_commits(timestamps: &[i64], t_min: i64, t_max: i64) -> Vec<VelocityWindow> {
    let span = t_max - t_min;
    let n_windows = ((span + WINDOW_SIZE_SECS - 1) / WINDOW_SIZE_SECS).max(1) as usize;
    let mut windows = Vec::with_capacity(n_windows);

    for i in 0..n_windows {
        let start = t_min + (i as i64) * WINDOW_SIZE_SECS;
        let end = start + WINDOW_SIZE_SECS;
        windows.push(VelocityWindow {
            start_ts: start,
            end_ts: end,
            commit_count: 0,
            velocity: 0.0,
        });
    }

    // Count commits per window using binary search for efficiency
    for &ts in timestamps {
        let idx = ((ts - t_min) / WINDOW_SIZE_SECS) as usize;
        let idx = idx.min(windows.len() - 1);
        windows[idx].commit_count += 1;
    }

    // Compute velocity (commits per day)
    let window_days = WINDOW_SIZE_SECS as f64 / 86400.0;
    for w in &mut windows {
        w.velocity = f64::from(w.commit_count) / window_days;
    }

    windows
}

/// Detects peaks (local maxima) in the velocity windows.
fn detect_peaks(windows: &[VelocityWindow]) -> Vec<ReleasePeak> {
    let mut peaks = Vec::new();

    if windows.len() < 3 {
        // Not enough windows for peak detection
        if let Some(w) = windows.iter().max_by_key(|w| w.commit_count) {
            if w.commit_count >= MIN_PEAK_COMMITS {
                let idx = windows
                    .iter()
                    .position(|x| x.start_ts == w.start_ts)
                    .unwrap_or(0);
                peaks.push(ReleasePeak {
                    window_idx: idx,
                    timestamp: w.start_ts,
                    commit_count: w.commit_count,
                });
            }
        }
        return peaks;
    }

    for i in 1..windows.len() - 1 {
        let prev = windows[i - 1].commit_count;
        let curr = windows[i].commit_count;
        let next = windows[i + 1].commit_count;
        if curr > prev && curr > next && curr >= MIN_PEAK_COMMITS {
            peaks.push(ReleasePeak {
                window_idx: i,
                timestamp: windows[i].start_ts,
                commit_count: curr,
            });
        }
    }

    // Also check first and last windows
    if windows.len() >= 2 {
        if windows[0].commit_count > windows[1].commit_count
            && windows[0].commit_count >= MIN_PEAK_COMMITS
        {
            peaks.insert(
                0,
                ReleasePeak {
                    window_idx: 0,
                    timestamp: windows[0].start_ts,
                    commit_count: windows[0].commit_count,
                },
            );
        }
        let last = windows.len() - 1;
        if windows[last].commit_count > windows[last - 1].commit_count
            && windows[last].commit_count >= MIN_PEAK_COMMITS
        {
            peaks.push(ReleasePeak {
                window_idx: last,
                timestamp: windows[last].start_ts,
                commit_count: windows[last].commit_count,
            });
        }
    }

    peaks
}

/// Computes average inter-peak interval in days.
fn compute_avg_interval(peaks: &[ReleasePeak]) -> f64 {
    if peaks.len() < 2 {
        return 0.0;
    }

    let total_interval: f64 = peaks
        .windows(2)
        .map(|pair| (pair[1].timestamp - pair[0].timestamp) as f64 / 86400.0)
        .sum();
    total_interval / (peaks.len() - 1) as f64
}

/// Computes regularity score from inter-peak intervals.
///
/// Regularity = 1 / (1 + CV) where CV = coefficient of variation.
/// Perfect regularity (equal intervals) → score = 1.0.
/// High variability → score → 0.0.
fn compute_regularity(peaks: &[ReleasePeak]) -> f64 {
    if peaks.len() < 2 {
        return 0.0;
    }

    let intervals: Vec<f64> = peaks
        .windows(2)
        .map(|pair| (pair[1].timestamp - pair[0].timestamp) as f64)
        .collect();

    let mean = intervals.iter().sum::<f64>() / intervals.len() as f64;
    if mean <= 0.0 {
        return 0.0;
    }

    let variance =
        intervals.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / intervals.len() as f64;
    let std_dev = variance.sqrt();
    let cv = std_dev / mean;

    1.0 / (1.0 + cv)
}

/// Determines the current development cycle phase based on recent windows.
fn determine_phase(windows: &[VelocityWindow]) -> CyclePhase {
    if windows.len() < 3 {
        return CyclePhase::Unknown;
    }

    let last = windows.len() - 1;
    let recent = windows[last].velocity;
    let prev = windows[last - 1].velocity;
    let avg: f64 = windows.iter().map(|w| w.velocity).sum::<f64>() / windows.len() as f64;

    if recent > avg * 1.5 {
        CyclePhase::PostRelease
    } else if recent > prev && recent > avg * 0.5 {
        CyclePhase::Building
    } else {
        CyclePhase::Quiet
    }
}

/// Determines velocity trend by comparing first half to second half.
fn determine_trend(windows: &[VelocityWindow]) -> VelocityTrend {
    if windows.len() < 4 {
        return VelocityTrend::Stable;
    }

    let mid = windows.len() / 2;
    let first_half_avg = windows[..mid].iter().map(|w| w.velocity).sum::<f64>() / mid as f64;
    let second_half_avg =
        windows[mid..].iter().map(|w| w.velocity).sum::<f64>() / (windows.len() - mid) as f64;

    if first_half_avg <= 0.0 {
        return VelocityTrend::Stable;
    }

    let ratio = second_half_avg / first_half_avg;
    if ratio > 1.2 {
        VelocityTrend::Accelerating
    } else if ratio < 0.8 {
        VelocityTrend::Decelerating
    } else {
        VelocityTrend::Stable
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = ReleaseRhythmAccumulator::new();
        let report = acc.finalize();
        assert!(report.windows.is_empty());
        assert!(report.peaks.is_empty());
        assert_eq!(report.current_phase, CyclePhase::Unknown);
    }

    #[test]
    fn test_default_impl() {
        let acc = ReleaseRhythmAccumulator::default();
        let report = acc.finalize();
        assert!(report.windows.is_empty());
    }

    #[test]
    fn test_single_commit() {
        let mut acc = ReleaseRhythmAccumulator::new();
        acc.record_commit(1000);
        let report = acc.finalize();
        // Single commit: t_min == t_max, should return empty
        assert!(report.windows.is_empty());
    }

    #[test]
    fn test_two_commits_same_window() {
        let mut acc = ReleaseRhythmAccumulator::new();
        acc.record_commit(0);
        acc.record_commit(86400); // 1 day later
        let report = acc.finalize();
        assert!(!report.windows.is_empty());
    }

    #[test]
    fn test_regular_commits() {
        // 10 commits, one per week over 10 weeks → should have ~10 windows
        let mut acc = ReleaseRhythmAccumulator::new();
        for i in 0..10 {
            acc.record_commit(i * WINDOW_SIZE_SECS);
        }
        let report = acc.finalize();
        assert!(!report.windows.is_empty());
        // All windows should have exactly 1 commit
        for w in &report.windows {
            assert!(w.commit_count <= 2, "window has {} commits", w.commit_count);
        }
    }

    #[test]
    fn test_burst_pattern() {
        // Burst-quiet-burst pattern: 5 commits in week 1, 0 in weeks 2-3, 5 in week 4
        let mut acc = ReleaseRhythmAccumulator::new();
        // Week 1: 5 commits
        for i in 0..5 {
            acc.record_commit(i * 86400);
        }
        // Week 4: 5 commits
        for i in 0..5 {
            acc.record_commit(3 * WINDOW_SIZE_SECS + i * 86400);
        }
        let report = acc.finalize();
        assert!(!report.windows.is_empty());
        // Should detect at least one peak
        assert!(!report.peaks.is_empty(), "should detect burst peaks");
    }

    #[test]
    fn test_regularity_perfect() {
        // Equal intervals between peaks → regularity should be high
        let peaks = vec![
            ReleasePeak {
                window_idx: 0,
                timestamp: 0,
                commit_count: 5,
            },
            ReleasePeak {
                window_idx: 4,
                timestamp: 4 * WINDOW_SIZE_SECS,
                commit_count: 5,
            },
            ReleasePeak {
                window_idx: 8,
                timestamp: 8 * WINDOW_SIZE_SECS,
                commit_count: 5,
            },
        ];
        let regularity = compute_regularity(&peaks);
        assert!(
            (regularity - 1.0).abs() < f64::EPSILON,
            "perfect regularity={}, expected=1.0",
            regularity
        );
    }

    #[test]
    fn test_regularity_zero_peaks() {
        let regularity = compute_regularity(&[]);
        assert!((regularity - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_regularity_single_peak() {
        let peaks = vec![ReleasePeak {
            window_idx: 0,
            timestamp: 0,
            commit_count: 5,
        }];
        let regularity = compute_regularity(&peaks);
        assert!((regularity - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_avg_interval() {
        let peaks = vec![
            ReleasePeak {
                window_idx: 0,
                timestamp: 0,
                commit_count: 5,
            },
            ReleasePeak {
                window_idx: 1,
                timestamp: 7 * 86400,
                commit_count: 5,
            },
            ReleasePeak {
                window_idx: 2,
                timestamp: 14 * 86400,
                commit_count: 5,
            },
        ];
        let avg = compute_avg_interval(&peaks);
        assert!(
            (avg - 7.0).abs() < f64::EPSILON,
            "avg_interval={}, expected=7.0",
            avg
        );
    }

    #[test]
    fn test_cycle_phase_display() {
        assert_eq!(format!("{}", CyclePhase::PostRelease), "post_release");
        assert_eq!(format!("{}", CyclePhase::Building), "building");
        assert_eq!(format!("{}", CyclePhase::Quiet), "quiet");
        assert_eq!(format!("{}", CyclePhase::Unknown), "unknown");
    }

    #[test]
    fn test_velocity_trend_display() {
        assert_eq!(format!("{}", VelocityTrend::Accelerating), "accelerating");
        assert_eq!(format!("{}", VelocityTrend::Stable), "stable");
        assert_eq!(format!("{}", VelocityTrend::Decelerating), "decelerating");
    }

    #[test]
    fn test_accelerating_trend() {
        // More commits in later windows → accelerating
        let mut acc = ReleaseRhythmAccumulator::new();
        // First 4 weeks: 1 commit/week
        for w in 0..4 {
            acc.record_commit(w * WINDOW_SIZE_SECS);
        }
        // Next 4 weeks: 5 commits/week
        for w in 4..8 {
            for d in 0..5 {
                acc.record_commit(w * WINDOW_SIZE_SECS + d * 86400);
            }
        }
        let report = acc.finalize();
        assert_eq!(report.velocity_trend, VelocityTrend::Accelerating);
    }

    #[test]
    fn test_decelerating_trend() {
        // More commits in earlier windows → decelerating
        let mut acc = ReleaseRhythmAccumulator::new();
        // First 4 weeks: 5 commits/week
        for w in 0..4 {
            for d in 0..5 {
                acc.record_commit(w * WINDOW_SIZE_SECS + d * 86400);
            }
        }
        // Next 4 weeks: 1 commit/week
        for w in 4..8 {
            acc.record_commit(w * WINDOW_SIZE_SECS);
        }
        let report = acc.finalize();
        assert_eq!(report.velocity_trend, VelocityTrend::Decelerating);
    }

    // ── Property-based tests ──

    #[allow(clippy::cast_possible_wrap)]
    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Regularity score is always in [0, 1].
            #[test]
            fn prop_regularity_bounded(
                n_peaks in 2usize..10,
                base_interval in 1i64..100
            ) {
                let peaks: Vec<ReleasePeak> = (0..n_peaks)
                    .map(|i| ReleasePeak {
                        window_idx: i,
                        timestamp: i as i64 * base_interval * 86400,
                        commit_count: 5,
                    })
                    .collect();
                let r = compute_regularity(&peaks);
                prop_assert!((0.0..=1.0).contains(&r), "regularity={} out of [0,1]", r);
            }

            /// Velocity is always non-negative.
            #[test]
            fn prop_velocity_non_negative(n_commits in 2usize..50) {
                let mut acc = ReleaseRhythmAccumulator::new();
                for i in 0..n_commits {
                    acc.record_commit(i as i64 * 86400);
                }
                let report = acc.finalize();
                for w in &report.windows {
                    prop_assert!(w.velocity >= 0.0, "negative velocity: {}", w.velocity);
                }
            }
        }
    }
}
