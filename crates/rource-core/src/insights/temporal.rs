// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Temporal pattern analysis.
//!
//! Analyzes when development activity occurs (time of day, day of week)
//! and detects change bursts — clusters of high-frequency commits.
//!
//! # Research Basis
//!
//! - Eyolfson et al. (2011) found that commits made late at night or in
//!   the early morning are more likely to contain bugs.
//! - Nagappan et al. (2008) showed that change bursts have higher predictive
//!   power for defect-prone components than complexity metrics.
//!
//! # Burst Detection Algorithm
//!
//! Uses a sliding window approach:
//! 1. Sort commits by timestamp
//! 2. Slide a window of `BURST_WINDOW_SECONDS` across the timeline
//! 3. When the commit count in the window exceeds `BURST_THRESHOLD`,
//!    record a burst event
//! 4. Merge overlapping bursts

/// Sliding window size for burst detection (in seconds).
/// 3600 seconds = 1 hour.
const BURST_WINDOW_SECONDS: i64 = 3600;

/// Minimum commits within the window to qualify as a burst.
const BURST_THRESHOLD: usize = 10;

/// Complete temporal analysis report.
#[derive(Debug, Clone)]
pub struct TemporalReport {
    /// Activity heatmap: 7 days × 24 hours.
    /// Index: `[day_of_week][hour]` where day 0 = Monday.
    /// Value: number of commits in that slot.
    pub activity_heatmap: [[u32; 24]; 7],

    /// Detected change bursts.
    pub bursts: Vec<ChangeBurst>,

    /// Peak activity hour (0-23).
    pub peak_hour: u8,

    /// Peak activity day (0=Monday, 6=Sunday).
    pub peak_day: u8,

    /// Total commits per day of week.
    pub commits_per_day: [u32; 7],

    /// Total commits per hour.
    pub commits_per_hour: [u32; 24],

    /// Average files changed per commit during bursts vs non-bursts.
    pub avg_files_in_bursts: f64,
    /// Average files changed per commit outside bursts.
    pub avg_files_outside_bursts: f64,
}

impl TemporalReport {
    /// Creates an empty report (for zero-commit repositories).
    #[must_use]
    pub fn empty() -> Self {
        Self {
            activity_heatmap: [[0; 24]; 7],
            bursts: Vec::new(),
            peak_hour: 0,
            peak_day: 0,
            commits_per_day: [0; 7],
            commits_per_hour: [0; 24],
            avg_files_in_bursts: 0.0,
            avg_files_outside_bursts: 0.0,
        }
    }
}

/// A detected burst of change activity.
#[derive(Debug, Clone)]
pub struct ChangeBurst {
    /// Start timestamp (Unix seconds).
    pub start: i64,
    /// End timestamp (Unix seconds).
    pub end: i64,
    /// Number of commits in this burst.
    pub commit_count: usize,
    /// Total files changed during this burst.
    pub total_files: usize,
    /// Duration in seconds.
    pub duration_seconds: i64,
}

/// Accumulates temporal data during commit processing.
pub struct TemporalAccumulator {
    /// Commit timestamps and file counts for burst detection.
    commit_events: Vec<(i64, usize)>,
    /// Activity heatmap accumulator.
    heatmap: [[u32; 24]; 7],
}

impl Default for TemporalAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl TemporalAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            commit_events: Vec::new(),
            heatmap: [[0; 24]; 7],
        }
    }

    /// Records a commit for temporal analysis.
    ///
    /// # Arguments
    ///
    /// * `timestamp` - Unix epoch seconds
    /// * `file_count` - Number of files changed in this commit
    pub fn record_commit(&mut self, timestamp: i64, file_count: usize) {
        self.commit_events.push((timestamp, file_count));

        // Compute day-of-week and hour from Unix timestamp
        // Unix epoch (1970-01-01) was a Thursday (day 3 in Mon=0 system)
        let (day, hour) = day_hour_from_timestamp(timestamp);
        let day_idx = day as usize % 7;
        let hour_idx = hour as usize % 24;
        self.heatmap[day_idx][hour_idx] += 1;
    }

    /// Finalizes the accumulator into a [`TemporalReport`].
    #[must_use]
    pub fn finalize(self) -> TemporalReport {
        // Compute per-day and per-hour totals
        let mut commits_per_day = [0u32; 7];
        let mut commits_per_hour = [0u32; 24];
        for (day, day_row) in self.heatmap.iter().enumerate() {
            for (hour, &count) in day_row.iter().enumerate() {
                commits_per_day[day] += count;
                commits_per_hour[hour] += count;
            }
        }

        // Find peaks
        let peak_day = commits_per_day
            .iter()
            .enumerate()
            .max_by_key(|(_, &v)| v)
            .map_or(0, |(i, _)| i as u8);

        let peak_hour = commits_per_hour
            .iter()
            .enumerate()
            .max_by_key(|(_, &v)| v)
            .map_or(0, |(i, _)| i as u8);

        // Detect bursts
        let bursts = detect_bursts(&self.commit_events);

        // Compute average files per commit in/out of bursts
        let (avg_in, avg_out) = compute_burst_file_averages(&self.commit_events, &bursts);

        TemporalReport {
            activity_heatmap: self.heatmap,
            bursts,
            peak_hour,
            peak_day,
            commits_per_day,
            commits_per_hour,
            avg_files_in_bursts: avg_in,
            avg_files_outside_bursts: avg_out,
        }
    }
}

/// Converts a Unix timestamp to (`day_of_week`, `hour`).
///
/// Day of week: 0 = Monday, 6 = Sunday.
/// This uses integer arithmetic only (no floating point).
fn day_hour_from_timestamp(timestamp: i64) -> (u8, u8) {
    // Seconds per day
    const SECS_PER_DAY: i64 = 86400;
    const SECS_PER_HOUR: i64 = 3600;

    // Days since epoch (1970-01-01 was Thursday)
    // Use Euclidean division to handle negative timestamps (pre-1970)
    let day_number = timestamp.div_euclid(SECS_PER_DAY);
    // Thursday = 3 in Mon=0 system
    let day_of_week = ((day_number + 3) % 7) as u8;

    let seconds_in_day = timestamp.rem_euclid(SECS_PER_DAY);
    let hour = (seconds_in_day / SECS_PER_HOUR) as u8;

    (day_of_week, hour)
}

/// Detects change bursts using a sliding window.
fn detect_bursts(events: &[(i64, usize)]) -> Vec<ChangeBurst> {
    if events.is_empty() {
        return Vec::new();
    }

    // Sort by timestamp
    let mut sorted: Vec<(i64, usize)> = events.to_vec();
    sorted.sort_by_key(|e| e.0);

    let mut bursts = Vec::new();
    let mut window_start = 0;

    for window_end in 0..sorted.len() {
        // Advance window start to maintain window size
        while sorted[window_end].0 - sorted[window_start].0 > BURST_WINDOW_SECONDS {
            window_start += 1;
        }

        let count = window_end - window_start + 1;
        if count >= BURST_THRESHOLD {
            let total_files: usize = sorted[window_start..=window_end].iter().map(|e| e.1).sum();
            let burst = ChangeBurst {
                start: sorted[window_start].0,
                end: sorted[window_end].0,
                commit_count: count,
                total_files,
                duration_seconds: sorted[window_end].0 - sorted[window_start].0,
            };

            // Merge with previous burst if overlapping
            if let Some(last) = bursts.last_mut() {
                let last_burst: &mut ChangeBurst = last;
                if burst.start <= last_burst.end + BURST_WINDOW_SECONDS {
                    // Extend existing burst
                    last_burst.end = burst.end;
                    last_burst.commit_count = last_burst.commit_count.max(burst.commit_count);
                    last_burst.total_files = last_burst.total_files.max(burst.total_files);
                    last_burst.duration_seconds = last_burst.end - last_burst.start;
                    continue;
                }
            }
            bursts.push(burst);
        }
    }

    bursts
}

/// Computes average files per commit during and outside bursts.
fn compute_burst_file_averages(events: &[(i64, usize)], bursts: &[ChangeBurst]) -> (f64, f64) {
    if events.is_empty() {
        return (0.0, 0.0);
    }

    let mut in_burst_files = 0usize;
    let mut in_burst_count = 0usize;
    let mut out_burst_files = 0usize;
    let mut out_burst_count = 0usize;

    for &(ts, files) in events {
        let is_in_burst = bursts.iter().any(|b| ts >= b.start && ts <= b.end);
        if is_in_burst {
            in_burst_files += files;
            in_burst_count += 1;
        } else {
            out_burst_files += files;
            out_burst_count += 1;
        }
    }

    let avg_in = if in_burst_count > 0 {
        in_burst_files as f64 / in_burst_count as f64
    } else {
        0.0
    };
    let avg_out = if out_burst_count > 0 {
        out_burst_files as f64 / out_burst_count as f64
    } else {
        0.0
    };

    (avg_in, avg_out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_day_hour_from_timestamp() {
        // 2024-01-01 00:00:00 UTC (Monday)
        // Unix timestamp: 1704067200
        let (day, hour) = day_hour_from_timestamp(1_704_067_200);
        assert_eq!(day, 0, "2024-01-01 should be Monday (0)");
        assert_eq!(hour, 0, "midnight should be hour 0");
    }

    #[test]
    fn test_day_hour_epoch() {
        // 1970-01-01 00:00:00 (Thursday)
        let (day, hour) = day_hour_from_timestamp(0);
        assert_eq!(day, 3, "epoch should be Thursday (3)");
        assert_eq!(hour, 0);
    }

    #[test]
    fn test_day_hour_afternoon() {
        // 1970-01-01 15:00:00 (Thursday, 3pm)
        let (day, hour) = day_hour_from_timestamp(15 * 3600);
        assert_eq!(day, 3);
        assert_eq!(hour, 15);
    }

    #[test]
    fn test_empty_temporal() {
        let acc = TemporalAccumulator::new();
        let report = acc.finalize();
        assert!(report.bursts.is_empty());
        assert_eq!(report.commits_per_day, [0; 7]);
        assert_eq!(report.commits_per_hour, [0; 24]);
    }

    #[test]
    fn test_heatmap_accumulation() {
        let mut acc = TemporalAccumulator::new();
        // Record 3 commits at the epoch (Thursday midnight)
        acc.record_commit(0, 1);
        acc.record_commit(1, 2);
        acc.record_commit(2, 3);
        let report = acc.finalize();

        // Thursday (3) at hour 0
        assert_eq!(report.activity_heatmap[3][0], 3);
        assert_eq!(report.peak_day, 3);
        assert_eq!(report.peak_hour, 0);
    }

    #[test]
    fn test_burst_detection() {
        let mut acc = TemporalAccumulator::new();
        // 15 commits within 1 hour — should trigger burst
        for i in 0..15 {
            acc.record_commit(1000 + i * 60, 2); // 1 commit per minute
        }
        // Isolated commit far away
        acc.record_commit(100_000, 1);

        let report = acc.finalize();
        assert!(
            !report.bursts.is_empty(),
            "should detect at least one burst"
        );
        assert_eq!(report.bursts[0].commit_count, 15);
    }

    #[test]
    fn test_no_burst_below_threshold() {
        let mut acc = TemporalAccumulator::new();
        // Only 5 commits in an hour — below threshold of 10
        for i in 0..5 {
            acc.record_commit(1000 + i * 60, 1);
        }
        let report = acc.finalize();
        assert!(report.bursts.is_empty());
    }

    #[test]
    fn test_burst_file_averages() {
        let events: Vec<(i64, usize)> = (0..15).map(|i| (1000 + i * 60, 3)).collect();
        let bursts = detect_bursts(&events);
        let (avg_in, avg_out) = compute_burst_file_averages(&events, &bursts);

        // All commits are in the burst, avg = 3.0
        assert!((avg_in - 3.0).abs() < 0.01);
        // No commits outside burst
        assert!((avg_out - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_negative_timestamp() {
        // Pre-1970 timestamp should not panic
        let (day, hour) = day_hour_from_timestamp(-86400);
        // -86400 = 1969-12-31, which was a Wednesday (2)
        assert_eq!(day, 2);
        assert_eq!(hour, 0);
    }

    #[test]
    fn test_peak_computation() {
        let mut acc = TemporalAccumulator::new();
        // Most commits on a specific day/hour
        // Friday at 14:00 (epoch + 1 day + 14 hours = Thursday→Friday)
        let friday_2pm = 86400 + 14 * 3600; // Friday 14:00
        for i in 0..10 {
            acc.record_commit(friday_2pm + i, 1);
        }
        // One commit on Monday
        let monday_9am = 4 * 86400 + 9 * 3600; // Monday 9:00
        acc.record_commit(monday_9am, 1);

        let report = acc.finalize();
        assert_eq!(report.peak_day, 4, "Friday should be peak day (4)");
        assert_eq!(report.peak_hour, 14, "14:00 should be peak hour");
    }

    #[test]
    fn test_empty_report() {
        let report = TemporalReport::empty();
        assert!(report.bursts.is_empty());
        assert_eq!(report.peak_hour, 0);
        assert_eq!(report.peak_day, 0);
        assert!((report.avg_files_in_bursts - 0.0).abs() < f64::EPSILON);
        assert!((report.avg_files_outside_bursts - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_burst_file_averages_mixed() {
        // Some commits in burst, some outside — verify exact averages
        // 12 commits within 1 hour (burst), then 3 commits outside
        let mut events: Vec<(i64, usize)> = Vec::new();
        // Burst: 12 commits, each touching 4 files
        for i in 0..12 {
            events.push((1000 + i * 60, 4));
        }
        // Outside burst: 3 commits, each touching 2 files
        events.push((100_000, 2));
        events.push((200_000, 2));
        events.push((300_000, 2));

        let bursts = detect_bursts(&events);
        assert!(!bursts.is_empty(), "should detect burst");

        let (avg_in, avg_out) = compute_burst_file_averages(&events, &bursts);
        // In-burst: 12 commits * 4 files / 12 = 4.0
        assert!(
            (avg_in - 4.0).abs() < 1e-10,
            "avg_in={}, expected=4.0",
            avg_in
        );
        // Out-burst: 3 commits * 2 files / 3 = 2.0
        assert!(
            (avg_out - 2.0).abs() < 1e-10,
            "avg_out={}, expected=2.0",
            avg_out
        );
    }

    #[test]
    fn test_commits_per_day_and_hour_summing() {
        // Kills mutants on += in finalize (commits_per_day/commits_per_hour)
        let mut acc = TemporalAccumulator::new();
        // 5 commits at epoch (Thursday midnight)
        for i in 0..5 {
            acc.record_commit(i, 1);
        }
        let report = acc.finalize();

        // All 5 on Thursday (day 3)
        assert_eq!(report.commits_per_day[3], 5);
        assert_eq!(report.commits_per_day.iter().sum::<u32>(), 5);
        // All 5 at hour 0
        assert_eq!(report.commits_per_hour[0], 5);
        assert_eq!(report.commits_per_hour.iter().sum::<u32>(), 5);
    }

    #[test]
    fn test_heatmap_different_slots() {
        let mut acc = TemporalAccumulator::new();
        // Thursday midnight (epoch)
        acc.record_commit(0, 1);
        // Thursday 15:00
        acc.record_commit(15 * 3600, 1);
        // Friday midnight (epoch + 24h)
        acc.record_commit(86400, 1);

        let report = acc.finalize();
        assert_eq!(report.activity_heatmap[3][0], 1, "Thu midnight");
        assert_eq!(report.activity_heatmap[3][15], 1, "Thu 15:00");
        assert_eq!(report.activity_heatmap[4][0], 1, "Fri midnight");
        // Total heatmap count should be 3
        let total: u32 = report.activity_heatmap.iter().flat_map(|r| r.iter()).sum();
        assert_eq!(total, 3);
    }

    #[test]
    fn test_burst_duration_seconds() {
        // Verify burst duration_seconds is end - start
        let mut events: Vec<(i64, usize)> = Vec::new();
        for i in 0..15 {
            events.push((1000 + i * 100, 1)); // 15 commits over 1400 seconds
        }
        let bursts = detect_bursts(&events);
        assert_eq!(bursts.len(), 1);
        assert_eq!(bursts[0].start, 1000);
        assert_eq!(bursts[0].end, 1000 + 14 * 100);
        assert_eq!(
            bursts[0].duration_seconds,
            bursts[0].end - bursts[0].start,
            "duration must be end - start"
        );
    }

    #[test]
    fn test_empty_events_burst_detection() {
        let bursts = detect_bursts(&[]);
        assert!(bursts.is_empty());
        let (avg_in, avg_out) = compute_burst_file_averages(&[], &[]);
        assert!((avg_in - 0.0).abs() < f64::EPSILON);
        assert!((avg_out - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_burst_merge_overlapping() {
        // Two groups of commits that should merge into one burst
        let mut events: Vec<(i64, usize)> = Vec::new();
        // First group: 10 commits at time 0-540 (within 1 hour window)
        for i in 0..10 {
            events.push((i * 60, 1));
        }
        // Second group: 10 commits at time 1800-2340 (within window of first group end + 3600)
        for i in 0..10 {
            events.push((1800 + i * 60, 1));
        }
        let bursts = detect_bursts(&events);
        // Should merge because second burst start (1800) <= first burst end + BURST_WINDOW_SECONDS
        assert_eq!(bursts.len(), 1, "overlapping bursts should merge");
    }

    #[test]
    fn test_burst_no_merge_gap_exceeds_window() {
        // Kills: merge condition (start <= last.end + BURST_WINDOW_SECONDS)
        // Two burst groups separated by more than BURST_WINDOW_SECONDS from last burst end
        let mut events: Vec<(i64, usize)> = Vec::new();
        // First group: 10 commits at time 0-540
        for i in 0..10 {
            events.push((i * 60, 1));
        }
        // Second group starts well beyond first_end + 2*BURST_WINDOW_SECONDS
        // First burst ends around 540, so gap must exceed 540 + 3600 = 4140
        // Place second group at time 10000+ (gap of ~9460 from first burst end)
        for i in 0..10 {
            events.push((10000 + i * 60, 1));
        }
        let bursts = detect_bursts(&events);
        assert_eq!(
            bursts.len(),
            2,
            "bursts separated by large gap should NOT merge"
        );
    }

    #[test]
    fn test_burst_threshold_exactly_10_commits() {
        // Kills: >= vs > in count >= BURST_THRESHOLD check
        // Exactly 10 commits in a 1-hour window should be a burst (threshold = 10)
        let mut events: Vec<(i64, usize)> = Vec::new();
        for i in 0..10 {
            events.push((i * 60, 2));
        }
        let bursts = detect_bursts(&events);
        assert_eq!(bursts.len(), 1, "exactly 10 commits should trigger burst");
        assert_eq!(bursts[0].commit_count, 10);
    }

    #[test]
    fn test_burst_threshold_9_commits_no_burst() {
        // Kills: >= vs > boundary — 9 commits should NOT be a burst
        let mut events: Vec<(i64, usize)> = Vec::new();
        for i in 0..9 {
            events.push((i * 60, 2));
        }
        let bursts = detect_bursts(&events);
        assert!(
            bursts.is_empty(),
            "9 commits should not trigger burst (threshold is 10)"
        );
    }

    #[test]
    fn test_burst_file_count_division_exact() {
        // Kills: replace / with * in avg_files_in_bursts = in_burst_files / in_burst_count
        let mut events: Vec<(i64, usize)> = Vec::new();
        // 10 commits, each touching 5 files
        for i in 0..10 {
            events.push((i * 60, 5));
        }
        // 2 commits outside burst, each touching 3 files
        events.push((100_000, 3));
        events.push((200_000, 3));

        let bursts = detect_bursts(&events);
        assert!(!bursts.is_empty());
        let (avg_in, avg_out) = compute_burst_file_averages(&events, &bursts);

        // In-burst: 10 * 5 / 10 = 5.0
        assert!(
            (avg_in - 5.0).abs() < 1e-10,
            "avg_in={}, expected=5.0",
            avg_in
        );
        // Out-burst: 2 * 3 / 2 = 3.0
        assert!(
            (avg_out - 3.0).abs() < 1e-10,
            "avg_out={}, expected=3.0",
            avg_out
        );
    }

    #[test]
    fn test_peak_hour_detection_exact() {
        // Kills: argmax correctness in peak_hour computation
        let mut acc = TemporalAccumulator::new();
        // 1 commit at hour 10 (epoch + 10h = Thursday 10:00)
        acc.record_commit(10 * 3600, 1);
        // 5 commits at hour 14 (epoch + 14h = Thursday 14:00)
        for i in 0..5 {
            acc.record_commit(14 * 3600 + i, 1);
        }
        // 3 commits at hour 22 (epoch + 22h = Thursday 22:00)
        for i in 0..3 {
            acc.record_commit(22 * 3600 + i, 1);
        }

        let report = acc.finalize();
        assert_eq!(report.peak_hour, 14, "hour 14 has most commits (5)");
        assert_eq!(report.commits_per_hour[14], 5);
        assert_eq!(report.commits_per_hour[10], 1);
        assert_eq!(report.commits_per_hour[22], 3);
    }

    #[test]
    fn test_peak_day_detection_exact() {
        // Kills: argmax correctness in peak_day computation
        let mut acc = TemporalAccumulator::new();
        // Thursday (day 3): epoch + 0 seconds, 2 commits
        acc.record_commit(0, 1);
        acc.record_commit(1, 1);
        // Monday (day 0): epoch + 4 days, 5 commits
        let monday = 4 * 86400;
        for i in 0..5 {
            acc.record_commit(monday + i, 1);
        }

        let report = acc.finalize();
        assert_eq!(report.peak_day, 0, "Monday has most commits (5)");
        assert_eq!(report.commits_per_day[0], 5, "Monday commit count");
        assert_eq!(report.commits_per_day[3], 2, "Thursday commit count");
    }

    #[test]
    fn test_commits_per_day_hour_total_consistency() {
        // Kills: += operator mutations in heatmap summing
        let mut acc = TemporalAccumulator::new();
        let total_commits = 20;
        for i in 0..total_commits {
            acc.record_commit(i * 7200, 1); // every 2 hours
        }

        let report = acc.finalize();
        let day_total: u32 = report.commits_per_day.iter().sum();
        let hour_total: u32 = report.commits_per_hour.iter().sum();
        assert_eq!(
            day_total, total_commits as u32,
            "sum of commits_per_day must equal total"
        );
        assert_eq!(
            hour_total, total_commits as u32,
            "sum of commits_per_hour must equal total"
        );
    }

    #[test]
    fn test_burst_window_boundary_exact() {
        // Kills: > vs >= in window advancement condition
        // sorted[window_end].0 - sorted[window_start].0 > BURST_WINDOW_SECONDS
        // Place 10 commits spanning exactly 3600 seconds (= BURST_WINDOW_SECONDS)
        let mut events: Vec<(i64, usize)> = Vec::new();
        for i in 0..10 {
            events.push((i * 400, 1)); // 10 commits over 3600s exactly
        }
        let bursts = detect_bursts(&events);
        assert_eq!(
            bursts.len(),
            1,
            "10 commits spanning exactly BURST_WINDOW_SECONDS should be a burst"
        );
    }

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Commits per day has exactly 7 bins.
            #[test]
            fn prop_day_bins_count(n_commits in 1usize..20) {
                let mut acc = TemporalAccumulator::new();
                for i in 0..n_commits {
                    acc.record_commit(i64::try_from(i).unwrap() * 86400, 1);
                }
                let report = acc.finalize();
                prop_assert_eq!(report.commits_per_day.len(), 7);
                prop_assert_eq!(report.commits_per_hour.len(), 24);
            }

            /// Sum of commits_per_day equals sum of commits_per_hour (total commits recorded in heatmap).
            #[test]
            fn prop_day_hour_sum_equal(n_commits in 1usize..30) {
                let mut acc = TemporalAccumulator::new();
                for i in 0..n_commits {
                    acc.record_commit(i64::try_from(i).unwrap() * 3600, 1);
                }
                let report = acc.finalize();
                let day_sum: u32 = report.commits_per_day.iter().sum();
                let hour_sum: u32 = report.commits_per_hour.iter().sum();
                prop_assert_eq!(day_sum, hour_sum,
                    "day_sum={} != hour_sum={}", day_sum, hour_sum);
            }

            /// peak_hour is in [0, 23] and peak_day is in [0, 6].
            #[test]
            fn prop_peak_bounded(n_commits in 1usize..20) {
                let mut acc = TemporalAccumulator::new();
                for i in 0..n_commits {
                    acc.record_commit(i64::try_from(i).unwrap() * 7200, 2);
                }
                let report = acc.finalize();
                prop_assert!(report.peak_hour <= 23, "peak_hour={}", report.peak_hour);
                prop_assert!(report.peak_day <= 6, "peak_day={}", report.peak_day);
            }

            /// avg_files_in_bursts and avg_files_outside_bursts are non-negative.
            #[test]
            fn prop_avg_files_non_negative(n_commits in 1usize..30) {
                let mut acc = TemporalAccumulator::new();
                for i in 0..n_commits {
                    acc.record_commit(i64::try_from(i).unwrap() * 60, 3);
                }
                let report = acc.finalize();
                prop_assert!(report.avg_files_in_bursts >= 0.0,
                    "avg_in={} < 0", report.avg_files_in_bursts);
                prop_assert!(report.avg_files_outside_bursts >= 0.0,
                    "avg_out={} < 0", report.avg_files_outside_bursts);
            }
        }
    }
}
