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
    }
}
