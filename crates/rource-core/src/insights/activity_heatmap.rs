// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Commit Activity Heatmap — day-of-week × hour-of-day distribution of commits.
//!
//! Provides a GitHub-style contribution heatmap showing when development
//! activity occurs. This complements the circadian risk analysis with a
//! more granular temporal view.
//!
//! # Research Basis
//!
//! - Eyolfson et al. (2011) "Do Time of Day and Developer Experience Affect
//!   Commit Bugginess?" (MSR) — temporal patterns in commit activity
//! - Claes et al. (2018) "Do Programmers Work at Night or During the
//!   Weekend?" (ICSE) — work pattern analysis from VCS timestamps
//!
//! # Algorithm
//!
//! 1. Convert each commit timestamp to day-of-week (0=Mon..6=Sun) and
//!    hour-of-day (0..23) using UTC.
//! 2. Build a 7×24 matrix of commit counts.
//! 3. Identify peak activity periods and compute distribution metrics.
//!
//! # Complexity
//!
//! - O(C) single pass where C = total commits

/// Commit activity heatmap report.
#[derive(Debug, Clone)]
pub struct ActivityHeatmapReport {
    /// 7×24 matrix: `grid[day][hour]` = commit count.
    /// Days: 0=Monday, 1=Tuesday, ..., 6=Sunday.
    /// Hours: 0..23 in UTC.
    pub grid: [[u32; 24]; 7],
    /// Total commits in the heatmap.
    pub total_commits: usize,
    /// Peak day-of-week (0=Mon..6=Sun).
    pub peak_day: u8,
    /// Peak hour-of-day (0..23 UTC).
    pub peak_hour: u8,
    /// Peak cell commit count.
    pub peak_count: u32,
    /// Commits during working hours (Mon-Fri, 9-17 UTC).
    pub work_hours_pct: f64,
    /// Commits during weekends (Sat-Sun).
    pub weekend_pct: f64,
}

/// Accumulates commit timestamps for heatmap generation.
pub struct ActivityHeatmapAccumulator {
    grid: [[u32; 24]; 7],
    total: usize,
}

impl Default for ActivityHeatmapAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl ActivityHeatmapAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            grid: [[0; 24]; 7],
            total: 0,
        }
    }

    /// Records a commit timestamp (Unix epoch seconds, UTC).
    pub fn record_commit(&mut self, timestamp: i64) {
        // Convert Unix timestamp to day-of-week and hour-of-day.
        // Using a simple calculation: Unix epoch (1970-01-01) was a Thursday (day 3).
        let (day, hour) = timestamp_to_day_hour(timestamp);
        if day < 7 && hour < 24 {
            self.grid[day as usize][hour as usize] += 1;
            self.total += 1;
        }
    }

    /// Finalizes the heatmap report.
    #[must_use]
    pub fn finalize(self) -> ActivityHeatmapReport {
        if self.total == 0 {
            return ActivityHeatmapReport {
                grid: [[0; 24]; 7],
                total_commits: 0,
                peak_day: 0,
                peak_hour: 0,
                peak_count: 0,
                work_hours_pct: 0.0,
                weekend_pct: 0.0,
            };
        }

        // Find peak cell
        let mut peak_day: u8 = 0;
        let mut peak_hour: u8 = 0;
        let mut peak_count: u32 = 0;

        let mut work_hours: u32 = 0;
        let mut weekend: u32 = 0;

        for (d, day_row) in self.grid.iter().enumerate() {
            for (h, &count) in day_row.iter().enumerate() {
                if count > peak_count {
                    peak_count = count;
                    peak_day = d as u8;
                    peak_hour = h as u8;
                }

                // Mon-Fri (0-4), 9:00-17:00
                if d < 5 && (9..17).contains(&h) {
                    work_hours += count;
                }

                // Sat-Sun (5-6)
                if d >= 5 {
                    weekend += count;
                }
            }
        }

        let total_f64 = self.total as f64;
        ActivityHeatmapReport {
            grid: self.grid,
            total_commits: self.total,
            peak_day,
            peak_hour,
            peak_count,
            work_hours_pct: f64::from(work_hours) / total_f64 * 100.0,
            weekend_pct: f64::from(weekend) / total_f64 * 100.0,
        }
    }
}

/// Converts a Unix timestamp to (`day_of_week`, `hour_of_day`) in UTC.
/// Day: 0=Monday, 1=Tuesday, ..., 6=Sunday.
/// Hour: 0..23.
fn timestamp_to_day_hour(timestamp: i64) -> (u8, u8) {
    // Seconds per day
    const SECS_PER_DAY: i64 = 86400;
    const SECS_PER_HOUR: i64 = 3600;

    // Handle negative timestamps (before epoch)
    let day_offset = timestamp.div_euclid(SECS_PER_DAY);
    let time_of_day = timestamp.rem_euclid(SECS_PER_DAY);

    // Unix epoch (1970-01-01) was a Thursday.
    // Thursday = 3 in our 0=Mon system.
    // day_of_week = (day_offset + 3) mod 7
    let dow = ((day_offset % 7) + 7 + 3) % 7;
    let hour = time_of_day / SECS_PER_HOUR;

    (dow as u8, hour as u8)
}

/// Day name for display.
const DAY_NAMES: [&str; 7] = [
    "Monday",
    "Tuesday",
    "Wednesday",
    "Thursday",
    "Friday",
    "Saturday",
    "Sunday",
];

/// Returns the day name for a day index (0=Monday..6=Sunday).
#[must_use]
pub fn day_name(day: u8) -> &'static str {
    DAY_NAMES.get(day as usize).copied().unwrap_or("Unknown")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let acc = ActivityHeatmapAccumulator::new();
        let report = acc.finalize();
        assert_eq!(report.total_commits, 0);
        assert_eq!(report.peak_count, 0);
    }

    #[test]
    fn test_default_impl() {
        let acc = ActivityHeatmapAccumulator::default();
        let report = acc.finalize();
        assert_eq!(report.total_commits, 0);
    }

    #[test]
    fn test_epoch_is_thursday() {
        // 1970-01-01 00:00:00 UTC = Thursday
        let (day, hour) = timestamp_to_day_hour(0);
        assert_eq!(day, 3, "epoch should be Thursday (3)");
        assert_eq!(hour, 0);
    }

    #[test]
    fn test_known_timestamp() {
        // 2024-01-01 12:00:00 UTC = Monday
        // timestamp = 1704110400
        let (day, hour) = timestamp_to_day_hour(1_704_110_400);
        assert_eq!(day, 0, "2024-01-01 should be Monday (0)");
        assert_eq!(hour, 12);
    }

    #[test]
    fn test_heatmap_counts() {
        let mut acc = ActivityHeatmapAccumulator::new();
        // Record 5 commits at same time
        for _ in 0..5 {
            acc.record_commit(1_704_110_400); // Monday 12:00
        }
        let report = acc.finalize();
        assert_eq!(report.total_commits, 5);
        assert_eq!(report.peak_day, 0); // Monday
        assert_eq!(report.peak_hour, 12);
        assert_eq!(report.peak_count, 5);
    }

    #[test]
    fn test_work_hours_pct() {
        let mut acc = ActivityHeatmapAccumulator::new();
        // All commits during work hours: Monday 10:00 UTC
        // Monday 10:00 = epoch + 4 days + 10 hours = 4*86400 + 10*3600 = 381600
        let monday_10am = 4 * 86400 + 10 * 3600; // 1970-01-05 Monday 10:00 UTC
        for _ in 0..10 {
            acc.record_commit(monday_10am);
        }
        let report = acc.finalize();
        assert!(
            (report.work_hours_pct - 100.0).abs() < 0.01,
            "all commits during work hours: {}",
            report.work_hours_pct
        );
    }

    #[test]
    fn test_weekend_pct() {
        let mut acc = ActivityHeatmapAccumulator::new();
        // Saturday = epoch + 2 days (1970-01-03 is Saturday)
        let saturday = 2 * 86400 + 14 * 3600; // Saturday 14:00
        for _ in 0..10 {
            acc.record_commit(saturday);
        }
        let report = acc.finalize();
        assert!(
            (report.weekend_pct - 100.0).abs() < 0.01,
            "all commits on weekend: {}",
            report.weekend_pct
        );
    }

    #[test]
    fn test_day_name() {
        assert_eq!(day_name(0), "Monday");
        assert_eq!(day_name(6), "Sunday");
        assert_eq!(day_name(7), "Unknown");
    }

    #[test]
    fn test_grid_sums_to_total() {
        let mut acc = ActivityHeatmapAccumulator::new();
        for i in 0..100 {
            acc.record_commit(i * 3600 * 7); // spread across times
        }
        let report = acc.finalize();
        let grid_total: u32 = report.grid.iter().flat_map(|row| row.iter()).sum();
        assert_eq!(
            grid_total as usize, report.total_commits,
            "grid sum should equal total commits"
        );
    }
}
