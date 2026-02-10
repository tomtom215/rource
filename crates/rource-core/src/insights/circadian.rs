// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Circadian (time-of-day) risk pattern analysis.
//!
//! Assigns risk scores to commits based on hour-of-day and day-of-week,
//! aggregating per-file and per-author risk profiles to surface temporal
//! patterns correlated with defect introduction.
//!
//! # Research Basis
//!
//! Eyolfson, Tan & Lam (2011) "Do Time of Day and Developer Experience Affect
//! Commit Bugginess?" (MSR 2011, pp. 153–162) validated on the Linux kernel
//! (180K+ commits), `PostgreSQL` (30K+ commits), and Xorg server. Commits between
//! midnight–4 AM are significantly buggier. Results were replicated in the 2014
//! journal extension (Empirical Software Engineering 19(4), pp. 1009–1039).
//!
//! # Known Limitation: UTC-Only Timestamps
//!
//! All timestamps in `CommitRecord` are Unix epoch (UTC). We do NOT have
//! per-author timezone information. For internationally distributed teams,
//! the hour-of-day extraction reflects UTC, not the developer's local time.
//! This means:
//! - A developer in UTC+9 (Tokyo) committing at their 10 AM local time appears
//!   as 01:00 UTC, which is scored as "high risk" despite being a normal work hour.
//! - The risk model is most accurate for teams concentrated in similar timezones
//!   or for repos where commit timestamps include timezone offsets (which we
//!   cannot currently distinguish from UTC timestamps).
//!
//! Despite this limitation, the aggregate patterns (e.g., "X% of commits at
//! high-risk UTC hours") still provide useful signals about when the repository
//! receives changes during potentially fatigued hours for SOME contributors.
//!
//! # Algorithm
//!
//! For each commit:
//! 1. Extract hour-of-day and day-of-week from UTC timestamp
//! 2. Look up risk weight from `HOUR_RISK` and `WEEKEND_MULTIPLIER`
//! 3. Accumulate weighted risk per file, per author, and per hour bucket
//!
//! # Complexity
//!
//! - Accumulation: O(N) where N = total file changes
//! - Finalization: O(F log F + A log A) for sorting files/authors by risk

use rustc_hash::FxHashMap;

/// Risk weight per UTC hour (0–23), derived from Eyolfson et al. (2011).
///
/// Higher values indicate hours correlated with buggier commits:
/// - 00:00–03:59 → 1.0 (peak buggy period)
/// - 04:00–06:59 → 0.7 (elevated)
/// - 07:00–11:59 → 0.2 (lowest risk — normal work hours)
/// - 12:00–17:59 → 0.4 (moderate)
/// - 18:00–23:59 → 0.6 (elevated — evening/fatigue)
const HOUR_RISK: [f64; 24] = [
    // 00-03: High risk
    1.0, 1.0, 1.0, 1.0, // 04-06: Elevated
    0.7, 0.7, 0.7, // 07-11: Low risk (normal work hours)
    0.2, 0.2, 0.2, 0.2, 0.2, // 12-17: Moderate
    0.4, 0.4, 0.4, 0.4, 0.4, 0.4, // 18-23: Elevated
    0.6, 0.6, 0.6, 0.6, 0.6, 0.6,
];

/// Weekend commits are slightly riskier (Eyolfson 2011).
const WEEKEND_MULTIPLIER: f64 = 1.3;

/// Hours 0–3 are classified as the "high risk" window.
const HIGH_RISK_HOUR_END: u8 = 4;

/// Per-file circadian risk profile.
#[derive(Debug, Clone)]
pub struct CircadianFileRisk {
    /// File path.
    pub path: String,
    /// Sum of risk scores from all commits touching this file.
    pub total_risk: f64,
    /// Number of commits in the 00:00–03:59 UTC window.
    pub high_risk_commits: u32,
    /// Total commits touching this file.
    pub total_commits: u32,
    /// Fraction of commits in the high-risk window.
    pub high_risk_fraction: f64,
}

/// Per-author circadian risk profile.
#[derive(Debug, Clone)]
pub struct CircadianAuthorRisk {
    /// Author name.
    pub author: String,
    /// Average risk score across all commits by this author.
    pub avg_risk: f64,
    /// Number of commits in the 00:00–03:59 UTC window.
    pub high_risk_commits: u32,
    /// Total commits by this author.
    pub total_commits: u32,
    /// Most common commit hour (0–23, UTC).
    pub preferred_hour: u8,
}

/// Complete circadian risk report.
#[derive(Debug, Clone)]
pub struct CircadianReport {
    /// Files sorted by `total_risk` descending.
    pub files: Vec<CircadianFileRisk>,
    /// Authors sorted by `avg_risk` descending.
    pub authors: Vec<CircadianAuthorRisk>,
    /// Static risk weight per hour (copy of `HOUR_RISK` for consumer reference).
    pub hourly_risk: [f64; 24],
    /// Percentage of all commits that fall in the high-risk window (0–3 UTC).
    pub high_risk_percentage: f64,
    /// Total commits analyzed.
    pub total_commits_analyzed: u32,
}

/// Internal per-file state during accumulation.
struct FileRiskState {
    risk_sum: f64,
    high_risk_count: u32,
    total_count: u32,
}

/// Accumulates circadian risk data from commit stream.
pub struct CircadianAccumulator {
    /// Per-file risk state.
    file_state: FxHashMap<String, FileRiskState>,
    /// Per-author: Vec of (hour, risk) per commit.
    author_risks: FxHashMap<String, Vec<(u8, f64)>>,
    /// Commit count per hour bucket.
    hourly_counts: [u32; 24],
    /// Total commits processed.
    total_commits: u32,
}

impl Default for CircadianAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl CircadianAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            file_state: FxHashMap::default(),
            author_risks: FxHashMap::default(),
            hourly_counts: [0; 24],
            total_commits: 0,
        }
    }

    /// Records a commit's circadian risk for all touched files.
    ///
    /// Extracts hour-of-day and day-of-week from the UTC timestamp, computes
    /// the risk weight, and updates per-file and per-author state.
    pub fn record_commit(&mut self, author: &str, timestamp: i64, file_paths: &[&str]) {
        let hour = extract_hour(timestamp);
        let dow = extract_day_of_week(timestamp);
        let risk = compute_risk(hour, dow);

        self.total_commits += 1;
        self.hourly_counts[hour as usize] += 1;
        let is_high_risk = hour < HIGH_RISK_HOUR_END;

        self.author_risks
            .entry(author.to_string())
            .or_default()
            .push((hour, risk));

        for path in file_paths {
            let state = self
                .file_state
                .entry((*path).to_string())
                .or_insert(FileRiskState {
                    risk_sum: 0.0,
                    high_risk_count: 0,
                    total_count: 0,
                });
            state.risk_sum += risk;
            state.total_count += 1;
            if is_high_risk {
                state.high_risk_count += 1;
            }
        }
    }

    /// Finalizes the accumulator into a [`CircadianReport`].
    #[must_use]
    pub fn finalize(self) -> CircadianReport {
        let mut files: Vec<CircadianFileRisk> = self
            .file_state
            .into_iter()
            .map(|(path, state)| {
                let high_risk_fraction = if state.total_count > 0 {
                    f64::from(state.high_risk_count) / f64::from(state.total_count)
                } else {
                    0.0
                };
                CircadianFileRisk {
                    path,
                    total_risk: state.risk_sum,
                    high_risk_commits: state.high_risk_count,
                    total_commits: state.total_count,
                    high_risk_fraction,
                }
            })
            .collect();
        files.sort_by(|a, b| {
            b.total_risk
                .partial_cmp(&a.total_risk)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        let mut authors: Vec<CircadianAuthorRisk> = self
            .author_risks
            .into_iter()
            .map(|(author, risks)| {
                let total_commits = risks.len() as u32;
                let avg_risk = if total_commits > 0 {
                    risks.iter().map(|(_, r)| r).sum::<f64>() / f64::from(total_commits)
                } else {
                    0.0
                };
                let high_risk_commits = risks
                    .iter()
                    .filter(|(h, _)| *h < HIGH_RISK_HOUR_END)
                    .count() as u32;

                // Find preferred hour (mode)
                let mut hour_counts = [0u32; 24];
                for (h, _) in &risks {
                    hour_counts[*h as usize] += 1;
                }
                let preferred_hour = hour_counts
                    .iter()
                    .enumerate()
                    .max_by_key(|(_, &c)| c)
                    .map_or(0, |(h, _)| h as u8);

                CircadianAuthorRisk {
                    author,
                    avg_risk,
                    high_risk_commits,
                    total_commits,
                    preferred_hour,
                }
            })
            .collect();
        authors.sort_by(|a, b| {
            b.avg_risk
                .partial_cmp(&a.avg_risk)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        let high_risk_count: u32 = self.hourly_counts[..HIGH_RISK_HOUR_END as usize]
            .iter()
            .sum();
        let high_risk_percentage = if self.total_commits > 0 {
            f64::from(high_risk_count) / f64::from(self.total_commits) * 100.0
        } else {
            0.0
        };

        CircadianReport {
            files,
            authors,
            hourly_risk: HOUR_RISK,
            high_risk_percentage,
            total_commits_analyzed: self.total_commits,
        }
    }
}

/// Extracts UTC hour (0–23) from a Unix timestamp.
///
/// Handles negative timestamps (pre-1970) by adding 86400 before modulo.
fn extract_hour(timestamp: i64) -> u8 {
    let seconds_in_day = timestamp.rem_euclid(86400);
    (seconds_in_day / 3600) as u8
}

/// Extracts day-of-week (0=Monday, 6=Sunday) from a Unix timestamp.
///
/// Unix epoch (1970-01-01) was a Thursday (index 3 in Mon=0 convention).
fn extract_day_of_week(timestamp: i64) -> u8 {
    let days = if timestamp >= 0 {
        timestamp / 86400
    } else {
        // For negative timestamps, round toward negative infinity
        (timestamp - 86399) / 86400
    };
    (((days % 7) + 7 + 3) % 7) as u8
}

/// Computes the risk score for a given hour and day-of-week.
fn compute_risk(hour: u8, dow: u8) -> f64 {
    let hour_risk = HOUR_RISK[hour as usize];
    let dow_multiplier = if dow >= 5 { WEEKEND_MULTIPLIER } else { 1.0 };
    hour_risk * dow_multiplier
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = CircadianAccumulator::new();
        let report = acc.finalize();
        assert!(report.files.is_empty());
        assert!(report.authors.is_empty());
        assert_eq!(report.total_commits_analyzed, 0);
        assert!((report.high_risk_percentage - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_midnight_commit_high_risk() {
        // 02:00 UTC on a weekday (Thursday = epoch day)
        // timestamp = 2*3600 = 7200 (Thursday Jan 1, 1970, 02:00 UTC)
        let mut acc = CircadianAccumulator::new();
        acc.record_commit("Alice", 7200, &["a.rs"]);
        let report = acc.finalize();
        assert_eq!(report.files.len(), 1);
        // Hour 2 → HOUR_RISK[2] = 1.0, Thursday (weekday) → multiplier = 1.0
        // risk = 1.0 * 1.0 = 1.0
        assert!(
            (report.files[0].total_risk - 1.0).abs() < f64::EPSILON,
            "risk={}, expected=1.0",
            report.files[0].total_risk
        );
        assert_eq!(report.files[0].high_risk_commits, 1);
    }

    #[test]
    fn test_morning_commit_low_risk() {
        // 09:00 UTC on a weekday
        // timestamp = 9*3600 = 32400 (Thursday Jan 1, 1970)
        let mut acc = CircadianAccumulator::new();
        acc.record_commit("Alice", 32400, &["a.rs"]);
        let report = acc.finalize();
        // Hour 9 → HOUR_RISK[9] = 0.2, weekday → multiplier = 1.0
        assert!(
            (report.files[0].total_risk - 0.2).abs() < f64::EPSILON,
            "risk={}, expected=0.2",
            report.files[0].total_risk
        );
        assert_eq!(report.files[0].high_risk_commits, 0);
    }

    #[test]
    fn test_weekend_multiplier() {
        // Saturday: epoch + 2 days = Saturday Jan 3, 1970 at 09:00 UTC
        let saturday_9am = 2 * 86400 + 9 * 3600;
        // Verify it's Saturday (dow=5)
        assert_eq!(extract_day_of_week(saturday_9am), 5);

        let mut acc = CircadianAccumulator::new();
        acc.record_commit("Alice", saturday_9am, &["a.rs"]);
        let report = acc.finalize();
        // Hour 9 → HOUR_RISK[9] = 0.2, Saturday → multiplier = 1.3
        let expected = 0.2 * WEEKEND_MULTIPLIER;
        assert!(
            (report.files[0].total_risk - expected).abs() < 1e-10,
            "risk={}, expected={}",
            report.files[0].total_risk,
            expected
        );
    }

    #[test]
    fn test_file_risk_accumulation() {
        // File touched by 3 commits at different hours
        let mut acc = CircadianAccumulator::new();
        acc.record_commit("Alice", 2 * 3600, &["a.rs"]); // hour 2, risk 1.0
        acc.record_commit("Bob", 9 * 3600, &["a.rs"]); // hour 9, risk 0.2
        acc.record_commit("Carol", 14 * 3600, &["a.rs"]); // hour 14, risk 0.4
        let report = acc.finalize();
        let expected = 1.0 + 0.2 + 0.4;
        assert!(
            (report.files[0].total_risk - expected).abs() < 1e-10,
            "risk={}, expected={}",
            report.files[0].total_risk,
            expected
        );
        assert_eq!(report.files[0].total_commits, 3);
    }

    #[test]
    fn test_author_avg_risk() {
        let mut acc = CircadianAccumulator::new();
        // Alice: commits at hour 2 (risk 1.0) and hour 9 (risk 0.2)
        acc.record_commit("Alice", 2 * 3600, &["a.rs"]);
        acc.record_commit("Alice", 9 * 3600, &["b.rs"]);
        let report = acc.finalize();
        let alice = report.authors.iter().find(|a| a.author == "Alice").unwrap();
        let expected_avg = (1.0 + 0.2) / 2.0;
        assert!(
            (alice.avg_risk - expected_avg).abs() < 1e-10,
            "avg_risk={}, expected={}",
            alice.avg_risk,
            expected_avg
        );
    }

    #[test]
    fn test_preferred_hour() {
        let mut acc = CircadianAccumulator::new();
        // Alice: 5 commits at hour 14, 2 at hour 22
        for i in 0..5 {
            acc.record_commit("Alice", 14 * 3600 + i * 86400, &["a.rs"]);
        }
        for i in 0..2 {
            acc.record_commit("Alice", 22 * 3600 + (i + 10) * 86400, &["b.rs"]);
        }
        let report = acc.finalize();
        let alice = report.authors.iter().find(|a| a.author == "Alice").unwrap();
        assert_eq!(
            alice.preferred_hour, 14,
            "preferred={}, expected=14",
            alice.preferred_hour
        );
    }

    #[test]
    fn test_high_risk_percentage() {
        let mut acc = CircadianAccumulator::new();
        // 2 commits at high-risk hours, 3 at low-risk
        acc.record_commit("Alice", 3600, &["a.rs"]); // hour 1 → high risk
        acc.record_commit("Alice", 3 * 3600, &["a.rs"]); // hour 3 → high risk
        acc.record_commit("Alice", 9 * 3600, &["a.rs"]); // hour 9 → low risk
        acc.record_commit("Alice", 10 * 3600, &["a.rs"]); // hour 10 → low risk
        acc.record_commit("Alice", 14 * 3600, &["a.rs"]); // hour 14 → moderate
        let report = acc.finalize();
        // 2/5 = 40%
        assert!(
            (report.high_risk_percentage - 40.0).abs() < 1e-10,
            "high_risk_pct={}, expected=40.0",
            report.high_risk_percentage
        );
    }

    #[test]
    fn test_negative_timestamp() {
        // Pre-1970 timestamp: -3600 = 1969-12-31 23:00 UTC
        let hour = extract_hour(-3600);
        assert_eq!(hour, 23, "hour={}, expected=23", hour);
    }

    #[test]
    fn test_hourly_risk_array() {
        // Verify exact HOUR_RISK constant values
        assert!((HOUR_RISK[0] - 1.0).abs() < f64::EPSILON);
        assert!((HOUR_RISK[3] - 1.0).abs() < f64::EPSILON);
        assert!((HOUR_RISK[4] - 0.7).abs() < f64::EPSILON);
        assert!((HOUR_RISK[7] - 0.2).abs() < f64::EPSILON);
        assert!((HOUR_RISK[12] - 0.4).abs() < f64::EPSILON);
        assert!((HOUR_RISK[18] - 0.6).abs() < f64::EPSILON);
    }

    #[test]
    fn test_day_of_week_extraction() {
        // Epoch (1970-01-01) was Thursday (dow=3)
        assert_eq!(extract_day_of_week(0), 3);
        // Friday = epoch + 1 day
        assert_eq!(extract_day_of_week(86400), 4);
        // Saturday = epoch + 2 days
        assert_eq!(extract_day_of_week(2 * 86400), 5);
        // Sunday = epoch + 3 days
        assert_eq!(extract_day_of_week(3 * 86400), 6);
        // Monday = epoch + 4 days
        assert_eq!(extract_day_of_week(4 * 86400), 0);
    }

    #[test]
    fn test_default_impl() {
        let acc = CircadianAccumulator::default();
        let report = acc.finalize();
        assert_eq!(report.total_commits_analyzed, 0);
    }

    // --- Mutation-killing tests ---

    #[test]
    fn test_high_risk_hour_end_boundary() {
        // Hour 3 is high risk (< 4), hour 4 is NOT high risk (4 is not < 4)
        // Kills: replace < with <= in `hour < HIGH_RISK_HOUR_END`
        let mut acc = CircadianAccumulator::new();
        // Hour 3: high risk
        acc.record_commit("Alice", 3 * 3600, &["a.rs"]);
        // Hour 4: NOT high risk
        acc.record_commit("Alice", 4 * 3600, &["b.rs"]);
        let report = acc.finalize();
        let a = report.files.iter().find(|f| f.path == "a.rs").unwrap();
        let b = report.files.iter().find(|f| f.path == "b.rs").unwrap();
        assert_eq!(a.high_risk_commits, 1, "hour 3 should be high risk");
        assert_eq!(b.high_risk_commits, 0, "hour 4 should NOT be high risk");
    }

    #[test]
    fn test_high_risk_fraction_division_exact() {
        // Kills: replace / with * in high_risk_fraction computation
        // 1 high-risk commit out of 4 total → fraction = 0.25
        let mut acc = CircadianAccumulator::new();
        acc.record_commit("Alice", 2 * 3600, &["a.rs"]); // hour 2 → high risk
        acc.record_commit("Bob", 9 * 3600, &["a.rs"]); // hour 9 → low
        acc.record_commit("Carol", 10 * 3600, &["a.rs"]); // hour 10 → low
        acc.record_commit("Dave", 14 * 3600, &["a.rs"]); // hour 14 → moderate
        let report = acc.finalize();
        assert!(
            (report.files[0].high_risk_fraction - 0.25).abs() < 1e-10,
            "fraction={}, expected=0.25",
            report.files[0].high_risk_fraction
        );
    }

    #[test]
    fn test_avg_risk_division_exact() {
        // Kills: replace / with * in avg_risk calculation
        // Alice: hour 2 (1.0) + hour 9 (0.2) → avg = 1.2/2 = 0.6
        let mut acc = CircadianAccumulator::new();
        acc.record_commit("Alice", 2 * 3600, &["a.rs"]);
        acc.record_commit("Alice", 9 * 3600, &["b.rs"]);
        let report = acc.finalize();
        let alice = report.authors.iter().find(|a| a.author == "Alice").unwrap();
        assert!(
            (alice.avg_risk - 0.6).abs() < 1e-10,
            "avg_risk={}, expected=0.6",
            alice.avg_risk
        );
    }

    #[test]
    fn test_weekend_dow_boundary() {
        // dow=4 (Friday) → weekday, dow=5 (Saturday) → weekend
        // Kills: replace >= with > in `dow >= 5`
        let friday = 86400; // epoch + 1 day = Friday
        let saturday = 2 * 86400; // epoch + 2 days = Saturday
        assert_eq!(extract_day_of_week(friday), 4);
        assert_eq!(extract_day_of_week(saturday), 5);

        let risk_friday = compute_risk(9, 4);
        let risk_saturday = compute_risk(9, 5);
        assert!(
            (risk_friday - 0.2).abs() < f64::EPSILON,
            "Friday hour 9 → 0.2"
        );
        assert!(
            (risk_saturday - 0.2 * WEEKEND_MULTIPLIER).abs() < 1e-10,
            "Saturday hour 9 → 0.2*1.3"
        );
    }

    #[test]
    fn test_high_risk_percentage_division() {
        // Kills: replace / with * and * with / in percentage calculation
        // 1 high-risk commit out of 5 total → 20%
        let mut acc = CircadianAccumulator::new();
        acc.record_commit("A", 3600, &["a.rs"]); // hour 1 → high
        acc.record_commit("A", 9 * 3600, &["a.rs"]); // hour 9 → low
        acc.record_commit("A", 10 * 3600, &["a.rs"]); // hour 10 → low
        acc.record_commit("A", 14 * 3600, &["a.rs"]); // hour 14 → mod
        acc.record_commit("A", 18 * 3600, &["a.rs"]); // hour 18 → elevated
        let report = acc.finalize();
        assert!(
            (report.high_risk_percentage - 20.0).abs() < 1e-10,
            "pct={}, expected=20.0",
            report.high_risk_percentage
        );
    }

    #[test]
    fn test_extract_hour_division() {
        // Kills: replace / with * in `seconds_in_day / 3600`
        // 2:30 AM = 2*3600 + 30*60 = 9000 seconds → hour = 9000/3600 = 2
        assert_eq!(extract_hour(9000), 2);
        // 23:59 = 23*3600 + 59*60 = 86340 → hour = 23
        assert_eq!(extract_hour(86340), 23);
    }

    #[test]
    fn test_timestamp_zero_is_thursday() {
        // Kills arithmetic mutants in extract_day_of_week
        // Epoch = Thursday (3). If +3 mutated to -3 or similar, wrong day.
        assert_eq!(extract_day_of_week(0), 3); // Thursday
        assert_eq!(extract_day_of_week(7 * 86400), 3); // Next Thursday
    }

    #[test]
    fn test_risk_multiplication() {
        // Kills: replace * with + in `hour_risk * dow_multiplier`
        // Weekend midnight: 1.0 * 1.3 = 1.3 (not 1.0 + 1.3 = 2.3)
        let risk = compute_risk(0, 5); // hour 0, Saturday
        assert!((risk - 1.3).abs() < 1e-10, "risk={}, expected=1.3", risk);
    }

    // ── Property-based tests ────────────────────────────────────────

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// extract_hour always returns a value in [0, 23].
            #[test]
            fn prop_hour_bounded(ts in proptest::num::i64::ANY) {
                let hour = extract_hour(ts);
                prop_assert!(hour <= 23, "hour={} > 23 for ts={}", hour, ts);
            }

            /// extract_day_of_week always returns a value in [0, 6].
            #[test]
            fn prop_dow_bounded(ts in proptest::num::i64::ANY) {
                let dow = extract_day_of_week(ts);
                prop_assert!(dow <= 6, "dow={} > 6 for ts={}", dow, ts);
            }

            /// Timestamps exactly 7 days apart have the same day of week.
            #[test]
            fn prop_dow_weekly_period(ts in -1_000_000_000i64..1_000_000_000i64) {
                let dow1 = extract_day_of_week(ts);
                let dow2 = extract_day_of_week(ts + 7 * 86400);
                prop_assert_eq!(dow1, dow2, "dow should be periodic with period 7 days");
            }

            /// Timestamps exactly 24 hours apart have the same hour.
            #[test]
            fn prop_hour_daily_period(ts in -1_000_000_000i64..1_000_000_000i64) {
                let h1 = extract_hour(ts);
                let h2 = extract_hour(ts + 86400);
                prop_assert_eq!(h1, h2, "hour should be periodic with period 24 hours");
            }

            /// compute_risk is always non-negative.
            #[test]
            fn prop_risk_non_negative(hour in 0u8..24, dow in 0u8..7) {
                let risk = compute_risk(hour, dow);
                prop_assert!(risk >= 0.0, "risk={} < 0 for hour={}, dow={}", risk, hour, dow);
            }

            /// Weekend risk is always >= weekday risk for the same hour.
            #[test]
            fn prop_weekend_risk_geq_weekday(hour in 0u8..24) {
                let weekday_risk = compute_risk(hour, 0); // Monday
                let weekend_risk = compute_risk(hour, 5); // Saturday
                prop_assert!(
                    weekend_risk >= weekday_risk - f64::EPSILON,
                    "weekend risk {} < weekday risk {} for hour {}",
                    weekend_risk, weekday_risk, hour
                );
            }

            /// High-risk percentage is always in [0, 100].
            #[test]
            fn prop_high_risk_pct_bounded(n_commits in 1usize..20) {
                let mut acc = CircadianAccumulator::new();
                for i in 0..n_commits {
                    // Distribute commits across various hours
                    let hour_offset = i64::try_from(i % 24).unwrap() * 3600;
                    acc.record_commit("Alice", hour_offset, &["a.rs"]);
                }
                let report = acc.finalize();
                prop_assert!(
                    report.high_risk_percentage >= 0.0,
                    "pct={} < 0",
                    report.high_risk_percentage
                );
                prop_assert!(
                    report.high_risk_percentage <= 100.0,
                    "pct={} > 100",
                    report.high_risk_percentage
                );
            }
        }
    }
}
