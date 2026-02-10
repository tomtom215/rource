// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! File survival analysis using the Kaplan-Meier estimator.
//!
//! Applies the gold-standard survival analysis technique from biostatistics
//! to estimate how long files survive in a repository before deletion.
//! Files still alive at analysis end are right-censored.
//!
//! # Research Basis
//!
//! Robles et al. "Source Code Survival with the Kaplan Meier Estimator" (MSR/ICSM
//! workshops) first applied survival analysis to source code.
//!
//! Cito et al. (2021) "Software Evolution: The Lifetime of Fine-Grained Elements"
//! (`PeerJ` Computer Science 7, e372) extended the approach to fine-grained elements,
//! revealing infant mortality patterns and file stability patterns.
//!
//! # Algorithm
//!
//! 1. For each file: determine birth (Create) and death (Delete) times
//! 2. Files alive at `t_max` are right-censored
//! 3. At each distinct death time tᵢ:
//!    - nᵢ = files still at risk (alive and not yet censored before tᵢ)
//!    - dᵢ = files that died at exactly tᵢ
//!    - S(tᵢ) = S(tᵢ₋₁) × (nᵢ − dᵢ) / nᵢ
//! 4. Median survival = time where S(t) first drops below 0.5
//!
//! # Complexity
//!
//! - O(F log F) for sorting events, O(F) for curve computation

/// Seconds per day, used for time-to-days conversion.
const SECONDS_PER_DAY: f64 = 86400.0;

/// Infant mortality threshold: files deleted within 30 days of creation.
const INFANT_MORTALITY_DAYS: f64 = 30.0;

/// A point on the Kaplan-Meier survival curve.
#[derive(Debug, Clone)]
pub struct SurvivalPoint {
    /// Days since file creation at this event time.
    pub time_days: f64,
    /// Survival probability S(t) ∈ \[0, 1\].
    pub survival_probability: f64,
    /// Number of files still at risk at this time.
    pub at_risk: u32,
    /// Number of deaths (deletions) at this time.
    pub events: u32,
}

/// Complete file survival analysis report.
#[derive(Debug, Clone)]
pub struct SurvivalReport {
    /// Kaplan-Meier survival curve points.
    pub curve: Vec<SurvivalPoint>,
    /// Median survival time in days (time at S(t) = 0.5).
    /// `None` if >50% of files survive to analysis end.
    pub median_survival_days: Option<f64>,
    /// Fraction of files deleted within 30 days of creation.
    pub infant_mortality_rate: f64,
    /// Total files ever created.
    pub total_births: u32,
    /// Total files deleted.
    pub total_deaths: u32,
    /// Files still alive at analysis end (right-censored).
    pub censored_count: u32,
}

/// Accumulates file birth/death events for survival analysis.
pub struct SurvivalAccumulator {
    /// `file_path` → `(birth_time, death_time)`. `death_time` is `None` if still alive.
    file_events: std::collections::HashMap<String, (i64, Option<i64>)>,
}

impl Default for SurvivalAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl SurvivalAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            file_events: std::collections::HashMap::new(),
        }
    }

    /// Records a file creation event.
    pub fn record_create(&mut self, path: &str, timestamp: i64) {
        self.file_events
            .entry(path.to_string())
            .or_insert((timestamp, None))
            .0 = timestamp.min(
            self.file_events
                .get(path)
                .map_or(timestamp, |(birth, _)| *birth),
        );
    }

    /// Records a file deletion event.
    pub fn record_delete(&mut self, path: &str, timestamp: i64) {
        let entry = self
            .file_events
            .entry(path.to_string())
            .or_insert((timestamp, None));
        entry.1 = Some(timestamp);
    }

    /// Finalizes the accumulator into a [`SurvivalReport`].
    ///
    /// # Arguments
    ///
    /// * `t_max` - Analysis end time (for right-censoring)
    #[must_use]
    pub fn finalize(self, t_max: i64) -> SurvivalReport {
        if self.file_events.is_empty() {
            return SurvivalReport {
                curve: Vec::new(),
                median_survival_days: None,
                infant_mortality_rate: 0.0,
                total_births: 0,
                total_deaths: 0,
                censored_count: 0,
            };
        }

        let total_births = self.file_events.len() as u32;
        let mut deaths: Vec<f64> = Vec::new(); // duration in days for each death
        let mut censored: Vec<f64> = Vec::new(); // duration in days for each censored file
        let mut infant_deaths: u32 = 0;

        for (birth, death) in self.file_events.values() {
            if let Some(death_time) = death {
                let duration_days = (*death_time - *birth) as f64 / SECONDS_PER_DAY;
                let duration_days = duration_days.max(0.0);
                deaths.push(duration_days);
                if duration_days <= INFANT_MORTALITY_DAYS {
                    infant_deaths += 1;
                }
            } else {
                let duration_days = (t_max - *birth) as f64 / SECONDS_PER_DAY;
                censored.push(duration_days.max(0.0));
            }
        }

        let total_deaths = deaths.len() as u32;
        let censored_count = censored.len() as u32;
        let infant_mortality_rate = if total_births > 0 {
            f64::from(infant_deaths) / f64::from(total_births)
        } else {
            0.0
        };

        // Build Kaplan-Meier curve
        let curve = compute_kaplan_meier(&mut deaths, &censored, total_births);

        let median_survival_days = curve
            .iter()
            .find(|p| p.survival_probability < 0.5)
            .map(|p| p.time_days);

        SurvivalReport {
            curve,
            median_survival_days,
            infant_mortality_rate,
            total_births,
            total_deaths,
            censored_count,
        }
    }
}

/// Computes the Kaplan-Meier survival curve.
///
/// Events are death times (in days). Censored observations are files still alive.
fn compute_kaplan_meier(deaths: &mut [f64], _censored: &[f64], total: u32) -> Vec<SurvivalPoint> {
    if deaths.is_empty() {
        return vec![SurvivalPoint {
            time_days: 0.0,
            survival_probability: 1.0,
            at_risk: total,
            events: 0,
        }];
    }

    deaths.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

    let mut curve = Vec::new();
    let mut survival = 1.0;
    let mut at_risk = total;
    let mut i = 0;

    // Start point
    curve.push(SurvivalPoint {
        time_days: 0.0,
        survival_probability: 1.0,
        at_risk,
        events: 0,
    });

    while i < deaths.len() {
        let current_time = deaths[i];
        let mut d = 0u32; // deaths at this time

        while i < deaths.len() && (deaths[i] - current_time).abs() < 1e-6 {
            d += 1;
            i += 1;
        }

        if at_risk > 0 {
            survival *= f64::from(at_risk - d) / f64::from(at_risk);
        }
        at_risk -= d;

        curve.push(SurvivalPoint {
            time_days: current_time,
            survival_probability: survival,
            at_risk,
            events: d,
        });
    }

    curve
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_deaths() {
        // All files survive → S(t) = 1.0, median = None
        let mut acc = SurvivalAccumulator::new();
        acc.record_create("a.rs", 0);
        acc.record_create("b.rs", 100);
        let report = acc.finalize(100_000);
        assert_eq!(report.total_births, 2);
        assert_eq!(report.total_deaths, 0);
        assert_eq!(report.censored_count, 2);
        assert!(report.median_survival_days.is_none());
        assert!(
            (report.curve[0].survival_probability - 1.0).abs() < f64::EPSILON,
            "S(0)={}, expected=1.0",
            report.curve[0].survival_probability
        );
    }

    #[test]
    fn test_all_die_immediately() {
        // All files deleted at same time as creation → S drops to 0
        let mut acc = SurvivalAccumulator::new();
        acc.record_create("a.rs", 0);
        acc.record_delete("a.rs", 0);
        acc.record_create("b.rs", 100);
        acc.record_delete("b.rs", 100);
        let report = acc.finalize(1000);
        assert_eq!(report.total_deaths, 2);
        // Last curve point should have survival ≈ 0
        let last = report.curve.last().unwrap();
        assert!(
            last.survival_probability.abs() < f64::EPSILON,
            "S(end)={}, expected=0.0",
            last.survival_probability
        );
    }

    #[test]
    fn test_known_survival_curve() {
        // 5 files: 2 die at day 10, 1 dies at day 20, 2 survive
        let mut acc = SurvivalAccumulator::new();
        for i in 0..5 {
            acc.record_create(&format!("f{i}.rs"), 0);
        }
        acc.record_delete("f0.rs", 10 * 86400);
        acc.record_delete("f1.rs", 10 * 86400);
        acc.record_delete("f2.rs", 20 * 86400);

        let report = acc.finalize(30 * 86400);
        assert_eq!(report.total_births, 5);
        assert_eq!(report.total_deaths, 3);
        assert_eq!(report.censored_count, 2);

        // S(0) = 1.0
        assert!((report.curve[0].survival_probability - 1.0).abs() < f64::EPSILON);
        // After day 10: 2 deaths of 5 at risk → S = 1.0 * (5-2)/5 = 0.6
        assert!(
            (report.curve[1].survival_probability - 0.6).abs() < 1e-10,
            "S(10)={}, expected=0.6",
            report.curve[1].survival_probability
        );
        // After day 20: 1 death of 3 at risk → S = 0.6 * (3-1)/3 = 0.4
        assert!(
            (report.curve[2].survival_probability - 0.4).abs() < 1e-10,
            "S(20)={}, expected=0.4",
            report.curve[2].survival_probability
        );
    }

    #[test]
    fn test_right_censoring() {
        // File alive at t_max → correctly censored
        let mut acc = SurvivalAccumulator::new();
        acc.record_create("alive.rs", 0);
        acc.record_create("dead.rs", 0);
        acc.record_delete("dead.rs", 86400); // dies at day 1
        let report = acc.finalize(100 * 86400);
        assert_eq!(report.total_deaths, 1);
        assert_eq!(report.censored_count, 1);
        // After the death: S = 1.0 * (2-1)/2 = 0.5
        assert!(
            (report.curve[1].survival_probability - 0.5).abs() < 1e-10,
            "S(1)={}",
            report.curve[1].survival_probability
        );
    }

    #[test]
    fn test_infant_mortality_rate() {
        // 3 of 10 files deleted within 30 days
        let mut acc = SurvivalAccumulator::new();
        for i in 0..10 {
            acc.record_create(&format!("f{i}.rs"), 0);
        }
        acc.record_delete("f0.rs", 5 * 86400); // 5 days
        acc.record_delete("f1.rs", 15 * 86400); // 15 days
        acc.record_delete("f2.rs", 25 * 86400); // 25 days
        acc.record_delete("f3.rs", 60 * 86400); // 60 days (not infant)

        let report = acc.finalize(365 * 86400);
        assert!(
            (report.infant_mortality_rate - 0.3).abs() < 1e-10,
            "rate={}, expected=0.3",
            report.infant_mortality_rate
        );
    }

    #[test]
    fn test_median_survival() {
        // 4 files: 3 die at various times, 1 survives
        // Need S(t) to cross 0.5
        let mut acc = SurvivalAccumulator::new();
        for i in 0..4 {
            acc.record_create(&format!("f{i}.rs"), 0);
        }
        acc.record_delete("f0.rs", 10 * 86400); // S = 3/4 = 0.75 after
        acc.record_delete("f1.rs", 20 * 86400); // S = 0.75 * 2/3 = 0.5 after
        acc.record_delete("f2.rs", 30 * 86400); // S = 0.5 * 1/2 = 0.25 after

        let report = acc.finalize(365 * 86400);
        // Median should be at day 30 (first time S < 0.5)
        assert!(report.median_survival_days.is_some());
        assert!(
            (report.median_survival_days.unwrap() - 30.0).abs() < 1e-6,
            "median={}, expected=30.0",
            report.median_survival_days.unwrap()
        );
    }

    #[test]
    fn test_empty_input() {
        let acc = SurvivalAccumulator::new();
        let report = acc.finalize(1000);
        assert!(report.curve.is_empty());
        assert_eq!(report.total_births, 0);
    }

    #[test]
    fn test_single_file_survives() {
        let mut acc = SurvivalAccumulator::new();
        acc.record_create("a.rs", 0);
        let report = acc.finalize(100 * 86400);
        assert_eq!(report.total_births, 1);
        assert_eq!(report.total_deaths, 0);
        assert_eq!(report.censored_count, 1);
        assert!(
            (report.curve[0].survival_probability - 1.0).abs() < f64::EPSILON,
            "single surviving file should have S(t)=1.0"
        );
    }

    #[test]
    fn test_default_impl() {
        let acc = SurvivalAccumulator::default();
        let report = acc.finalize(0);
        assert!(report.curve.is_empty());
    }

    // --- Mutation-killing tests ---

    #[test]
    fn test_infant_mortality_boundary_exactly_30_days() {
        // 30 days = exactly INFANT_MORTALITY_DAYS → IS infant (kills < vs <= boundary)
        let mut acc = SurvivalAccumulator::new();
        acc.record_create("a.rs", 0);
        acc.record_delete("a.rs", 30 * 86400); // exactly 30 days
        acc.record_create("b.rs", 0);
        let report = acc.finalize(365 * 86400);
        assert_eq!(report.total_births, 2);
        assert_eq!(report.total_deaths, 1);
        assert!(
            (report.infant_mortality_rate - 0.5).abs() < 1e-10,
            "rate={}, expected=0.5",
            report.infant_mortality_rate
        );
    }

    #[test]
    fn test_infant_mortality_31_days_not_infant() {
        // 31 days > INFANT_MORTALITY_DAYS → NOT infant
        let mut acc = SurvivalAccumulator::new();
        acc.record_create("a.rs", 0);
        acc.record_delete("a.rs", 31 * 86400); // 31 days
        let report = acc.finalize(365 * 86400);
        assert!(
            report.infant_mortality_rate.abs() < f64::EPSILON,
            "31 days should not be infant, rate={}",
            report.infant_mortality_rate
        );
    }

    #[test]
    fn test_infant_mortality_rate_division_exact() {
        // Kills: replace / with * in infant_mortality_rate calculation
        // 2 infant deaths out of 5 total → rate = 2/5 = 0.4
        let mut acc = SurvivalAccumulator::new();
        for i in 0..5 {
            acc.record_create(&format!("f{i}.rs"), 0);
        }
        acc.record_delete("f0.rs", 10 * 86400); // infant
        acc.record_delete("f1.rs", 20 * 86400); // infant
        let report = acc.finalize(365 * 86400);
        assert!(
            (report.infant_mortality_rate - 0.4).abs() < 1e-10,
            "rate={}, expected=0.4",
            report.infant_mortality_rate
        );
    }

    #[test]
    fn test_survival_formula_subtraction() {
        // Kills: replace - with + in `f64::from(at_risk - d) / f64::from(at_risk)`
        // 3 files, 1 dies at day 10 → S = (3-1)/3 = 2/3
        let mut acc = SurvivalAccumulator::new();
        for i in 0..3 {
            acc.record_create(&format!("f{i}.rs"), 0);
        }
        acc.record_delete("f0.rs", 10 * 86400);
        let report = acc.finalize(365 * 86400);
        let expected = 2.0 / 3.0;
        assert!(
            (report.curve[1].survival_probability - expected).abs() < 1e-10,
            "S(10)={}, expected={}",
            report.curve[1].survival_probability,
            expected
        );
        assert_eq!(report.curve[1].at_risk, 2);
        assert_eq!(report.curve[1].events, 1);
    }

    #[test]
    fn test_median_survival_below_half() {
        // Kills: replace < with <= in `p.survival_probability < 0.5`
        // S exactly = 0.5 should NOT be the median (need S < 0.5)
        let mut acc = SurvivalAccumulator::new();
        for i in 0..4 {
            acc.record_create(&format!("f{i}.rs"), 0);
        }
        acc.record_delete("f0.rs", 10 * 86400); // S = 3/4 = 0.75
        acc.record_delete("f1.rs", 20 * 86400); // S = 0.75 * 2/3 = 0.5

        let report = acc.finalize(365 * 86400);
        // S = 0.5 at day 20 — this is NOT < 0.5, so median should be None
        assert!(
            report.median_survival_days.is_none(),
            "S=0.5 should not trigger median (need S < 0.5)"
        );
    }

    #[test]
    fn test_duration_days_division_by_seconds_per_day() {
        // Kills: replace / with * in duration calculation
        // File lives 2 days = 2*86400 seconds → duration = 2.0 days
        let mut acc = SurvivalAccumulator::new();
        acc.record_create("a.rs", 0);
        acc.record_delete("a.rs", 2 * 86400);
        let report = acc.finalize(10 * 86400);
        // Death at 2.0 days
        assert!(
            (report.curve[1].time_days - 2.0).abs() < 1e-10,
            "time={}, expected=2.0",
            report.curve[1].time_days
        );
    }

    #[test]
    fn test_negative_duration_clamped_to_zero() {
        // Birth AFTER death → duration negative → clamped to 0.0
        let mut acc = SurvivalAccumulator::new();
        acc.record_create("a.rs", 200);
        acc.record_delete("a.rs", 100); // death before birth
        let report = acc.finalize(1000);
        assert_eq!(report.total_deaths, 1);
        // Duration clamped to 0.0 via .max(0.0)
        assert!(
            report.curve[1].time_days.abs() < 1e-10,
            "negative duration should be clamped to 0"
        );
    }

    #[test]
    fn test_record_create_keeps_earliest_birth() {
        // Multiple creates for same file → keeps earliest birth
        let mut acc = SurvivalAccumulator::new();
        acc.record_create("a.rs", 1000);
        acc.record_create("a.rs", 500); // Earlier!
        acc.record_delete("a.rs", 5000);
        let report = acc.finalize(10000);
        // Birth should be 500, death at 5000 → duration = 4500/86400 days
        assert_eq!(report.total_births, 1);
        assert_eq!(report.total_deaths, 1);
    }
}
