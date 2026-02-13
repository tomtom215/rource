// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Team rhythm synchronization via circular statistics on commit timestamps.
//!
//! Measures how synchronized team members' commit patterns are using
//! circular statistics on the hour-of-day distribution of commits.
//!
//! # Interpretation
//!
//! - High sync (> 0.7): team works in cadence — good collaboration but
//!   potential for merge conflicts during peak hours.
//! - Low sync (< 0.3): asynchronous work patterns — lower conflict risk
//!   but potential coordination gaps.
//!
//! # Academic Citations
//!
//! - Eyolfson, Tan & Lam (2011) — Circadian patterns in software development
//! - Cataldo & Herbsleb (2008) — Coordination requirements
//! - Fisher (1993) — "Statistical Analysis of Circular Data" (circular statistics)
//!
//! # Novelty
//!
//! Circular statistics applied to team synchronization measurement from
//! VCS data is not offered by any existing tool. Standard tools compute
//! per-developer time-of-day distributions but do not quantify team-level
//! synchronization using directional statistics (mean resultant length).

use rustc_hash::FxHashMap;

/// Team rhythm synchronization report.
#[derive(Debug)]
pub struct TeamRhythmReport {
    /// Per-developer rhythm profiles.
    pub developers: Vec<DeveloperRhythm>,
    /// Team-level synchronization score [0.0, 1.0].
    /// Based on circular correlation of commit hour distributions.
    pub team_sync_score: f64,
    /// Mean resultant length (R̄) of the team's combined commit hour distribution.
    /// Higher = more concentrated around a single peak hour.
    pub mean_resultant_length: f64,
    /// Team's mean commit hour (circular mean, 0-23).
    pub team_mean_hour: f64,
    /// Team's circular variance (1 - R̄), [0.0, 1.0].
    pub team_circular_variance: f64,
    /// Number of developer pairs with high synchronization (> 0.7).
    pub high_sync_pairs: u32,
    /// Number of developer pairs with low synchronization (< 0.3).
    pub low_sync_pairs: u32,
    /// Total developer pairs analyzed.
    pub total_pairs: u32,
}

/// Rhythm profile for a single developer.
#[derive(Debug)]
pub struct DeveloperRhythm {
    /// Developer name.
    pub author: String,
    /// Mean commit hour (circular mean, 0.0–23.99).
    pub mean_hour: f64,
    /// Mean resultant length for this developer [0.0, 1.0].
    /// Higher = more regular schedule.
    pub resultant_length: f64,
    /// Circular variance [0.0, 1.0].
    pub circular_variance: f64,
    /// Total commits analyzed.
    pub commit_count: u32,
    /// Rhythm classification.
    pub rhythm_type: RhythmType,
}

/// Developer rhythm classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RhythmType {
    /// Regular: concentrated commit hours (R̄ > 0.7).
    Regular,
    /// Moderate: some regularity (0.3 < R̄ ≤ 0.7).
    Moderate,
    /// Irregular: spread across many hours (R̄ ≤ 0.3).
    Irregular,
}

impl std::fmt::Display for RhythmType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Regular => write!(f, "regular"),
            Self::Moderate => write!(f, "moderate"),
            Self::Irregular => write!(f, "irregular"),
        }
    }
}

/// Accumulator for team rhythm data.
#[derive(Default)]
pub struct TeamRhythmAccumulator {
    /// Per-developer commit hours (0-23).
    developer_hours: FxHashMap<String, Vec<u8>>,
}

impl TeamRhythmAccumulator {
    /// Creates a new accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Records a commit timestamp for rhythm analysis.
    ///
    /// Extracts hour-of-day from the Unix timestamp (UTC).
    pub fn record_commit(&mut self, author: &str, timestamp: i64) {
        let hour = ((timestamp % 86400) / 3600).unsigned_abs() as u8;
        let hour = hour % 24; // safety clamp
        self.developer_hours
            .entry(author.to_string())
            .or_default()
            .push(hour);
    }

    /// Finalizes the accumulator into a report.
    #[must_use]
    pub fn finalize(self) -> TeamRhythmReport {
        if self.developer_hours.is_empty() {
            return TeamRhythmReport {
                developers: Vec::new(),
                team_sync_score: 0.0,
                mean_resultant_length: 0.0,
                team_mean_hour: 0.0,
                team_circular_variance: 1.0,
                high_sync_pairs: 0,
                low_sync_pairs: 0,
                total_pairs: 0,
            };
        }

        // Compute per-developer circular statistics
        let mut developers: Vec<DeveloperRhythm> = self
            .developer_hours
            .iter()
            .filter(|(_, hours)| hours.len() >= 2) // need at least 2 commits
            .map(|(author, hours)| compute_developer_rhythm(author, hours))
            .collect();

        developers.sort_by(|a, b| {
            b.resultant_length
                .partial_cmp(&a.resultant_length)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        // Compute team-level circular statistics from ALL commit hours
        let all_hours: Vec<u8> = self
            .developer_hours
            .values()
            .flat_map(|h| h.iter().copied())
            .collect();
        let (team_mean, team_r) = circular_mean_and_r(&all_hours);

        // Compute pairwise synchronization scores
        let dev_names: Vec<&String> = self
            .developer_hours
            .keys()
            .filter(|k| self.developer_hours[*k].len() >= 2)
            .collect();
        let (high_sync, low_sync, total_pairs) =
            compute_pairwise_sync(&dev_names, &self.developer_hours);

        // Team sync score: average pairwise overlap
        let team_sync = if total_pairs > 0 {
            // Use the proportion of high-sync pairs as team sync indicator
            // Combined with mean resultant length for a balanced score
            let pair_score = f64::from(high_sync) / f64::from(total_pairs);
            (0.5 * team_r + 0.5 * pair_score).clamp(0.0, 1.0)
        } else {
            team_r
        };

        TeamRhythmReport {
            developers,
            team_sync_score: team_sync,
            mean_resultant_length: team_r,
            team_mean_hour: team_mean,
            team_circular_variance: 1.0 - team_r,
            high_sync_pairs: high_sync,
            low_sync_pairs: low_sync,
            total_pairs,
        }
    }
}

/// Computes circular mean and mean resultant length for an hour distribution.
///
/// Circular statistics (Fisher 1993): converts hours to angles on a circle,
/// computes the vector mean, and returns (`mean_hour`, `R̄`).
///
/// `R̄` ∈ \[0, 1\]: 1 = all values identical, 0 = uniformly distributed.
fn circular_mean_and_r(hours: &[u8]) -> (f64, f64) {
    if hours.is_empty() {
        return (0.0, 0.0);
    }

    let n = hours.len() as f64;
    let mut sin_sum = 0.0_f64;
    let mut cos_sum = 0.0_f64;

    for &h in hours {
        let theta = 2.0 * std::f64::consts::PI * f64::from(h) / 24.0;
        sin_sum += theta.sin();
        cos_sum += theta.cos();
    }

    let mean_sin = sin_sum / n;
    let mean_cos = cos_sum / n;
    let r = mean_sin.hypot(mean_cos);

    let mean_angle = mean_sin.atan2(mean_cos);
    let mut mean_hour = mean_angle * 24.0 / (2.0 * std::f64::consts::PI);
    if mean_hour < 0.0 {
        mean_hour += 24.0;
    }

    (mean_hour, r.min(1.0))
}

/// Computes rhythm profile for a single developer.
fn compute_developer_rhythm(author: &str, hours: &[u8]) -> DeveloperRhythm {
    let (mean_hour, r) = circular_mean_and_r(hours);
    let rhythm_type = if r > 0.7 {
        RhythmType::Regular
    } else if r > 0.3 {
        RhythmType::Moderate
    } else {
        RhythmType::Irregular
    };

    DeveloperRhythm {
        author: author.to_string(),
        mean_hour,
        resultant_length: r,
        circular_variance: 1.0 - r,
        commit_count: hours.len() as u32,
        rhythm_type,
    }
}

/// Computes pairwise synchronization between developers.
///
/// Two developers are "synchronized" if their commit hour distributions
/// overlap significantly. We use the overlap coefficient of their
/// hour-of-day histograms.
fn compute_pairwise_sync(
    dev_names: &[&String],
    dev_hours: &FxHashMap<String, Vec<u8>>,
) -> (u32, u32, u32) {
    let n = dev_names.len();
    if n < 2 {
        return (0, 0, 0);
    }

    // Pre-compute hour histograms (normalized)
    let histograms: Vec<[f64; 24]> = dev_names
        .iter()
        .map(|name| {
            let hours = &dev_hours[*name];
            let mut hist = [0.0_f64; 24];
            for &h in hours {
                hist[h as usize] += 1.0;
            }
            let total: f64 = hist.iter().sum();
            if total > 0.0 {
                for v in &mut hist {
                    *v /= total;
                }
            }
            hist
        })
        .collect();

    let mut high_sync = 0u32;
    let mut low_sync = 0u32;
    let mut total_pairs = 0u32;

    for i in 0..n {
        for j in (i + 1)..n {
            // Overlap coefficient: sum of min(P_i(h), P_j(h)) for each hour
            let overlap: f64 = (0..24)
                .map(|h| histograms[i][h].min(histograms[j][h]))
                .sum();
            total_pairs += 1;
            if overlap > 0.7 {
                high_sync += 1;
            } else if overlap < 0.3 {
                low_sync += 1;
            }
        }
    }

    (high_sync, low_sync, total_pairs)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = TeamRhythmAccumulator::new();
        let report = acc.finalize();
        assert!(report.developers.is_empty());
        assert!((report.team_sync_score - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_single_developer() {
        let mut acc = TeamRhythmAccumulator::new();
        // Commits at 10:00 and 11:00
        acc.record_commit("Alice", 10 * 3600);
        acc.record_commit("Alice", 11 * 3600);
        let report = acc.finalize();
        assert_eq!(report.developers.len(), 1);
        let dev = &report.developers[0];
        assert_eq!(dev.author, "Alice");
        assert!(dev.resultant_length > 0.9, "R={}", dev.resultant_length);
        assert_eq!(dev.rhythm_type, RhythmType::Regular);
    }

    #[test]
    fn test_circular_mean_single_value() {
        let (mean, r) = circular_mean_and_r(&[12]);
        assert!((mean - 12.0).abs() < 0.1);
        assert!((r - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_circular_mean_opposite_hours() {
        // Commits at 0:00 and 12:00 — mean at 6 or 18, R ≈ 0
        let (_, r) = circular_mean_and_r(&[0, 12]);
        assert!(r < 0.1, "R={}", r);
    }

    #[test]
    fn test_circular_mean_adjacent_hours() {
        // Commits at 10:00 and 11:00 — high concentration
        let (mean, r) = circular_mean_and_r(&[10, 11]);
        assert!(mean > 9.5 && mean < 11.5, "mean={}", mean);
        assert!(r > 0.95, "R={}", r);
    }

    #[test]
    fn test_circular_mean_uniform() {
        // Commits at every hour — should have R ≈ 0
        let hours: Vec<u8> = (0..24).collect();
        let (_, r) = circular_mean_and_r(&hours);
        assert!(r < 0.1, "R={} for uniform distribution", r);
    }

    #[test]
    fn test_synchronized_developers() {
        let mut acc = TeamRhythmAccumulator::new();
        // Both work 9-11 AM
        for h in 9..12 {
            acc.record_commit("Alice", i64::from(h) * 3600);
            acc.record_commit("Bob", i64::from(h) * 3600);
        }
        let report = acc.finalize();
        assert_eq!(report.total_pairs, 1);
        assert!(
            report.team_sync_score > 0.5,
            "sync={}",
            report.team_sync_score
        );
    }

    #[test]
    fn test_asynchronous_developers() {
        let mut acc = TeamRhythmAccumulator::new();
        // Alice works 9 AM, Bob works 9 PM (opposite)
        for _ in 0..5 {
            acc.record_commit("Alice", 9 * 3600);
            acc.record_commit("Bob", 21 * 3600);
        }
        let report = acc.finalize();
        assert_eq!(report.total_pairs, 1);
        // Low overlap between morning and evening workers
        assert!(report.low_sync_pairs >= 1 || report.high_sync_pairs == 0);
    }

    #[test]
    fn test_rhythm_classification() {
        let mut acc = TeamRhythmAccumulator::new();
        // Regular: all commits at 10 AM
        for _ in 0..10 {
            acc.record_commit("Regular", 10 * 3600);
        }
        // Irregular: commits spread across all hours
        for h in 0..24 {
            acc.record_commit("Irregular", i64::from(h) * 3600);
        }
        let report = acc.finalize();
        let regular = report
            .developers
            .iter()
            .find(|d| d.author == "Regular")
            .unwrap();
        let irregular = report
            .developers
            .iter()
            .find(|d| d.author == "Irregular")
            .unwrap();
        assert_eq!(regular.rhythm_type, RhythmType::Regular);
        assert_eq!(irregular.rhythm_type, RhythmType::Irregular);
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", RhythmType::Regular), "regular");
        assert_eq!(format!("{}", RhythmType::Moderate), "moderate");
        assert_eq!(format!("{}", RhythmType::Irregular), "irregular");
    }

    #[test]
    fn test_mean_hour_wraps_midnight() {
        // Commits at 23:00 and 1:00 — mean should be around midnight (0 or 24)
        let (mean, _) = circular_mean_and_r(&[23, 1]);
        // Mean should be near 0 (midnight)
        assert!(
            !(2.0..=22.0).contains(&mean),
            "mean={}, expected near midnight",
            mean
        );
    }
}
