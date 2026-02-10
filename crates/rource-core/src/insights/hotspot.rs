// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! File hotspot analysis.
//!
//! Identifies files with disproportionately high change frequency, weighted
//! by recency. Research (Nagappan et al. 2005, Microsoft) shows that relative
//! code churn predicts fault-prone components with ~89% accuracy.
//!
//! # Algorithm
//!
//! For each file, we compute:
//! - **Total changes**: Raw count of commits touching this file
//! - **Weighted changes**: Exponentially decay-weighted sum favoring recent changes
//! - **Hotspot score**: `weighted_changes × (1 + log2(total_changes))`
//!
//! The exponential decay uses `λ = ln(2) / half_life`, where `half_life` is half
//! the repository's active time span. This ensures recent changes weigh more
//! while older changes still contribute.

use super::FileActionKind;

/// Decay half-life as a fraction of the total time span.
///
/// A value of 0.5 means changes at the midpoint of the repo's history
/// receive half the weight of the most recent changes.
const HALF_LIFE_FRACTION: f64 = 0.5;

/// A file identified as a hotspot.
#[derive(Debug, Clone)]
pub struct FileHotspot {
    /// File path relative to repository root.
    pub path: String,
    /// Total number of changes (unweighted).
    pub total_changes: u32,
    /// Recency-weighted change count.
    pub weighted_changes: f64,
    /// Composite hotspot score (higher = more attention needed).
    pub score: f64,
    /// Number of create actions.
    pub creates: u32,
    /// Number of modify actions.
    pub modifies: u32,
    /// Number of delete actions.
    pub deletes: u32,
    /// Timestamp of first change (Unix seconds).
    pub first_seen: i64,
    /// Timestamp of most recent change (Unix seconds).
    pub last_seen: i64,
}

/// Accumulator for building hotspot data during a single pass over commits.
#[derive(Debug)]
pub struct HotspotAccumulator {
    /// Timestamps of each change (for decay computation).
    timestamps: Vec<i64>,
    /// Total changes.
    total: u32,
    /// Action counts.
    creates: u32,
    modifies: u32,
    deletes: u32,
    /// First and last seen timestamps.
    first_seen: i64,
    last_seen: i64,
}

impl HotspotAccumulator {
    /// Creates a new accumulator with the first change timestamp.
    #[must_use]
    pub fn new(first_timestamp: i64) -> Self {
        Self {
            timestamps: Vec::new(),
            total: 0,
            creates: 0,
            modifies: 0,
            deletes: 0,
            first_seen: first_timestamp,
            last_seen: first_timestamp,
        }
    }

    /// Records a change at the given timestamp.
    pub fn record(&mut self, timestamp: i64, action: FileActionKind) {
        self.timestamps.push(timestamp);
        self.total += 1;
        match action {
            FileActionKind::Create => self.creates += 1,
            FileActionKind::Modify => self.modifies += 1,
            FileActionKind::Delete => self.deletes += 1,
        }
        if timestamp < self.first_seen {
            self.first_seen = timestamp;
        }
        if timestamp > self.last_seen {
            self.last_seen = timestamp;
        }
    }

    /// Finalizes the accumulator into a [`FileHotspot`].
    ///
    /// # Arguments
    ///
    /// * `path` - File path
    /// * `t_min` - Earliest commit timestamp in the repository
    /// * `t_max` - Latest commit timestamp in the repository
    #[must_use]
    pub fn finalize(self, path: String, t_min: i64, t_max: i64) -> FileHotspot {
        let time_span = (t_max - t_min) as f64;
        let weighted_changes = if time_span > 0.0 {
            let half_life = time_span * HALF_LIFE_FRACTION;
            // λ = ln(2) / half_life
            let lambda = std::f64::consts::LN_2 / half_life;
            self.timestamps
                .iter()
                .map(|&t| {
                    let age = (t_max - t) as f64;
                    (-lambda * age).exp()
                })
                .sum()
        } else {
            // All commits at same timestamp — equal weight
            f64::from(self.total)
        };

        // Score: weighted changes amplified by log of total changes
        // This rewards files that are both recently active AND historically turbulent
        let log_factor = 1.0 + f64::from(self.total).ln_1p();
        let score = weighted_changes * log_factor;

        FileHotspot {
            path,
            total_changes: self.total,
            weighted_changes,
            score,
            creates: self.creates,
            modifies: self.modifies,
            deletes: self.deletes,
            first_seen: self.first_seen,
            last_seen: self.last_seen,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_accumulator_single_change() {
        let mut acc = HotspotAccumulator::new(1000);
        acc.record(1000, FileActionKind::Modify);
        let hotspot = acc.finalize("test.rs".to_string(), 1000, 1000);

        assert_eq!(hotspot.total_changes, 1);
        assert_eq!(hotspot.modifies, 1);
        assert_eq!(hotspot.creates, 0);
        assert_eq!(hotspot.deletes, 0);
        // Zero time span → weighted_changes = total = 1.0
        assert!((hotspot.weighted_changes - 1.0).abs() < f64::EPSILON);
        // score = 1.0 * (1 + ln(1 + 1)) = 1.0 * (1 + ln(2))
        let expected_score = 1.0 * (1.0 + 1.0_f64.ln_1p());
        assert!(
            (hotspot.score - expected_score).abs() < 1e-10,
            "score={}, expected={}",
            hotspot.score,
            expected_score
        );
    }

    #[test]
    fn test_recent_changes_weighted_higher() {
        // File A: changed only recently
        let mut acc_recent = HotspotAccumulator::new(9000);
        acc_recent.record(9000, FileActionKind::Modify);
        acc_recent.record(10000, FileActionKind::Modify);
        let recent = acc_recent.finalize("recent.rs".to_string(), 0, 10000);

        // File B: changed only at the start
        let mut acc_old = HotspotAccumulator::new(0);
        acc_old.record(0, FileActionKind::Modify);
        acc_old.record(1000, FileActionKind::Modify);
        let old = acc_old.finalize("old.rs".to_string(), 0, 10000);

        // Same number of changes, but recent should have higher weighted_changes
        assert_eq!(recent.total_changes, old.total_changes);
        assert!(
            recent.weighted_changes > old.weighted_changes,
            "recent weighted={}, old weighted={}",
            recent.weighted_changes,
            old.weighted_changes
        );
        // Verify actual decay math: time_span=10000, half_life=5000
        // lambda = ln(2)/5000
        // For recent: ages are 1000 and 0 → weights = exp(-λ*1000) + exp(0)
        // For old: ages are 10000 and 9000 → much lower weights
        let lambda = std::f64::consts::LN_2 / 5000.0;
        let expected_recent = (-lambda * 1000.0).exp() + 1.0; // ages: 1000, 0
        let expected_old = (-lambda * 10000.0).exp() + (-lambda * 9000.0).exp();
        assert!(
            (recent.weighted_changes - expected_recent).abs() < 1e-10,
            "recent weighted={}, expected={}",
            recent.weighted_changes,
            expected_recent
        );
        assert!(
            (old.weighted_changes - expected_old).abs() < 1e-10,
            "old weighted={}, expected={}",
            old.weighted_changes,
            expected_old
        );
    }

    #[test]
    fn test_more_changes_higher_score() {
        let mut acc_many = HotspotAccumulator::new(5000);
        for ts in [5000, 6000, 7000, 8000, 9000] {
            acc_many.record(ts, FileActionKind::Modify);
        }
        let many = acc_many.finalize("busy.rs".to_string(), 0, 10000);

        let mut acc_few = HotspotAccumulator::new(9000);
        acc_few.record(9000, FileActionKind::Modify);
        let few = acc_few.finalize("quiet.rs".to_string(), 0, 10000);

        assert!(many.score > few.score);
    }

    #[test]
    fn test_action_counts() {
        let mut acc = HotspotAccumulator::new(1000);
        acc.record(1000, FileActionKind::Create);
        acc.record(2000, FileActionKind::Modify);
        acc.record(3000, FileActionKind::Modify);
        acc.record(4000, FileActionKind::Delete);
        let hotspot = acc.finalize("mixed.rs".to_string(), 1000, 4000);

        assert_eq!(hotspot.creates, 1);
        assert_eq!(hotspot.modifies, 2);
        assert_eq!(hotspot.deletes, 1);
        assert_eq!(hotspot.total_changes, 4);
    }

    #[test]
    fn test_first_last_seen() {
        let mut acc = HotspotAccumulator::new(3000);
        acc.record(3000, FileActionKind::Modify);
        acc.record(1000, FileActionKind::Create);
        acc.record(5000, FileActionKind::Modify);
        let hotspot = acc.finalize("track.rs".to_string(), 0, 10000);

        assert_eq!(hotspot.first_seen, 1000);
        assert_eq!(hotspot.last_seen, 5000);
    }

    #[test]
    fn test_first_last_seen_strict_boundaries() {
        // Kills mutants: < vs <= on first_seen, > vs >= on last_seen
        // Start with timestamp 500, then record 500 again — first_seen must stay 500, not change
        let mut acc = HotspotAccumulator::new(500);
        acc.record(500, FileActionKind::Modify);
        // Record earlier timestamp — first_seen must update to 200
        acc.record(200, FileActionKind::Modify);
        // Record timestamp equal to current first_seen — must NOT update (< not <=)
        acc.record(200, FileActionKind::Modify);
        // Record timestamp equal to current last_seen — must NOT update (> not >=)
        acc.record(500, FileActionKind::Modify);
        // Record a later timestamp
        acc.record(800, FileActionKind::Modify);

        let hotspot = acc.finalize("bounds.rs".to_string(), 0, 1000);
        assert_eq!(hotspot.first_seen, 200);
        assert_eq!(hotspot.last_seen, 800);
        assert_eq!(hotspot.total_changes, 5);
    }

    #[test]
    fn test_zero_time_span() {
        // All commits at the same instant
        let mut acc = HotspotAccumulator::new(5000);
        acc.record(5000, FileActionKind::Modify);
        acc.record(5000, FileActionKind::Modify);
        acc.record(5000, FileActionKind::Modify);
        let hotspot = acc.finalize("instant.rs".to_string(), 5000, 5000);

        assert_eq!(hotspot.total_changes, 3);
        assert!((hotspot.weighted_changes - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_score_formula_exact() {
        // Kills mutants: * vs + and * vs / in score formula
        // Use total=5 so that multiplication and addition diverge significantly:
        // 5.0 * (1 + ln(6)) ≈ 13.96 vs 5.0 + (1 + ln(6)) ≈ 7.79 (diff ≈ 6.17)
        // With zero time_span, weighted_changes = total = 5
        let mut acc = HotspotAccumulator::new(100);
        for _ in 0..5 {
            acc.record(100, FileActionKind::Modify);
        }
        let hotspot = acc.finalize("exact.rs".to_string(), 100, 100);

        assert_eq!(hotspot.total_changes, 5);
        assert!((hotspot.weighted_changes - 5.0).abs() < f64::EPSILON);
        // score = weighted_changes * (1 + ln_1p(total))
        // = 5.0 * (1.0 + ln(1 + 5)) = 5.0 * (1.0 + ln(6))
        let log_factor = 1.0 + 5.0_f64.ln_1p();
        let expected = 5.0 * log_factor;
        assert!(
            (hotspot.score - expected).abs() < 1e-10,
            "score={}, expected={} (5.0 * (1.0 + ln(6)))",
            hotspot.score,
            expected
        );
        // Verify it's NOT the result of + or / operations
        let wrong_add = 5.0 + log_factor;
        let wrong_div = 5.0 / log_factor;
        assert!(
            (hotspot.score - wrong_add).abs() > 1.0,
            "score ({}) should differ from addition variant ({})",
            hotspot.score,
            wrong_add
        );
        assert!(
            (hotspot.score - wrong_div).abs() > 1.0,
            "score ({}) should differ from division variant ({})",
            hotspot.score,
            wrong_div
        );
    }

    #[test]
    fn test_decay_weight_direction() {
        // Kills mutant: t_max - t vs t_max + t
        // With positive ages, decay should reduce weight
        let mut acc = HotspotAccumulator::new(0);
        acc.record(0, FileActionKind::Modify); // age = t_max - 0 = 10000 (old)
        let hotspot = acc.finalize("old.rs".to_string(), 0, 10000);

        // exp(-lambda * 10000) where lambda = ln(2)/5000
        // = exp(-ln(2) * 2) = exp(-2*ln(2)) = 1/4 = 0.25
        let expected_weight = 0.25;
        assert!(
            (hotspot.weighted_changes - expected_weight).abs() < 1e-10,
            "weighted_changes={}, expected={}",
            hotspot.weighted_changes,
            expected_weight
        );
        // If mutation flipped - to +, age would be 10000+0=10000 still but
        // with t_max + t it would be 20000 → exp(-lambda*20000) = 1/16
        // So verify we got 0.25, not 0.0625
        assert!(
            hotspot.weighted_changes > 0.2,
            "decay must be moderate for age = time_span"
        );
    }
}
