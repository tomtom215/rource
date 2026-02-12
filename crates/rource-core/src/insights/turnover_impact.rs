// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Developer Turnover Impact — measures the risk posed by developers who have
//! left the project and the files they leave orphaned.
//!
//! Detects developer departure (no commits in the last N days of the project
//! history) and computes the impact: how many files lose their top expert when
//! a developer departs.
//!
//! # Research Basis
//!
//! - Mockus (2009) "Succession: Measuring Transfer of Code and Developer
//!   Productivity" (ICSE) — knowledge transfer and succession patterns
//! - Rigby et al. (2016) "Quantifying and Mitigating Turnover-Induced
//!   Knowledge Loss" (ICSE) — turnover's effect on code quality
//!
//! # Algorithm
//!
//! 1. For each developer, find their last commit timestamp.
//! 2. If `last_commit` < (`t_max` - `INACTIVITY_THRESHOLD`), mark as departed.
//! 3. For each departed developer, find files where they were the top owner
//!    AND no remaining active contributor has > `SUCCESSION_THRESHOLD` ownership.
//! 4. Impact = `orphaned_files` / `total_files_touched_by_departed_dev`.
//!
//! # Complexity
//!
//! - O(D × `F_avg`) where D=departed developers, `F_avg`=avg files per developer

use rustc_hash::{FxHashMap, FxHashSet};

/// Days of inactivity before a developer is considered "departed."
const INACTIVITY_THRESHOLD_DAYS: i64 = 90;
const INACTIVITY_THRESHOLD_SECS: i64 = INACTIVITY_THRESHOLD_DAYS * 86400;

/// Minimum ownership share for a remaining contributor to be considered a successor.
const SUCCESSION_THRESHOLD: f64 = 0.20;

/// Turnover impact report for the repository.
#[derive(Debug, Clone)]
pub struct TurnoverImpactReport {
    /// Per-developer departure analysis.
    pub departed_developers: Vec<DepartedDeveloper>,
    /// Total number of active developers.
    pub active_count: u32,
    /// Total number of departed developers.
    pub departed_count: u32,
    /// Overall orphan rate: `orphaned_files` / `total_files`.
    pub orphan_rate: f64,
    /// Number of files with no active expert.
    pub total_orphaned_files: usize,
}

/// Departure analysis for a single developer.
#[derive(Debug, Clone)]
pub struct DepartedDeveloper {
    /// Developer name.
    pub name: String,
    /// Unix timestamp of last commit.
    pub last_commit_ts: i64,
    /// Days since last commit (from end of history).
    pub days_since_last: i64,
    /// Number of files this developer was the top owner of.
    pub owned_files: u32,
    /// Number of those files now orphaned (no successor with > 20% ownership).
    pub orphaned_files: u32,
    /// Impact score: `orphaned_files` / `owned_files`.
    pub impact_score: f64,
}

/// Accumulates per-developer last-commit timestamps.
pub struct TurnoverImpactAccumulator {
    /// Developer → last commit timestamp.
    dev_last_commit: FxHashMap<String, i64>,
}

impl Default for TurnoverImpactAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl TurnoverImpactAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            dev_last_commit: FxHashMap::default(),
        }
    }

    /// Records a commit for turnover analysis.
    pub fn record_commit(&mut self, author: &str, timestamp: i64) {
        let entry = self
            .dev_last_commit
            .entry(author.to_string())
            .or_insert(timestamp);
        if timestamp > *entry {
            *entry = timestamp;
        }
    }

    /// Finalizes the turnover impact report.
    ///
    /// `file_authors` maps file path → (author → commit count).
    /// `t_max` is the timestamp of the last commit in the repository.
    #[must_use]
    #[allow(clippy::implicit_hasher)]
    pub fn finalize(
        self,
        file_authors: &FxHashMap<String, FxHashMap<String, u32>>,
        t_max: i64,
    ) -> TurnoverImpactReport {
        if self.dev_last_commit.is_empty() {
            return TurnoverImpactReport {
                departed_developers: Vec::new(),
                active_count: 0,
                departed_count: 0,
                orphan_rate: 0.0,
                total_orphaned_files: 0,
            };
        }

        // Partition developers into active and departed
        let mut active_devs: FxHashSet<String> = FxHashSet::default();
        let mut departed_devs: FxHashMap<String, i64> = FxHashMap::default();

        for (dev, &last_ts) in &self.dev_last_commit {
            if t_max - last_ts > INACTIVITY_THRESHOLD_SECS {
                departed_devs.insert(dev.clone(), last_ts);
            } else {
                active_devs.insert(dev.clone());
            }
        }

        // For each departed developer, find orphaned files
        let mut departed_developers = Vec::with_capacity(departed_devs.len());
        let mut all_orphaned: FxHashSet<String> = FxHashSet::default();

        for (dev, &last_ts) in &departed_devs {
            let days_since = (t_max - last_ts) / 86400;
            let mut owned_files: u32 = 0;
            let mut orphaned_files: u32 = 0;

            for (path, authors) in file_authors {
                // Check if departed dev was the top owner
                let total: u32 = authors.values().sum();
                let dev_count = authors.get(dev).copied().unwrap_or(0);

                if dev_count == 0 {
                    continue;
                }

                // Must be top owner (largest share) for this file
                let is_top_owner = authors.iter().all(|(_, &count)| count <= dev_count);

                if !is_top_owner {
                    continue;
                }

                owned_files += 1;

                // Check if any active contributor has >= SUCCESSION_THRESHOLD ownership
                let has_successor = authors.iter().any(|(other, &count)| {
                    if !active_devs.contains(other) {
                        return false;
                    }
                    let share = if total > 0 {
                        f64::from(count) / f64::from(total)
                    } else {
                        0.0
                    };
                    share >= SUCCESSION_THRESHOLD && dev != other
                });

                if !has_successor {
                    orphaned_files += 1;
                    all_orphaned.insert(path.clone());
                }
            }

            let impact_score = if owned_files > 0 {
                f64::from(orphaned_files) / f64::from(owned_files)
            } else {
                0.0
            };

            if owned_files > 0 {
                departed_developers.push(DepartedDeveloper {
                    name: dev.clone(),
                    last_commit_ts: last_ts,
                    days_since_last: days_since,
                    owned_files,
                    orphaned_files,
                    impact_score,
                });
            }
        }

        // Sort by impact score descending
        departed_developers.sort_by(|a, b| {
            b.impact_score
                .partial_cmp(&a.impact_score)
                .unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| b.orphaned_files.cmp(&a.orphaned_files))
        });

        let total_files = file_authors.len();
        let orphan_rate = if total_files > 0 {
            all_orphaned.len() as f64 / total_files as f64
        } else {
            0.0
        };

        TurnoverImpactReport {
            active_count: active_devs.len() as u32,
            departed_count: departed_devs.len() as u32,
            orphan_rate,
            total_orphaned_files: all_orphaned.len(),
            departed_developers,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_file_authors(
        data: &[(&str, &[(&str, u32)])],
    ) -> FxHashMap<String, FxHashMap<String, u32>> {
        let mut result = FxHashMap::default();
        for (path, authors) in data {
            let mut author_map = FxHashMap::default();
            for (author, count) in *authors {
                author_map.insert(author.to_string(), *count);
            }
            result.insert(path.to_string(), author_map);
        }
        result
    }

    #[test]
    fn test_empty_accumulator() {
        let acc = TurnoverImpactAccumulator::new();
        let report = acc.finalize(&FxHashMap::default(), 0);
        assert_eq!(report.departed_count, 0);
        assert_eq!(report.active_count, 0);
        assert!(report.departed_developers.is_empty());
    }

    #[test]
    fn test_default_impl() {
        let acc = TurnoverImpactAccumulator::default();
        let report = acc.finalize(&FxHashMap::default(), 0);
        assert!(report.departed_developers.is_empty());
    }

    #[test]
    fn test_no_departed_developers() {
        let mut acc = TurnoverImpactAccumulator::new();
        let t_max = 1_000_000;
        // All developers active (last commit within 90 days)
        acc.record_commit("Alice", t_max - 86400); // 1 day ago
        acc.record_commit("Bob", t_max - 86400 * 30); // 30 days ago
        let file_authors = make_file_authors(&[("a.rs", &[("Alice", 5), ("Bob", 5)])]);
        let report = acc.finalize(&file_authors, t_max);
        assert_eq!(report.departed_count, 0);
        assert_eq!(report.active_count, 2);
        assert!(report.departed_developers.is_empty());
    }

    #[test]
    fn test_one_departed_with_orphaned_files() {
        let mut acc = TurnoverImpactAccumulator::new();
        let t_max = 1_000_000;
        // Alice departed 100 days ago
        acc.record_commit("Alice", t_max - 86400 * 100);
        // Bob is still active
        acc.record_commit("Bob", t_max - 86400);

        // Alice is the top owner of a.rs with no successor
        let file_authors = make_file_authors(&[
            ("a.rs", &[("Alice", 10), ("Bob", 1)]), // Alice owns, Bob has < 20%
            ("b.rs", &[("Bob", 10)]),               // Bob owns
        ]);
        let report = acc.finalize(&file_authors, t_max);
        assert_eq!(report.departed_count, 1);
        assert_eq!(report.active_count, 1);
        assert_eq!(report.departed_developers.len(), 1);
        let alice = &report.departed_developers[0];
        assert_eq!(alice.name, "Alice");
        assert_eq!(alice.owned_files, 1);
        assert_eq!(alice.orphaned_files, 1);
        assert!((alice.impact_score - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_departed_with_successor() {
        let mut acc = TurnoverImpactAccumulator::new();
        let t_max = 1_000_000;
        acc.record_commit("Alice", t_max - 86400 * 100); // departed
        acc.record_commit("Bob", t_max - 86400); // active

        // Alice owns a.rs but Bob has > 20% → not orphaned
        let file_authors = make_file_authors(&[("a.rs", &[("Alice", 6), ("Bob", 4)])]);
        let report = acc.finalize(&file_authors, t_max);
        let alice = report
            .departed_developers
            .iter()
            .find(|d| d.name == "Alice");
        if let Some(a) = alice {
            assert_eq!(a.orphaned_files, 0, "Bob is a successor with 40% share");
        }
    }

    #[test]
    fn test_orphan_rate() {
        let mut acc = TurnoverImpactAccumulator::new();
        let t_max = 1_000_000;
        acc.record_commit("Alice", t_max - 86400 * 200); // departed
        acc.record_commit("Bob", t_max - 86400); // active

        let file_authors = make_file_authors(&[
            ("a.rs", &[("Alice", 10)]), // orphaned
            ("b.rs", &[("Bob", 10)]),   // healthy
        ]);
        let report = acc.finalize(&file_authors, t_max);
        // 1 out of 2 files orphaned → orphan_rate = 0.5
        assert!(
            (report.orphan_rate - 0.5).abs() < f64::EPSILON,
            "orphan_rate={}, expected=0.5",
            report.orphan_rate
        );
        assert_eq!(report.total_orphaned_files, 1);
    }

    #[test]
    fn test_days_since_last() {
        let mut acc = TurnoverImpactAccumulator::new();
        let t_max = 1_000_000;
        let last_commit = t_max - 86400 * 150;
        acc.record_commit("Alice", last_commit);

        let file_authors = make_file_authors(&[("a.rs", &[("Alice", 10)])]);
        let report = acc.finalize(&file_authors, t_max);
        assert_eq!(report.departed_developers.len(), 1);
        assert_eq!(report.departed_developers[0].days_since_last, 150);
    }

    #[test]
    fn test_multiple_commits_takes_latest() {
        let mut acc = TurnoverImpactAccumulator::new();
        let t_max = 1_000_000;
        acc.record_commit("Alice", t_max - 86400 * 200);
        acc.record_commit("Alice", t_max - 86400 * 50); // more recent → still active

        let file_authors = make_file_authors(&[("a.rs", &[("Alice", 10)])]);
        let report = acc.finalize(&file_authors, t_max);
        assert_eq!(report.active_count, 1);
        assert_eq!(report.departed_count, 0);
    }

    #[test]
    fn test_sorted_by_impact_descending() {
        let mut acc = TurnoverImpactAccumulator::new();
        let t_max = 1_000_000;
        acc.record_commit("Alice", t_max - 86400 * 100);
        acc.record_commit("Bob", t_max - 86400 * 100);
        acc.record_commit("Carol", t_max - 86400);

        let file_authors = make_file_authors(&[
            ("a.rs", &[("Alice", 10), ("Carol", 1)]),
            ("b.rs", &[("Alice", 10), ("Carol", 1)]),
            ("c.rs", &[("Bob", 10), ("Carol", 3)]), // Carol has 23% → successor
        ]);
        let report = acc.finalize(&file_authors, t_max);
        for w in report.departed_developers.windows(2) {
            assert!(
                w[0].impact_score >= w[1].impact_score - 1e-10,
                "not sorted: {} < {}",
                w[0].impact_score,
                w[1].impact_score
            );
        }
    }

    // ── Property-based tests ──

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Orphan rate is in [0, 1].
            #[test]
            fn prop_orphan_rate_bounded(n_devs in 1usize..5, n_files in 1usize..10) {
                let mut acc = TurnoverImpactAccumulator::new();
                let t_max = 1_000_000_i64;
                let devs: Vec<String> = (0..n_devs).map(|i| format!("dev{i}")).collect();
                for (i, dev) in devs.iter().enumerate() {
                    // Half departed, half active
                    let ts = if i % 2 == 0 {
                        t_max - 86400 * 200
                    } else {
                        t_max - 86400
                    };
                    acc.record_commit(dev, ts);
                }

                let mut file_authors = FxHashMap::default();
                for f in 0..n_files {
                    let path = format!("f{f}.rs");
                    let mut authors = FxHashMap::default();
                    authors.insert(devs[f % n_devs].clone(), 10);
                    file_authors.insert(path, authors);
                }

                let report = acc.finalize(&file_authors, t_max);
                prop_assert!(
                    (0.0..=1.0).contains(&report.orphan_rate),
                    "orphan_rate={} out of [0,1]",
                    report.orphan_rate
                );
            }

            /// Impact score per developer is in [0, 1].
            #[test]
            fn prop_impact_score_bounded(n_files in 1usize..8) {
                let mut acc = TurnoverImpactAccumulator::new();
                let t_max = 1_000_000_i64;
                acc.record_commit("Alice", t_max - 86400 * 200);

                let mut file_authors = FxHashMap::default();
                for f in 0..n_files {
                    let path = format!("f{f}.rs");
                    let mut authors = FxHashMap::default();
                    authors.insert("Alice".to_string(), 10);
                    file_authors.insert(path, authors);
                }

                let report = acc.finalize(&file_authors, t_max);
                for dev in &report.departed_developers {
                    prop_assert!(
                        (0.0..=1.0).contains(&dev.impact_score),
                        "impact_score={} out of [0,1]",
                        dev.impact_score
                    );
                }
            }
        }
    }
}
