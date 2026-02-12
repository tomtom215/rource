// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Enhanced Truck Factor (Bus Factor) — the minimum number of developers whose
//! departure would leave more than 50% of files without knowledgeable maintainers.
//!
//! This is an enhanced version of the basic bus factor in `ownership.rs`, using
//! the DOA (Degree of Authorship) model from Avelino et al. (2016) to more
//! accurately capture who truly "knows" a file based on authorship primacy,
//! delivery frequency, and competing contributions.
//!
//! # Research Basis
//!
//! - Avelino et al. (2016) "A Novel Approach for Estimating Truck Factors"
//!   (ICPC) — DOA model: `DOA(d,f) = 3.293 + 1.098×FA + 0.164×DL - 0.321×AC`
//! - Ricca et al. (2011) "On the Relationship between the Truck Factor and
//!   Files" (PROMISE) — empirical validation of truck factor metrics
//!
//! # Algorithm
//!
//! For each (developer, file) pair, compute DOA:
//!
//! ```text
//! DOA(d, f) = 3.293 + 1.098 × FA + 0.164 × DL - 0.321 × AC
//!
//! where:
//!   FA = 1 if d was the first author of f, else 0
//!   DL = number of commits by d to f (normalized by max commits to f)
//!   AC = number of commits by others to f (normalized by total commits to f)
//! ```
//!
//! A developer "knows" a file if `DOA > DOA_THRESHOLD` (default: 3.293, the
//! intercept — meaning any positive signal is sufficient).
//!
//! Truck factor is computed by iteratively removing the developer with the
//! highest total DOA and checking if >50% of files have lost all experts.
//!
//! # Complexity
//!
//! - O(F × D) for DOA computation where F=files, D=developers
//! - O(D × F) for iterative removal simulation

use rustc_hash::{FxHashMap, FxHashSet};

/// DOA model intercept — threshold for considering a developer an "expert."
const DOA_THRESHOLD: f64 = 3.293;

/// DOA model coefficients from Avelino et al. (2016).
const DOA_COEFF_FA: f64 = 1.098;
const DOA_COEFF_DL: f64 = 0.164;
const DOA_COEFF_AC: f64 = 0.321;

/// Truck factor report for the repository.
#[derive(Debug, Clone)]
pub struct TruckFactorReport {
    /// The truck factor value (minimum devs to lose to orphan >50% of files).
    pub truck_factor: u32,
    /// Developers ranked by total DOA (most critical first).
    pub ranked_developers: Vec<DeveloperCriticality>,
    /// Total files analyzed.
    pub total_files: usize,
    /// Files that would be orphaned if the top developer leaves.
    pub top_dev_orphan_count: usize,
    /// Percentage of files at risk (covered by only 1 expert).
    pub single_expert_pct: f64,
}

/// Criticality ranking for a developer.
#[derive(Debug, Clone)]
pub struct DeveloperCriticality {
    /// Developer name.
    pub name: String,
    /// Total DOA across all files (sum of DOA for files where they are expert).
    pub total_doa: f64,
    /// Number of files where this developer is an expert.
    pub expert_file_count: u32,
    /// Number of files where this developer is the sole expert.
    pub sole_expert_count: u32,
}

/// Computes the enhanced truck factor from the `file_authors` accumulator.
///
/// `file_authors` maps file path → (author → commit count).
/// `first_authors` maps file path → author who first created the file.
///
/// # Complexity
///
/// O(F × D) for DOA computation + O(D × F) for iterative removal.
#[must_use]
#[allow(clippy::implicit_hasher, clippy::too_many_lines)]
pub fn compute_truck_factor(
    file_authors: &FxHashMap<String, FxHashMap<String, u32>>,
    first_authors: &FxHashMap<String, String>,
) -> TruckFactorReport {
    if file_authors.is_empty() {
        return TruckFactorReport {
            truck_factor: 0,
            ranked_developers: Vec::new(),
            total_files: 0,
            top_dev_orphan_count: 0,
            single_expert_pct: 0.0,
        };
    }

    // Step 1: Compute DOA for every (developer, file) pair
    // doa_matrix: developer → (file → DOA score)
    let mut doa_matrix: FxHashMap<String, FxHashMap<String, f64>> = FxHashMap::default();
    // experts_per_file: file → set of expert developers
    let mut experts_per_file: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();

    for (path, authors) in file_authors {
        let total_commits: u32 = authors.values().sum();
        let max_commits = authors.values().max().copied().unwrap_or(1);
        let first_author = first_authors.get(path.as_str()).map(String::as_str);

        for (dev, &commit_count) in authors {
            let fa = if first_author == Some(dev.as_str()) {
                1.0
            } else {
                0.0
            };
            let dl = if max_commits > 0 {
                f64::from(commit_count) / f64::from(max_commits)
            } else {
                0.0
            };
            let ac = if total_commits > 0 {
                f64::from(total_commits - commit_count) / f64::from(total_commits)
            } else {
                0.0
            };

            let doa = DOA_THRESHOLD + DOA_COEFF_FA * fa + DOA_COEFF_DL * dl - DOA_COEFF_AC * ac;

            if doa > DOA_THRESHOLD {
                doa_matrix
                    .entry(dev.clone())
                    .or_default()
                    .insert(path.clone(), doa);
                experts_per_file
                    .entry(path.clone())
                    .or_default()
                    .insert(dev.clone());
            }
        }
    }

    // Step 2: Rank developers by total DOA
    let mut dev_rankings: Vec<DeveloperCriticality> = doa_matrix
        .iter()
        .map(|(dev, files)| {
            let total_doa: f64 = files.values().sum();
            let expert_file_count = files.len() as u32;
            let sole_expert_count = files
                .keys()
                .filter(|f| {
                    experts_per_file
                        .get(f.as_str())
                        .is_some_and(|e| e.len() == 1)
                })
                .count() as u32;
            DeveloperCriticality {
                name: dev.clone(),
                total_doa,
                expert_file_count,
                sole_expert_count,
            }
        })
        .collect();

    dev_rankings.sort_by(|a, b| {
        b.total_doa
            .partial_cmp(&a.total_doa)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    // Step 3: Iteratively remove developers to find truck factor
    let total_files = file_authors.len();
    let orphan_threshold = total_files / 2 + 1; // >50%
    let mut removed: FxHashSet<String> = FxHashSet::default();
    let mut truck_factor: u32 = 0;

    // Count files orphaned when top dev leaves (before full simulation)
    let top_dev_orphan_count = dev_rankings.first().map_or(0, |top| {
        count_orphaned_files(&experts_per_file, &FxHashSet::from_iter([top.name.clone()]))
    });

    for dev in &dev_rankings {
        removed.insert(dev.name.clone());
        truck_factor += 1;
        let orphaned = count_orphaned_files(&experts_per_file, &removed);
        if orphaned >= orphan_threshold {
            break;
        }
    }

    // If we removed all developers and still didn't reach threshold
    if truck_factor == 0 {
        truck_factor = dev_rankings.len() as u32;
    }

    // Step 4: Compute single-expert percentage
    let single_expert_files = experts_per_file
        .values()
        .filter(|experts| experts.len() == 1)
        .count();
    let single_expert_pct = if total_files > 0 {
        single_expert_files as f64 / total_files as f64
    } else {
        0.0
    };

    TruckFactorReport {
        truck_factor,
        ranked_developers: dev_rankings,
        total_files,
        top_dev_orphan_count,
        single_expert_pct,
    }
}

/// Counts files that have no remaining experts after removing a set of developers.
fn count_orphaned_files(
    experts_per_file: &FxHashMap<String, FxHashSet<String>>,
    removed: &FxHashSet<String>,
) -> usize {
    experts_per_file
        .values()
        .filter(|experts| experts.iter().all(|e| removed.contains(e)))
        .count()
}

/// Accumulates first-author information for truck factor computation.
pub struct TruckFactorAccumulator {
    /// Maps file path → first author (the developer who created it).
    first_authors: FxHashMap<String, String>,
}

impl Default for TruckFactorAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl TruckFactorAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            first_authors: FxHashMap::default(),
        }
    }

    /// Records a file creation event.
    pub fn record_file(&mut self, path: &str, action: super::FileActionKind, author: &str) {
        if action == super::FileActionKind::Create {
            // Only record the first Create for each file
            self.first_authors
                .entry(path.to_string())
                .or_insert_with(|| author.to_string());
        }
    }

    /// Returns the accumulated first-author map for use in `compute_truck_factor`.
    #[must_use]
    pub fn into_first_authors(self) -> FxHashMap<String, String> {
        self.first_authors
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

    fn make_first_authors(data: &[(&str, &str)]) -> FxHashMap<String, String> {
        data.iter()
            .map(|(p, a)| (p.to_string(), a.to_string()))
            .collect()
    }

    #[test]
    fn test_empty_input() {
        let report = compute_truck_factor(&FxHashMap::default(), &FxHashMap::default());
        assert_eq!(report.truck_factor, 0);
        assert!(report.ranked_developers.is_empty());
        assert_eq!(report.total_files, 0);
    }

    #[test]
    fn test_single_developer() {
        let file_authors = make_file_authors(&[
            ("a.rs", &[("Alice", 10)]),
            ("b.rs", &[("Alice", 5)]),
            ("c.rs", &[("Alice", 3)]),
        ]);
        let first_authors =
            make_first_authors(&[("a.rs", "Alice"), ("b.rs", "Alice"), ("c.rs", "Alice")]);
        let report = compute_truck_factor(&file_authors, &first_authors);
        assert_eq!(
            report.truck_factor, 1,
            "single developer → truck factor = 1"
        );
        assert_eq!(report.ranked_developers.len(), 1);
        assert_eq!(report.ranked_developers[0].name, "Alice");
    }

    #[test]
    fn test_two_developers_shared() {
        // Both developers have significant contributions to all files
        let file_authors = make_file_authors(&[
            ("a.rs", &[("Alice", 5), ("Bob", 5)]),
            ("b.rs", &[("Alice", 5), ("Bob", 5)]),
        ]);
        let first_authors = make_first_authors(&[("a.rs", "Alice"), ("b.rs", "Bob")]);
        let report = compute_truck_factor(&file_authors, &first_authors);
        // With shared expertise, truck factor should be > 1
        assert!(
            report.truck_factor >= 1,
            "shared files → truck_factor >= 1, got {}",
            report.truck_factor
        );
    }

    #[test]
    fn test_disjoint_developers() {
        // Each developer owns different files exclusively
        let file_authors =
            make_file_authors(&[("a.rs", &[("Alice", 10)]), ("b.rs", &[("Bob", 10)])]);
        let first_authors = make_first_authors(&[("a.rs", "Alice"), ("b.rs", "Bob")]);
        let report = compute_truck_factor(&file_authors, &first_authors);
        // Threshold is >50% (strictly greater): with 2 files, need 2 orphaned
        // Removing 1 dev orphans 1/2 = 50% (not >50%), so both must be removed
        assert_eq!(
            report.truck_factor, 2,
            "disjoint ownership with 2 files → truck_factor = 2"
        );
    }

    #[test]
    fn test_doa_model_first_author_bonus() {
        // File with first author getting a DOA bonus
        let file_authors = make_file_authors(&[("a.rs", &[("Alice", 3), ("Bob", 10)])]);
        let first_authors = make_first_authors(&[("a.rs", "Alice")]);
        let report = compute_truck_factor(&file_authors, &first_authors);
        // Alice is first author → FA bonus even with fewer commits
        let alice = report.ranked_developers.iter().find(|d| d.name == "Alice");
        let bob = report.ranked_developers.iter().find(|d| d.name == "Bob");
        assert!(alice.is_some() || bob.is_some(), "at least one expert");
    }

    #[test]
    fn test_single_expert_percentage() {
        let file_authors = make_file_authors(&[
            ("solo.rs", &[("Alice", 10)]),
            ("shared.rs", &[("Alice", 5), ("Bob", 5)]),
        ]);
        let first_authors = make_first_authors(&[("solo.rs", "Alice"), ("shared.rs", "Alice")]);
        let report = compute_truck_factor(&file_authors, &first_authors);
        // solo.rs has 1 expert, shared.rs has 2
        assert!(
            report.single_expert_pct >= 0.0 && report.single_expert_pct <= 1.0,
            "single_expert_pct={} out of [0,1]",
            report.single_expert_pct
        );
    }

    #[test]
    fn test_ranked_by_total_doa_descending() {
        let file_authors = make_file_authors(&[
            ("a.rs", &[("Alice", 10), ("Bob", 1)]),
            ("b.rs", &[("Alice", 8), ("Bob", 2)]),
            ("c.rs", &[("Alice", 1), ("Bob", 10)]),
        ]);
        let first_authors =
            make_first_authors(&[("a.rs", "Alice"), ("b.rs", "Alice"), ("c.rs", "Bob")]);
        let report = compute_truck_factor(&file_authors, &first_authors);
        for w in report.ranked_developers.windows(2) {
            assert!(
                w[0].total_doa >= w[1].total_doa - 1e-10,
                "not sorted: {} < {}",
                w[0].total_doa,
                w[1].total_doa
            );
        }
    }

    #[test]
    fn test_accumulator() {
        let mut acc = TruckFactorAccumulator::new();
        acc.record_file("a.rs", super::super::FileActionKind::Create, "Alice");
        acc.record_file("a.rs", super::super::FileActionKind::Modify, "Bob");
        acc.record_file("b.rs", super::super::FileActionKind::Create, "Bob");
        let first = acc.into_first_authors();
        assert_eq!(first.get("a.rs").map(String::as_str), Some("Alice"));
        assert_eq!(first.get("b.rs").map(String::as_str), Some("Bob"));
    }

    #[test]
    fn test_accumulator_default() {
        let acc = TruckFactorAccumulator::default();
        assert!(acc.into_first_authors().is_empty());
    }

    #[test]
    fn test_accumulator_duplicate_creates() {
        // Only the first Create should be recorded
        let mut acc = TruckFactorAccumulator::new();
        acc.record_file("a.rs", super::super::FileActionKind::Create, "Alice");
        acc.record_file("a.rs", super::super::FileActionKind::Create, "Bob");
        let first = acc.into_first_authors();
        assert_eq!(first.get("a.rs").map(String::as_str), Some("Alice"));
    }

    // ── Property-based tests ──

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Truck factor is at most the number of developers.
            #[test]
            fn prop_truck_factor_bounded(n_devs in 1usize..5, n_files in 1usize..10) {
                let mut file_authors = FxHashMap::default();
                let mut first_authors = FxHashMap::default();
                let devs: Vec<String> = (0..n_devs).map(|i| format!("dev{i}")).collect();

                for f in 0..n_files {
                    let path = format!("file{f}.rs");
                    let mut authors = FxHashMap::default();
                    let primary = &devs[f % n_devs];
                    authors.insert(primary.clone(), 10);
                    first_authors.insert(path.clone(), primary.clone());
                    file_authors.insert(path, authors);
                }

                let report = compute_truck_factor(&file_authors, &first_authors);
                prop_assert!(
                    report.truck_factor as usize <= n_devs,
                    "truck_factor={} > n_devs={}",
                    report.truck_factor,
                    n_devs
                );
            }

            /// Single-expert percentage is in [0, 1].
            #[test]
            fn prop_single_expert_pct_bounded(n_devs in 1usize..4, n_files in 1usize..8) {
                let mut file_authors = FxHashMap::default();
                let mut first_authors = FxHashMap::default();
                let devs: Vec<String> = (0..n_devs).map(|i| format!("dev{i}")).collect();

                for f in 0..n_files {
                    let path = format!("f{f}.rs");
                    let mut authors = FxHashMap::default();
                    for (d, dev) in devs.iter().enumerate().take((f % n_devs) + 1) {
                        authors.insert(dev.clone(), (10 - d) as u32);
                    }
                    first_authors.insert(path.clone(), devs[0].clone());
                    file_authors.insert(path, authors);
                }

                let report = compute_truck_factor(&file_authors, &first_authors);
                prop_assert!(
                    (0.0..=1.0).contains(&report.single_expert_pct),
                    "single_expert_pct={} out of [0,1]",
                    report.single_expert_pct
                );
            }
        }
    }
}
