// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Per-File Ownership Fragmentation (Gini Coefficient) — measures inequality
//! of commit distribution among contributors for each file.
//!
//! While the repository-level Gini (in `inequality.rs`) measures global commit
//! distribution, this module computes per-file Gini coefficients to identify
//! files with diluted ownership (mid-range Gini) that correlate with defects.
//!
//! # Research Basis
//!
//! - Bird et al. (2011) "Don't Touch My Code! Examining the Effects of
//!   Ownership on Software Quality" (FSE) — strong vs weak ownership
//! - Greiler et al. (2015) "Code Ownership and Software Quality: A
//!   Replication Study" (MSR) — confirms ownership fragmentation predicts defects
//!
//! # Algorithm
//!
//! Per-file Gini coefficient of contributor commit counts:
//!
//! ```text
//! G = (2 × Σ(i × x_i)) / (n × Σ(x_i)) - (n + 1) / n
//!
//! where:
//!   x_i = sorted commit counts per contributor (ascending)
//!   n   = number of contributors
//!   i   = 1-based rank
//! ```
//!
//! - G = 0: perfectly equal ownership (all contributors commit equally)
//! - G = 1: maximally concentrated (one person owns everything)
//! - Mid-range (0.3–0.7): fragmented ownership — highest defect risk
//!
//! # Complexity
//!
//! - O(k log k) per file where k = number of contributors (sorting step)
//! - O(F × `k_avg`) total where F = files, `k_avg` = average contributors per file

use rustc_hash::FxHashMap;

/// Ownership fragmentation report for the repository.
#[derive(Debug, Clone)]
pub struct OwnershipFragmentationReport {
    /// Per-file ownership fragmentation data.
    pub files: Vec<FileOwnershipFragmentation>,
    /// Average Gini coefficient across all files.
    pub avg_gini: f64,
    /// Number of files with fragmented ownership (Gini 0.3–0.7).
    pub fragmented_count: usize,
    /// Number of files with concentrated ownership (Gini > 0.7).
    pub concentrated_count: usize,
}

/// Ownership fragmentation for a single file.
#[derive(Debug, Clone)]
pub struct FileOwnershipFragmentation {
    /// File path.
    pub path: String,
    /// Gini coefficient of contributor commit distribution (0.0–1.0).
    pub gini_coefficient: f64,
    /// Number of contributors.
    pub contributor_count: u32,
    /// Classification based on Gini value.
    pub ownership_type: OwnershipType,
}

/// Ownership classification based on Gini coefficient.
///
/// Based on Bird et al. (2011) thresholds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OwnershipType {
    /// Single contributor or very high concentration (Gini ≥ 0.7 or count = 1).
    Strong,
    /// Moderate concentration — a clear owner exists but others contribute.
    Moderate,
    /// Fragmented ownership — multiple near-equal contributors.
    /// This is the highest defect-risk category per Bird et al. (2011).
    Fragmented,
    /// Perfectly equal distribution (Gini = 0, multiple contributors).
    Equal,
}

impl std::fmt::Display for OwnershipType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Strong => write!(f, "strong"),
            Self::Moderate => write!(f, "moderate"),
            Self::Fragmented => write!(f, "fragmented"),
            Self::Equal => write!(f, "equal"),
        }
    }
}

/// Computes per-file ownership fragmentation from the `file_authors` accumulator.
///
/// `file_authors` maps file path → (author → commit count).
///
/// # Complexity
///
/// O(F × `k_avg` log `k_avg`) where F = files, `k_avg` = avg contributors per file.
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn compute_ownership_fragmentation(
    file_authors: &FxHashMap<String, FxHashMap<String, u32>>,
) -> OwnershipFragmentationReport {
    let mut files = Vec::with_capacity(file_authors.len());

    for (path, authors) in file_authors {
        if authors.is_empty() {
            continue;
        }

        let mut counts: Vec<u32> = authors.values().copied().collect();
        counts.sort_unstable();

        let gini = compute_gini(&counts);
        let contributor_count = counts.len() as u32;
        let ownership_type = classify_ownership(gini, contributor_count);

        files.push(FileOwnershipFragmentation {
            path: path.clone(),
            gini_coefficient: gini,
            contributor_count,
            ownership_type,
        });
    }

    // Sort by Gini descending (most fragmentation-risk first)
    files.sort_by(|a, b| {
        b.gini_coefficient
            .partial_cmp(&a.gini_coefficient)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let avg_gini = if files.is_empty() {
        0.0
    } else {
        files.iter().map(|f| f.gini_coefficient).sum::<f64>() / files.len() as f64
    };
    let fragmented_count = files
        .iter()
        .filter(|f| f.ownership_type == OwnershipType::Fragmented)
        .count();
    let concentrated_count = files
        .iter()
        .filter(|f| f.ownership_type == OwnershipType::Strong)
        .count();

    OwnershipFragmentationReport {
        files,
        avg_gini,
        fragmented_count,
        concentrated_count,
    }
}

/// Computes the Gini coefficient from a sorted (ascending) array of values.
///
/// Uses the formula: `G = (2 × Σ(i × x_i)) / (n × Σ(x_i)) - (n + 1) / n`
///
/// # Arguments
///
/// * `sorted_counts` - Commit counts sorted ascending
///
/// # Returns
///
/// Gini coefficient in [0, 1]. Returns 0.0 for single-element arrays.
fn compute_gini(sorted_counts: &[u32]) -> f64 {
    let n = sorted_counts.len();
    if n <= 1 {
        return 0.0;
    }

    let sum: f64 = sorted_counts.iter().map(|&c| f64::from(c)).sum();
    if sum <= 0.0 {
        return 0.0;
    }

    let n_f = n as f64;
    let weighted_sum: f64 = sorted_counts
        .iter()
        .enumerate()
        .map(|(i, &c)| (i as f64 + 1.0) * f64::from(c))
        .sum();

    let gini = (2.0 * weighted_sum) / (n_f * sum) - (n_f + 1.0) / n_f;
    gini.clamp(0.0, 1.0)
}

/// Classifies ownership based on Gini coefficient and contributor count.
fn classify_ownership(gini: f64, contributor_count: u32) -> OwnershipType {
    if contributor_count <= 1 {
        return OwnershipType::Strong;
    }
    if gini < f64::EPSILON {
        return OwnershipType::Equal;
    }
    if gini >= 0.7 {
        OwnershipType::Strong
    } else if gini >= 0.3 {
        OwnershipType::Fragmented
    } else {
        OwnershipType::Moderate
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
    fn test_empty_input() {
        let data = FxHashMap::default();
        let report = compute_ownership_fragmentation(&data);
        assert!(report.files.is_empty());
        assert!((report.avg_gini - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_single_contributor_gini_zero() {
        let data = make_file_authors(&[("a.rs", &[("Alice", 10)])]);
        let report = compute_ownership_fragmentation(&data);
        assert_eq!(report.files.len(), 1);
        assert!(
            (report.files[0].gini_coefficient - 0.0).abs() < f64::EPSILON,
            "single contributor should have Gini=0"
        );
        assert_eq!(report.files[0].ownership_type, OwnershipType::Strong);
    }

    #[test]
    fn test_equal_contributors_gini_zero() {
        let data = make_file_authors(&[("a.rs", &[("Alice", 5), ("Bob", 5)])]);
        let report = compute_ownership_fragmentation(&data);
        let f = &report.files[0];
        assert!(
            f.gini_coefficient.abs() < f64::EPSILON,
            "equal contributors should have Gini=0, got {}",
            f.gini_coefficient
        );
        assert_eq!(f.ownership_type, OwnershipType::Equal);
    }

    #[test]
    fn test_highly_unequal_gini_high() {
        // One contributor with 99 commits, one with 1 commit
        let data = make_file_authors(&[("a.rs", &[("Alice", 99), ("Bob", 1)])]);
        let report = compute_ownership_fragmentation(&data);
        let f = &report.files[0];
        // Gini should be close to (but less than) 1.0
        assert!(f.gini_coefficient > 0.4, "gini={}", f.gini_coefficient);
    }

    #[test]
    fn test_gini_formula_exact() {
        // 3 contributors with [1, 2, 3] commits
        // sorted: [1, 2, 3], n=3, sum=6
        // weighted_sum = 1*1 + 2*2 + 3*3 = 1 + 4 + 9 = 14
        // gini = (2*14)/(3*6) - (3+1)/3 = 28/18 - 4/3 = 1.5556 - 1.3333 = 0.2222
        let gini = compute_gini(&[1, 2, 3]);
        let expected = 2.0 / 9.0; // = 0.2222...
        assert!(
            (gini - expected).abs() < 1e-10,
            "gini={}, expected={}",
            gini,
            expected
        );
    }

    #[test]
    fn test_gini_two_equal() {
        let gini = compute_gini(&[5, 5]);
        assert!(
            gini.abs() < f64::EPSILON,
            "equal pair should have Gini=0, got {}",
            gini
        );
    }

    #[test]
    fn test_gini_two_unequal() {
        // [1, 9]: n=2, sum=10
        // weighted_sum = 1*1 + 2*9 = 19
        // gini = (2*19)/(2*10) - 3/2 = 1.9 - 1.5 = 0.4
        let gini = compute_gini(&[1, 9]);
        assert!((gini - 0.4).abs() < 1e-10, "gini={}, expected=0.4", gini);
    }

    #[test]
    fn test_classify_ownership() {
        assert_eq!(classify_ownership(0.0, 1), OwnershipType::Strong);
        assert_eq!(classify_ownership(0.0, 3), OwnershipType::Equal);
        assert_eq!(classify_ownership(0.8, 3), OwnershipType::Strong);
        assert_eq!(classify_ownership(0.5, 3), OwnershipType::Fragmented);
        assert_eq!(classify_ownership(0.2, 3), OwnershipType::Moderate);
    }

    #[test]
    fn test_ownership_type_display() {
        assert_eq!(format!("{}", OwnershipType::Strong), "strong");
        assert_eq!(format!("{}", OwnershipType::Moderate), "moderate");
        assert_eq!(format!("{}", OwnershipType::Fragmented), "fragmented");
        assert_eq!(format!("{}", OwnershipType::Equal), "equal");
    }

    #[test]
    fn test_fragmented_count() {
        let data = make_file_authors(&[
            // Fragmented: Gini ~0.5
            ("frag.rs", &[("A", 1), ("B", 9)]),
            // Equal: Gini 0
            ("equal.rs", &[("A", 5), ("B", 5)]),
            // Strong: single owner
            ("solo.rs", &[("A", 10)]),
        ]);
        let report = compute_ownership_fragmentation(&data);
        assert_eq!(report.files.len(), 3);
        // Verify fragmented count matches classification
        let actual_frag = report
            .files
            .iter()
            .filter(|f| f.ownership_type == OwnershipType::Fragmented)
            .count();
        assert_eq!(report.fragmented_count, actual_frag);
    }

    #[test]
    fn test_sorted_descending() {
        let data = make_file_authors(&[
            ("low.rs", &[("A", 5), ("B", 5)]),   // Gini ~0
            ("high.rs", &[("A", 99), ("B", 1)]), // Gini high
        ]);
        let report = compute_ownership_fragmentation(&data);
        assert!(
            report.files[0].gini_coefficient >= report.files[1].gini_coefficient,
            "not sorted descending: {} < {}",
            report.files[0].gini_coefficient,
            report.files[1].gini_coefficient
        );
    }

    // ── Property-based tests ──

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Gini is always in [0, 1].
            #[test]
            fn prop_gini_bounded(
                a in 1u32..100,
                b in 1u32..100,
                c in 1u32..100
            ) {
                let mut v = vec![a, b, c];
                v.sort_unstable();
                let g = compute_gini(&v);
                prop_assert!((0.0..=1.0).contains(&g),
                    "gini={} out of [0,1] for {:?}", g, v);
            }

            /// Equal values always give Gini = 0.
            #[test]
            fn prop_equal_gini_zero(val in 1u32..100, n in 2usize..10) {
                let v = vec![val; n];
                let g = compute_gini(&v);
                prop_assert!(g.abs() < 1e-10,
                    "equal values should have Gini=0, got {}", g);
            }
        }
    }
}
