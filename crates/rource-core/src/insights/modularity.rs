// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Co-change modularity analysis (Design Structure Matrix).
//!
//! Compares the coupling structure revealed by co-change analysis against the
//! declared directory hierarchy. Measures how much coupling crosses directory
//! boundaries (architectural erosion) vs. stays within directories (good modularity).
//!
//! # Research Basis
//!
//! Silva et al. (2014) "Assessing Modularity Using Co-Change Clusters" (Modularity
//! 2014) validated on multiple large OSS projects. Files co-change coupled across
//! module boundaries account for ≥27.93% of all dependencies. `InSep` pairs have 190%
//! more co-changes than properly separated pairs.
//!
//! `MacCormack` et al. (2006) "Exploring the Structure of Complex Software Designs"
//! (Management Science 52(7), pp. 1015–1030) introduced the propagation cost metric
//! using Design Structure Matrices.
//!
//! # Algorithm
//!
//! 1. Build a co-change edge list from coupling pairs
//! 2. Extract top-level directory for each file
//! 3. Classify each edge as intra-module or cross-module
//! 4. Modularity index = 1.0 − (`cross_edges` / `total_edges`)
//!
//! # Complexity
//!
//! - O(E) where E = co-change edges (from finalized coupling pairs)

use rustc_hash::FxHashMap;

use super::coupling::CouplingPair;

/// Co-change modularity for a single directory.
#[derive(Debug, Clone)]
pub struct DirectoryModularity {
    /// Directory path.
    pub directory: String,
    /// Intra-directory co-change edges.
    pub internal_coupling: u32,
    /// Cross-directory co-change edges.
    pub external_coupling: u32,
    /// Modularity score: `internal / (internal + external)`.
    pub modularity_score: f64,
    /// Top externally-coupled directories sorted by edge count descending.
    pub top_external_deps: Vec<(String, u32)>,
}

/// Complete modularity report.
#[derive(Debug, Clone)]
pub struct ModularityReport {
    /// Overall modularity index: `1.0 − cross_ratio`.
    /// 1.0 = perfectly modular; 0.0 = everything coupled across boundaries.
    pub modularity_index: f64,
    /// Fraction of co-change edges that cross directory boundaries.
    pub cross_module_ratio: f64,
    /// Total intra-directory co-change edges.
    pub total_intra_edges: u32,
    /// Total cross-directory co-change edges.
    pub total_cross_edges: u32,
    /// Per-directory breakdown, sorted by `modularity_score` ascending (worst first).
    pub directories: Vec<DirectoryModularity>,
}

/// Computes modularity from finalized coupling pairs.
///
/// # Arguments
///
/// * `couplings` - Finalized co-change coupling pairs from `CouplingAccumulator`
#[must_use]
pub fn compute_modularity(couplings: &[CouplingPair]) -> ModularityReport {
    if couplings.is_empty() {
        return ModularityReport {
            modularity_index: 1.0, // vacuously modular
            cross_module_ratio: 0.0,
            total_intra_edges: 0,
            total_cross_edges: 0,
            directories: Vec::new(),
        };
    }

    let mut total_intra: u32 = 0;
    let mut total_cross: u32 = 0;

    // Per-directory: (internal_count, external_counts_by_dir)
    let mut dir_data: FxHashMap<String, (u32, FxHashMap<String, u32>)> = FxHashMap::default();

    for pair in couplings {
        let dir_a = extract_directory(&pair.file_a);
        let dir_b = extract_directory(&pair.file_b);

        if dir_a == dir_b {
            total_intra += 1;
            dir_data.entry(dir_a).or_default().0 += 1;
        } else {
            total_cross += 1;
            // Count external dep for both directories
            *dir_data
                .entry(dir_a.clone())
                .or_default()
                .1
                .entry(dir_b.clone())
                .or_insert(0) += 1;
            *dir_data
                .entry(dir_b)
                .or_default()
                .1
                .entry(dir_a)
                .or_insert(0) += 1;
        }
    }

    let total_edges = total_intra + total_cross;
    let cross_module_ratio = if total_edges > 0 {
        f64::from(total_cross) / f64::from(total_edges)
    } else {
        0.0
    };
    let modularity_index = 1.0 - cross_module_ratio;

    let mut directories: Vec<DirectoryModularity> = dir_data
        .into_iter()
        .map(|(directory, (internal, external_map))| {
            let external: u32 = external_map.values().sum();
            let total = internal + external;
            let modularity_score = if total > 0 {
                f64::from(internal) / f64::from(total)
            } else {
                1.0
            };

            let mut top_external_deps: Vec<(String, u32)> = external_map.into_iter().collect();
            top_external_deps.sort_by(|a, b| b.1.cmp(&a.1));
            top_external_deps.truncate(5);

            DirectoryModularity {
                directory,
                internal_coupling: internal,
                external_coupling: external,
                modularity_score,
                top_external_deps,
            }
        })
        .collect();

    // Sort by modularity ascending (worst directories first)
    directories.sort_by(|a, b| {
        a.modularity_score
            .partial_cmp(&b.modularity_score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    ModularityReport {
        modularity_index,
        cross_module_ratio,
        total_intra_edges: total_intra,
        total_cross_edges: total_cross,
        directories,
    }
}

/// Extracts the top-level directory from a file path.
fn extract_directory(path: &str) -> String {
    path.split('/')
        .next()
        .filter(|_| path.contains('/'))
        .unwrap_or(".")
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_coupling(a: &str, b: &str, support: u32) -> CouplingPair {
        CouplingPair {
            file_a: a.to_string(),
            file_b: b.to_string(),
            support,
            confidence_ab: 0.0,
            confidence_ba: 0.0,
            total_a: support,
            total_b: support,
        }
    }

    #[test]
    fn test_perfect_modularity() {
        // All co-changes within same directory
        let couplings = vec![
            make_coupling("src/a.rs", "src/b.rs", 5),
            make_coupling("tests/c.rs", "tests/d.rs", 3),
        ];
        let report = compute_modularity(&couplings);
        assert!(
            (report.modularity_index - 1.0).abs() < f64::EPSILON,
            "index={}, expected=1.0",
            report.modularity_index
        );
        assert_eq!(report.total_intra_edges, 2);
        assert_eq!(report.total_cross_edges, 0);
    }

    #[test]
    fn test_zero_modularity() {
        // All co-changes cross directories
        let couplings = vec![
            make_coupling("src/a.rs", "tests/b.rs", 5),
            make_coupling("src/c.rs", "docs/d.rs", 3),
        ];
        let report = compute_modularity(&couplings);
        assert!(
            report.modularity_index.abs() < f64::EPSILON,
            "index={}, expected=0.0",
            report.modularity_index
        );
        assert_eq!(report.total_intra_edges, 0);
        assert_eq!(report.total_cross_edges, 2);
    }

    #[test]
    fn test_mixed_modularity() {
        // 2 intra + 1 cross = 2/3 modularity
        let couplings = vec![
            make_coupling("src/a.rs", "src/b.rs", 5),
            make_coupling("tests/c.rs", "tests/d.rs", 3),
            make_coupling("src/e.rs", "tests/f.rs", 2),
        ];
        let report = compute_modularity(&couplings);
        let expected = 2.0 / 3.0;
        assert!(
            (report.modularity_index - expected).abs() < 1e-10,
            "index={}, expected={}",
            report.modularity_index,
            expected
        );
    }

    #[test]
    fn test_single_directory() {
        // All files in root → all edges intra → index = 1.0
        let couplings = vec![make_coupling("a.rs", "b.rs", 5)];
        let report = compute_modularity(&couplings);
        assert!(
            (report.modularity_index - 1.0).abs() < f64::EPSILON,
            "root files should be intra-module"
        );
    }

    #[test]
    fn test_directory_extraction() {
        assert_eq!(extract_directory("src/foo/bar.rs"), "src");
        assert_eq!(extract_directory("tests/unit.rs"), "tests");
        assert_eq!(extract_directory("README.md"), ".");
    }

    #[test]
    fn test_empty_report() {
        let report = compute_modularity(&[]);
        assert!(
            (report.modularity_index - 1.0).abs() < f64::EPSILON,
            "empty = vacuously modular"
        );
        assert_eq!(report.total_intra_edges, 0);
        assert_eq!(report.total_cross_edges, 0);
    }

    #[test]
    fn test_top_external_deps() {
        // src coupled with tests(5x) and docs(2x) → tests listed first
        let couplings = vec![
            make_coupling("src/a.rs", "tests/b.rs", 5),
            make_coupling("src/c.rs", "tests/d.rs", 5),
            make_coupling("src/e.rs", "tests/f.rs", 5),
            make_coupling("src/g.rs", "tests/h.rs", 5),
            make_coupling("src/i.rs", "tests/j.rs", 5),
            make_coupling("src/k.rs", "docs/l.rs", 2),
            make_coupling("src/m.rs", "docs/n.rs", 2),
        ];
        let report = compute_modularity(&couplings);
        let src = report
            .directories
            .iter()
            .find(|d| d.directory == "src")
            .unwrap();
        assert!(!src.top_external_deps.is_empty());
        assert_eq!(src.top_external_deps[0].0, "tests");
        assert_eq!(src.top_external_deps[0].1, 5);
    }

    #[test]
    fn test_per_directory_scores() {
        // src: 1 internal, 1 external → score = 0.5
        // tests: 0 internal, 1 external → score = 0.0
        let couplings = vec![
            make_coupling("src/a.rs", "src/b.rs", 3),
            make_coupling("src/c.rs", "tests/d.rs", 2),
        ];
        let report = compute_modularity(&couplings);
        let src = report
            .directories
            .iter()
            .find(|d| d.directory == "src")
            .unwrap();
        assert!(
            (src.modularity_score - 0.5).abs() < 1e-10,
            "src score={}, expected=0.5",
            src.modularity_score
        );
        let tests = report
            .directories
            .iter()
            .find(|d| d.directory == "tests")
            .unwrap();
        assert!(
            tests.modularity_score.abs() < f64::EPSILON,
            "tests score={}, expected=0.0",
            tests.modularity_score
        );
    }

    // ── Mutation-killing tests ──────────────────────────────────────

    #[test]
    fn test_dir_equality_check() {
        // Kills: replace `==` with `!=` in `if dir_a == dir_b`
        // Same-dir pair MUST count as intra, not cross.
        let couplings = vec![make_coupling("src/a.rs", "src/b.rs", 1)];
        let report = compute_modularity(&couplings);
        assert_eq!(report.total_intra_edges, 1);
        assert_eq!(report.total_cross_edges, 0);
        assert!(
            (report.modularity_index - 1.0).abs() < f64::EPSILON,
            "same-dir must be intra"
        );
    }

    #[test]
    fn test_cross_module_ratio_division_exact() {
        // Kills: replace `/` with `*` in `f64::from(total_cross) / f64::from(total_edges)`
        // 1 cross out of 3 total → ratio = 1/3, not 1*3
        let couplings = vec![
            make_coupling("src/a.rs", "src/b.rs", 1),
            make_coupling("src/c.rs", "src/d.rs", 1),
            make_coupling("src/e.rs", "tests/f.rs", 1),
        ];
        let report = compute_modularity(&couplings);
        let expected_ratio = 1.0 / 3.0;
        assert!(
            (report.cross_module_ratio - expected_ratio).abs() < 1e-10,
            "ratio={}, expected={}",
            report.cross_module_ratio,
            expected_ratio
        );
    }

    #[test]
    fn test_modularity_index_subtraction() {
        // Kills: replace `-` with `+` in `1.0 - cross_module_ratio`
        // ratio = 1/3 → index = 1-1/3 = 2/3, not 1+1/3 = 4/3
        let couplings = vec![
            make_coupling("src/a.rs", "src/b.rs", 1),
            make_coupling("src/c.rs", "src/d.rs", 1),
            make_coupling("src/e.rs", "tests/f.rs", 1),
        ];
        let report = compute_modularity(&couplings);
        let expected_index = 2.0 / 3.0;
        assert!(
            (report.modularity_index - expected_index).abs() < 1e-10,
            "index={}, expected={}",
            report.modularity_index,
            expected_index
        );
        assert!(report.modularity_index <= 1.0, "index must be <= 1.0");
    }

    #[test]
    fn test_per_dir_modularity_score_division() {
        // Kills: replace `/` with `*` in `f64::from(internal) / f64::from(total)`
        // src: 2 internal, 1 external → score = 2/3, not 2*3=6
        let couplings = vec![
            make_coupling("src/a.rs", "src/b.rs", 1),
            make_coupling("src/c.rs", "src/d.rs", 1),
            make_coupling("src/e.rs", "tests/f.rs", 1),
        ];
        let report = compute_modularity(&couplings);
        let src = report
            .directories
            .iter()
            .find(|d| d.directory == "src")
            .unwrap();
        let expected = 2.0 / 3.0;
        assert!(
            (src.modularity_score - expected).abs() < 1e-10,
            "src.modularity_score={}, expected={}",
            src.modularity_score,
            expected
        );
        assert!(src.modularity_score <= 1.0, "score must be <= 1.0");
    }

    #[test]
    fn test_total_edges_guard_with_single_edge() {
        // Kills: replace `> 0` with `> 1` in `if total_edges > 0`
        // Exactly 1 total edge → guard must pass.
        let couplings = vec![make_coupling("src/a.rs", "tests/b.rs", 1)];
        let report = compute_modularity(&couplings);
        // total_edges = 1, all cross → ratio = 1.0
        assert!(
            (report.cross_module_ratio - 1.0).abs() < f64::EPSILON,
            "single cross edge: ratio={}, expected=1.0",
            report.cross_module_ratio
        );
    }

    #[test]
    fn test_per_dir_total_guard_with_single_edge() {
        // Kills: replace `> 0` with `> 1` in per-dir `if total > 0`
        // Directory with exactly 1 edge (all external) → score = 0.0
        let couplings = vec![make_coupling("src/a.rs", "tests/b.rs", 1)];
        let report = compute_modularity(&couplings);
        let tests_dir = report
            .directories
            .iter()
            .find(|d| d.directory == "tests")
            .unwrap();
        // tests: 0 internal, 1 external → total=1, score = 0/1 = 0.0
        assert!(
            tests_dir.modularity_score.abs() < f64::EPSILON,
            "tests score={}, expected=0.0",
            tests_dir.modularity_score
        );
        assert_eq!(tests_dir.internal_coupling, 0);
        assert_eq!(tests_dir.external_coupling, 1);
    }

    #[test]
    fn test_intra_cross_counts_exact() {
        // Kills: mutants that swap `+= 1` to `+= 0` or `-= 1` on total_intra/total_cross
        // 2 intra + 2 cross = 4 total
        let couplings = vec![
            make_coupling("src/a.rs", "src/b.rs", 1),
            make_coupling("tests/c.rs", "tests/d.rs", 1),
            make_coupling("src/e.rs", "tests/f.rs", 1),
            make_coupling("src/g.rs", "docs/h.rs", 1),
        ];
        let report = compute_modularity(&couplings);
        assert_eq!(
            report.total_intra_edges, 2,
            "expected exactly 2 intra edges"
        );
        assert_eq!(
            report.total_cross_edges, 2,
            "expected exactly 2 cross edges"
        );
    }

    #[test]
    fn test_extract_directory_with_slash() {
        // Kills: negate `path.contains('/')` filter
        // File with slash → first component, file without slash → "."
        assert_eq!(extract_directory("src/main.rs"), "src");
        assert_eq!(extract_directory("nodir.txt"), ".");
    }

    #[test]
    fn test_external_coupling_counts_both_directions() {
        // Kills: removing one of the two `dir_data.entry(dir_b)` / `dir_data.entry(dir_a)` blocks
        // Cross-edge src↔tests should add to BOTH src and tests external counts.
        let couplings = vec![make_coupling("src/a.rs", "tests/b.rs", 1)];
        let report = compute_modularity(&couplings);
        let src = report
            .directories
            .iter()
            .find(|d| d.directory == "src")
            .unwrap();
        let tests_dir = report
            .directories
            .iter()
            .find(|d| d.directory == "tests")
            .unwrap();
        assert_eq!(src.external_coupling, 1, "src should have 1 external edge");
        assert_eq!(
            tests_dir.external_coupling, 1,
            "tests should have 1 external edge"
        );
    }

    #[test]
    fn test_directories_sorted_ascending_by_score() {
        // Kills: swap sort order (a↔b in partial_cmp)
        let couplings = vec![
            make_coupling("src/a.rs", "src/b.rs", 1), // src: 1 intra, 0 cross → score 1.0
            make_coupling("tests/c.rs", "docs/d.rs", 1), // tests & docs: 0 intra, 1 cross → score 0.0
        ];
        let report = compute_modularity(&couplings);
        assert!(report.directories.len() >= 2);
        // First element (worst) should have lowest score
        assert!(
            report.directories[0].modularity_score
                <= report.directories.last().unwrap().modularity_score,
            "directories not sorted ascending: first={}, last={}",
            report.directories[0].modularity_score,
            report.directories.last().unwrap().modularity_score
        );
    }

    // ── Property-based tests ────────────────────────────────────────

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        /// Strategy to generate random coupling pairs.
        fn arb_couplings() -> impl Strategy<Value = Vec<CouplingPair>> {
            let dirs = ["src", "tests", "docs", "lib"];
            proptest::collection::vec(
                (0usize..4, 0usize..3, 0usize..4, 0usize..3, 1u32..10),
                1..=10,
            )
            .prop_map(move |specs| {
                specs
                    .into_iter()
                    .map(|(d1, f1, d2, f2, support)| {
                        let file_a = format!("{}/f{f1}.rs", dirs[d1]);
                        let file_b = format!("{}/f{f2}.rs", dirs[d2]);
                        CouplingPair {
                            file_a,
                            file_b,
                            support,
                            confidence_ab: 0.5,
                            confidence_ba: 0.5,
                            total_a: support * 2,
                            total_b: support * 2,
                        }
                    })
                    .collect()
            })
        }

        proptest! {
            /// Modularity index is always in [0, 1].
            #[test]
            fn prop_modularity_bounded(couplings in arb_couplings()) {
                let report = compute_modularity(&couplings);
                prop_assert!(
                    report.modularity_index >= -f64::EPSILON,
                    "index={} < 0",
                    report.modularity_index
                );
                prop_assert!(
                    report.modularity_index <= 1.0 + f64::EPSILON,
                    "index={} > 1",
                    report.modularity_index
                );
            }

            /// Intra + cross always equals total edges.
            #[test]
            fn prop_edge_conservation(couplings in arb_couplings()) {
                let report = compute_modularity(&couplings);
                prop_assert_eq!(
                    report.total_intra_edges + report.total_cross_edges,
                    couplings.len() as u32,
                    "intra({}) + cross({}) != total({})",
                    report.total_intra_edges, report.total_cross_edges, couplings.len()
                );
            }

            /// Cross module ratio is always in [0, 1].
            #[test]
            fn prop_cross_ratio_bounded(couplings in arb_couplings()) {
                let report = compute_modularity(&couplings);
                prop_assert!(
                    report.cross_module_ratio >= -f64::EPSILON,
                    "ratio={} < 0",
                    report.cross_module_ratio
                );
                prop_assert!(
                    report.cross_module_ratio <= 1.0 + f64::EPSILON,
                    "ratio={} > 1",
                    report.cross_module_ratio
                );
            }

            /// modularity_index = 1.0 - cross_module_ratio always holds.
            #[test]
            fn prop_index_eq_one_minus_ratio(couplings in arb_couplings()) {
                let report = compute_modularity(&couplings);
                let expected = 1.0 - report.cross_module_ratio;
                prop_assert!(
                    (report.modularity_index - expected).abs() < 1e-10,
                    "index={}, 1-ratio={}",
                    report.modularity_index, expected
                );
            }

            /// Per-directory modularity scores are always in [0, 1].
            #[test]
            fn prop_dir_scores_bounded(couplings in arb_couplings()) {
                let report = compute_modularity(&couplings);
                for dir in &report.directories {
                    prop_assert!(
                        dir.modularity_score >= -f64::EPSILON,
                        "dir {} score={} < 0",
                        dir.directory, dir.modularity_score
                    );
                    prop_assert!(
                        dir.modularity_score <= 1.0 + f64::EPSILON,
                        "dir {} score={} > 1",
                        dir.directory, dir.modularity_score
                    );
                }
            }
        }
    }
}
