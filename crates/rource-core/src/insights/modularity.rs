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
}
