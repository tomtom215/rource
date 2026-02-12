// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Change Propagation Prediction analysis.
//!
//! For each file, produces a ranked list of files most likely to need
//! concurrent modification, with confidence scores and transitive cascade depth.
//!
//! # Research Basis
//!
//! - Hassan & Holt (ICSM 2004, DOI: 10.1109/ICSM.2004.1357802) — change propagation prediction
//! - Zimmermann et al. (ESEC/FSE 2005, DOI: 10.1145/1081706.1081728) — association rules, ~70% precision
//!
//! # Novelty
//!
//! Transitive propagation depth computation and risk-weighted scoring have not
//! been combined in published work. Existing approaches predict direct propagation
//! only. This extension models cascading effects using truncated Markov chain
//! absorption theory.
//!
//! # Algorithm
//!
//! For file `f`, the propagation set with probabilities:
//!   `P(g needs change | f changed) = co_changes(f,g) / changes(f)`
//!
//! Propagation Risk Score:
//!   `PRS(f) = Σ P(g|f)` for `g` in top-K predicted files
//!
//! Expected Propagation Depth (truncated at depth D=3):
//!   Direct (depth 1): `Σ_g P(g|f)`
//!   Transitive (depth 2): `Σ_g Σ_h P(g|f) × P(h|g)`
//!   Computed using sparse matrix multiplication.
//!
//! # Complexity
//!
//! - Direct propagation: `O(E)` where `E` = coupling edges
//! - Transitive depth 2: `O(E × avg_degree)`
//! - Total: `O(E × D × avg_degree)` where `D` = max depth (default: 3)

use rustc_hash::FxHashMap;

use super::coupling::CouplingPair;

/// Maximum propagation depth for transitive cascade analysis.
const MAX_DEPTH: usize = 3;

/// Maximum number of predicted files per source file.
const TOP_K: usize = 10;

/// Per-file propagation prediction.
#[derive(Debug, Clone)]
pub struct FilePropagation {
    /// Source file path.
    pub path: String,
    /// Top-K predicted files with probabilities, sorted by P desc.
    pub predictions: Vec<(String, f64)>,
    /// Propagation Risk Score: sum of top-K probabilities.
    pub risk_score: f64,
    /// Expected Propagation Depth (truncated at `MAX_DEPTH`).
    pub expected_depth: f64,
    /// Number of files reachable at each depth level.
    pub depth_counts: Vec<u32>,
}

/// Aggregate propagation report.
#[derive(Debug, Clone)]
pub struct ChangePropagationReport {
    /// Per-file propagation predictions, sorted by `risk_score` descending.
    pub files: Vec<FilePropagation>,
    /// Average propagation risk across all files.
    pub avg_risk_score: f64,
    /// Average expected propagation depth.
    pub avg_expected_depth: f64,
    /// Files with highest cascade potential (`depth_counts[2] > 0`).
    pub cascade_count: u32,
}

/// Computes change propagation predictions from coupling data.
///
/// # Arguments
///
/// * `couplings` - Pre-computed coupling pairs
#[must_use]
pub fn compute_change_propagation(couplings: &[CouplingPair]) -> ChangePropagationReport {
    if couplings.is_empty() {
        return ChangePropagationReport {
            files: Vec::new(),
            avg_risk_score: 0.0,
            avg_expected_depth: 0.0,
            cascade_count: 0,
        };
    }

    // Build directed transition probability adjacency list.
    // For each file f, store (neighbor, P(neighbor | f)).
    let mut adj: FxHashMap<&str, Vec<(&str, f64)>> = FxHashMap::default();

    for pair in couplings {
        adj.entry(&pair.file_a)
            .or_default()
            .push((&pair.file_b, pair.confidence_ab));
        adj.entry(&pair.file_b)
            .or_default()
            .push((&pair.file_a, pair.confidence_ba));
    }

    let mut results: Vec<FilePropagation> = adj
        .keys()
        .map(|&file| compute_file_propagation(file, &adj))
        .collect();

    results.sort_unstable_by(|a, b| {
        b.risk_score
            .partial_cmp(&a.risk_score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    build_propagation_report(results)
}

/// Computes propagation metrics for a single file.
fn compute_file_propagation(
    file: &str,
    adj: &FxHashMap<&str, Vec<(&str, f64)>>,
) -> FilePropagation {
    let mut depth_counts = vec![0u32; MAX_DEPTH];
    let mut expected_depth = 0.0;

    // Depth 1: direct neighbors
    let direct = adj.get(file).cloned().unwrap_or_default();
    depth_counts[0] = direct.len() as u32;
    let depth1_sum: f64 = direct.iter().map(|(_, p)| p).sum();
    expected_depth += depth1_sum;

    // Depth 2+: transitive cascades
    if MAX_DEPTH >= 2 {
        let (d2_expected, d2_files) = compute_depth2_cascade(file, &direct, adj, &mut depth_counts);
        expected_depth += d2_expected;

        if MAX_DEPTH >= 3 {
            expected_depth +=
                compute_depth3_cascade(file, &direct, &d2_files, adj, &mut depth_counts);
        }
    }

    // Top-K predictions (sorted by probability)
    let mut predictions: Vec<(String, f64)> =
        direct.iter().map(|(g, p)| (g.to_string(), *p)).collect();
    predictions.sort_unstable_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
    predictions.truncate(TOP_K);

    let risk_score: f64 = predictions.iter().map(|(_, p)| p).sum();

    FilePropagation {
        path: file.to_string(),
        predictions,
        risk_score,
        expected_depth,
        depth_counts,
    }
}

/// Computes depth-2 transitive cascade (f → g → h).
/// Returns the expected depth contribution and the depth-2 file map.
fn compute_depth2_cascade<'a>(
    file: &str,
    direct: &[(&'a str, f64)],
    adj: &FxHashMap<&'a str, Vec<(&'a str, f64)>>,
    depth_counts: &mut [u32],
) -> (f64, FxHashMap<&'a str, f64>) {
    let mut depth2_files: FxHashMap<&str, f64> = FxHashMap::default();
    for &(g, p_g) in direct {
        if let Some(g_neighbors) = adj.get(g) {
            for &(h, p_h) in g_neighbors {
                if h != file {
                    *depth2_files.entry(h).or_insert(0.0) += p_g * p_h;
                }
            }
        }
    }
    // Remove files already at depth 1
    for &(g, _) in direct {
        depth2_files.remove(g);
    }
    depth_counts[1] = depth2_files.len() as u32;
    let depth2_sum: f64 = depth2_files.values().sum();
    (depth2_sum, depth2_files)
}

/// Computes depth-3 cascade (f → g → h → i).
fn compute_depth3_cascade(
    file: &str,
    direct: &[(&str, f64)],
    depth2_files: &FxHashMap<&str, f64>,
    adj: &FxHashMap<&str, Vec<(&str, f64)>>,
    depth_counts: &mut [u32],
) -> f64 {
    let mut depth3_count = 0u32;
    let mut depth3_sum = 0.0;
    for (&h, &p_fh) in depth2_files {
        if let Some(h_neighbors) = adj.get(h) {
            for &(i, p_i) in h_neighbors {
                if i != file
                    && !direct.iter().any(|(g, _)| *g == i)
                    && !depth2_files.contains_key(i)
                {
                    depth3_count += 1;
                    depth3_sum += p_fh * p_i;
                }
            }
        }
    }
    depth_counts[2] = depth3_count;
    depth3_sum
}

/// Builds the aggregate propagation report from sorted results.
fn build_propagation_report(results: Vec<FilePropagation>) -> ChangePropagationReport {
    let cascade_count = results
        .iter()
        .filter(|f| f.depth_counts.len() > 2 && f.depth_counts[2] > 0)
        .count() as u32;
    let avg_risk_score = if results.is_empty() {
        0.0
    } else {
        results.iter().map(|f| f.risk_score).sum::<f64>() / results.len() as f64
    };
    let avg_expected_depth = if results.is_empty() {
        0.0
    } else {
        results.iter().map(|f| f.expected_depth).sum::<f64>() / results.len() as f64
    };

    ChangePropagationReport {
        files: results,
        avg_risk_score,
        avg_expected_depth,
        cascade_count,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_pair(
        a: &str,
        b: &str,
        support: u32,
        total_a: u32,
        total_b: u32,
        n: u32,
    ) -> CouplingPair {
        let conf_ab = f64::from(support) / f64::from(total_a);
        let conf_ba = f64::from(support) / f64::from(total_b);
        let lift = f64::from(support) * f64::from(n) / (f64::from(total_a) * f64::from(total_b));
        CouplingPair {
            file_a: a.to_string(),
            file_b: b.to_string(),
            support,
            confidence_ab: conf_ab,
            confidence_ba: conf_ba,
            total_a,
            total_b,
            lift,
        }
    }

    #[test]
    fn test_empty_couplings() {
        let report = compute_change_propagation(&[]);
        assert!(report.files.is_empty());
        assert_eq!(report.avg_risk_score, 0.0);
    }

    #[test]
    fn test_single_pair() {
        let pairs = vec![make_pair("a.rs", "b.rs", 5, 10, 10, 20)];
        let report = compute_change_propagation(&pairs);

        assert_eq!(report.files.len(), 2);
        // a.rs should predict b.rs with P=0.5
        let a_file = report.files.iter().find(|f| f.path == "a.rs").unwrap();
        assert_eq!(a_file.predictions.len(), 1);
        assert_eq!(a_file.predictions[0].0, "b.rs");
        assert!((a_file.predictions[0].1 - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_transitive_chain() {
        // A↔B and B↔C, so A→B→C should create depth-2 cascade
        let pairs = vec![
            make_pair("a.rs", "b.rs", 8, 10, 10, 20),
            make_pair("b.rs", "c.rs", 6, 10, 10, 20),
        ];
        let report = compute_change_propagation(&pairs);

        let a_file = report.files.iter().find(|f| f.path == "a.rs").unwrap();
        // Depth 1: b.rs
        assert_eq!(a_file.depth_counts[0], 1);
        // Depth 2: c.rs (via b.rs)
        assert_eq!(a_file.depth_counts[1], 1);
    }

    #[test]
    fn test_expected_depth_positive() {
        let pairs = vec![make_pair("a.rs", "b.rs", 5, 10, 10, 20)];
        let report = compute_change_propagation(&pairs);

        for file in &report.files {
            assert!(file.expected_depth >= 0.0);
        }
    }

    #[test]
    fn test_predictions_sorted_by_probability() {
        let pairs = vec![
            make_pair("a.rs", "b.rs", 8, 10, 10, 20),
            make_pair("a.rs", "c.rs", 3, 10, 10, 20),
        ];
        let report = compute_change_propagation(&pairs);

        let a_file = report.files.iter().find(|f| f.path == "a.rs").unwrap();
        assert!(a_file.predictions.len() >= 2);
        assert!(a_file.predictions[0].1 >= a_file.predictions[1].1);
    }

    #[test]
    fn test_risk_score_equals_sum_of_predictions() {
        let pairs = vec![
            make_pair("a.rs", "b.rs", 8, 10, 10, 20),
            make_pair("a.rs", "c.rs", 3, 10, 10, 20),
        ];
        let report = compute_change_propagation(&pairs);

        let a_file = report.files.iter().find(|f| f.path == "a.rs").unwrap();
        let sum: f64 = a_file.predictions.iter().map(|(_, p)| p).sum();
        assert!((a_file.risk_score - sum).abs() < f64::EPSILON);
    }
}
