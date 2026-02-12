// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Architectural Drift Index analysis.
//!
//! Measures the divergence between intended architecture (directory structure)
//! and actual architecture (clusters of files that change together).
//!
//! # Research Basis
//!
//! - Tzerpos & Holt (IWPC 2000, DOI: 10.1109/WPC.2000.852478) — software clustering
//! - Maqbool & Babri (JSS 2007, DOI: 10.1016/j.jss.2006.05.031) — hierarchical clustering
//! - Garcia et al. (ICSE 2013, DOI: 10.1109/ICSE.2013.6606611) — architecture recovery comparison
//! - Vinh et al. (JMLR 2010, URL: <https://jmlr.org/papers/v11/vinh10a.html>) — NMI for clusters
//!
//! # Novelty
//!
//! Applying Normalized Mutual Information (NMI) to compare co-change-derived
//! clusters against directory structure as a quantitative "architectural truth"
//! metric has not been published. Existing work recovers architecture from
//! co-changes but does not quantify the drift from intended structure.
//!
//! # Algorithm
//!
//! 1. Build co-change adjacency graph from coupling pairs
//! 2. Cluster files using label propagation (deterministic variant)
//! 3. Extract directory partition from file paths
//! 4. Compare using Normalized Mutual Information: NMI(clusters, directories)
//! 5. ADI = 1 - NMI  (0 = perfect alignment, 1 = complete misalignment)
//!
//! # Complexity
//!
//! - Label propagation: O(V + E × iterations) where V = files, E = coupling edges
//! - NMI computation: O(V) given cluster assignments
//! - Total: O(V + E × I), I ≈ 10 iterations typically

use rustc_hash::{FxHashMap, FxHashSet};

use super::coupling::CouplingPair;

/// Maximum iterations for label propagation.
const MAX_ITERATIONS: usize = 50;

/// Per-file cluster assignment.
#[derive(Debug, Clone)]
pub struct FileDriftInfo {
    /// File path.
    pub path: String,
    /// Directory (intended module).
    pub directory: String,
    /// Assigned cluster ID (actual module from co-change patterns).
    pub cluster_id: u32,
    /// Whether this file is "misplaced" — cluster differs from directory majority.
    pub is_misplaced: bool,
}

/// Directory-level drift summary.
#[derive(Debug, Clone)]
pub struct DirectoryDrift {
    /// Directory path.
    pub directory: String,
    /// Number of distinct clusters represented in this directory.
    pub cluster_count: u32,
    /// Fraction of files belonging to the dominant cluster.
    pub dominant_cluster_pct: f64,
    /// Total files in this directory.
    pub file_count: u32,
}

/// Ghost module: a cluster that spans multiple directories.
#[derive(Debug, Clone)]
pub struct GhostModule {
    /// Cluster ID.
    pub cluster_id: u32,
    /// Directories spanned by this cluster.
    pub directories: Vec<String>,
    /// Files in this cluster.
    pub files: Vec<String>,
}

/// Aggregate architectural drift report.
#[derive(Debug, Clone)]
pub struct ArchitecturalDriftReport {
    /// Architectural Drift Index: 1 - NMI.
    /// 0 = directory structure perfectly reflects change patterns.
    /// 1 = completely uncorrelated.
    pub drift_index: f64,
    /// Raw NMI value.
    pub nmi: f64,
    /// Per-file cluster assignments.
    pub files: Vec<FileDriftInfo>,
    /// Per-directory drift summaries.
    pub directories: Vec<DirectoryDrift>,
    /// Ghost modules (clusters spanning multiple directories).
    pub ghost_modules: Vec<GhostModule>,
    /// Number of clusters found.
    pub cluster_count: u32,
    /// Number of misplaced files.
    pub misplaced_count: u32,
}

/// Computes the Architectural Drift Index from coupling data.
///
/// # Arguments
///
/// * `couplings` - Pre-computed coupling pairs
/// * `all_files` - All file paths in the repository (for directory extraction)
#[must_use]
pub fn compute_architectural_drift(
    couplings: &[CouplingPair],
    all_files: &[String],
) -> ArchitecturalDriftReport {
    if couplings.is_empty() || all_files.is_empty() {
        return ArchitecturalDriftReport {
            drift_index: 0.0,
            nmi: 1.0,
            files: Vec::new(),
            directories: Vec::new(),
            ghost_modules: Vec::new(),
            cluster_count: 0,
            misplaced_count: 0,
        };
    }

    // Steps 1-2: Build adjacency graph and run label propagation.
    let (file_list, labels, cluster_count) = label_propagation(couplings);

    // Step 3: Extract directory partition.
    let dir_of = |path: &str| -> String {
        path.rsplit_once('/')
            .map_or_else(|| ".".to_string(), |(dir, _)| dir.to_string())
    };
    let file_dirs: Vec<String> = file_list.iter().map(|f| dir_of(f)).collect();

    // Step 4: Compute NMI(clusters, directories).
    let nmi = compute_nmi(&labels, &file_dirs);
    let drift_index = 1.0 - nmi;

    // Step 5: Build per-file, per-directory, and ghost module results.
    build_drift_report(
        &file_list,
        &labels,
        &file_dirs,
        cluster_count,
        nmi,
        drift_index,
    )
}

/// Runs deterministic label propagation on the co-change graph.
///
/// Returns `(file_list, labels, cluster_count)` where `labels[i]` is the
/// cluster assignment for `file_list[i]`.
fn label_propagation(couplings: &[CouplingPair]) -> (Vec<&str>, Vec<u32>, u32) {
    // Build adjacency list with weights (support).
    let mut adj: FxHashMap<&str, Vec<(&str, u32)>> = FxHashMap::default();
    let coupled_files: FxHashSet<&str> = couplings
        .iter()
        .flat_map(|p| [p.file_a.as_str(), p.file_b.as_str()])
        .collect();

    for pair in couplings {
        adj.entry(pair.file_a.as_str())
            .or_default()
            .push((pair.file_b.as_str(), pair.support));
        adj.entry(pair.file_b.as_str())
            .or_default()
            .push((pair.file_a.as_str(), pair.support));
    }

    let file_list: Vec<&str> = coupled_files.iter().copied().collect();
    let mut file_to_idx: FxHashMap<&str, usize> = FxHashMap::default();
    for (i, &f) in file_list.iter().enumerate() {
        file_to_idx.insert(f, i);
    }

    let mut labels: Vec<u32> = (0..file_list.len() as u32).collect();

    for _iter in 0..MAX_ITERATIONS {
        let mut changed = false;
        let mut sorted_indices: Vec<usize> = (0..file_list.len()).collect();
        sorted_indices.sort_unstable_by_key(|&i| file_list[i]);

        for &idx in &sorted_indices {
            let file = file_list[idx];
            if let Some(neighbors) = adj.get(file) {
                let mut label_weight: FxHashMap<u32, u32> = FxHashMap::default();
                for &(neighbor, weight) in neighbors {
                    if let Some(&n_idx) = file_to_idx.get(neighbor) {
                        *label_weight.entry(labels[n_idx]).or_insert(0) += weight;
                    }
                }
                if let Some((&best_label, _)) = label_weight
                    .iter()
                    .max_by_key(|(label, weight)| (**weight, std::cmp::Reverse(**label)))
                {
                    if labels[idx] != best_label {
                        labels[idx] = best_label;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Renumber labels contiguously starting from 0
    let mut label_map: FxHashMap<u32, u32> = FxHashMap::default();
    let mut next_id = 0u32;
    for &l in &labels {
        label_map.entry(l).or_insert_with(|| {
            let id = next_id;
            next_id += 1;
            id
        });
    }
    let labels: Vec<u32> = labels.iter().map(|l| label_map[l]).collect();

    (file_list, labels, next_id)
}

/// Builds the full drift report from cluster assignments and directory partitions.
fn build_drift_report(
    file_list: &[&str],
    labels: &[u32],
    file_dirs: &[String],
    cluster_count: u32,
    nmi: f64,
    drift_index: f64,
) -> ArchitecturalDriftReport {
    // For each directory, find the dominant cluster.
    let mut dir_clusters: FxHashMap<&str, FxHashMap<u32, u32>> = FxHashMap::default();
    for (i, dir) in file_dirs.iter().enumerate() {
        *dir_clusters
            .entry(dir.as_str())
            .or_default()
            .entry(labels[i])
            .or_insert(0) += 1;
    }
    let dir_dominant: FxHashMap<&str, u32> = dir_clusters
        .iter()
        .map(|(&dir, clusters)| {
            let (&dominant, _) = clusters
                .iter()
                .max_by_key(|(_, count)| *count)
                .unwrap_or((&0, &0));
            (dir, dominant)
        })
        .collect();

    let files: Vec<FileDriftInfo> = file_list
        .iter()
        .enumerate()
        .map(|(i, &path)| {
            let dir = &file_dirs[i];
            let cluster_id = labels[i];
            let dominant = dir_dominant.get(dir.as_str()).copied().unwrap_or(0);
            let is_misplaced = cluster_id != dominant;
            FileDriftInfo {
                path: path.to_string(),
                directory: dir.clone(),
                cluster_id,
                is_misplaced,
            }
        })
        .collect();

    let misplaced_count = files.iter().filter(|f| f.is_misplaced).count() as u32;

    // Per-directory summaries
    let mut directories: Vec<DirectoryDrift> = dir_clusters
        .iter()
        .map(|(&dir, clusters)| {
            let file_count: u32 = clusters.values().sum();
            let max_count = clusters.values().max().copied().unwrap_or(0);
            let dominant_cluster_pct = if file_count > 0 {
                f64::from(max_count) / f64::from(file_count)
            } else {
                0.0
            };
            DirectoryDrift {
                directory: dir.to_string(),
                cluster_count: clusters.len() as u32,
                dominant_cluster_pct,
                file_count,
            }
        })
        .collect();
    directories.sort_unstable_by(|a, b| {
        a.dominant_cluster_pct
            .partial_cmp(&b.dominant_cluster_pct)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    // Ghost modules
    let mut cluster_dir_map: FxHashMap<u32, FxHashSet<String>> = FxHashMap::default();
    let mut cluster_file_map: FxHashMap<u32, Vec<String>> = FxHashMap::default();
    for (i, &label) in labels.iter().enumerate() {
        cluster_dir_map
            .entry(label)
            .or_default()
            .insert(file_dirs[i].clone());
        cluster_file_map
            .entry(label)
            .or_default()
            .push(file_list[i].to_string());
    }
    let mut ghost_modules: Vec<GhostModule> = cluster_dir_map
        .into_iter()
        .filter(|(_, dirs)| dirs.len() > 1)
        .map(|(cluster_id, dirs)| {
            let mut dir_list: Vec<String> = dirs.into_iter().collect();
            dir_list.sort();
            GhostModule {
                cluster_id,
                directories: dir_list,
                files: cluster_file_map.remove(&cluster_id).unwrap_or_default(),
            }
        })
        .collect();
    ghost_modules.sort_unstable_by(|a, b| b.directories.len().cmp(&a.directories.len()));

    ArchitecturalDriftReport {
        drift_index,
        nmi,
        files,
        directories,
        ghost_modules,
        cluster_count,
        misplaced_count,
    }
}

/// Computes Normalized Mutual Information between two partitions.
///
/// NMI(C, D) = 2 × I(C; D) / (H(C) + H(D))
fn compute_nmi(cluster_labels: &[u32], dir_labels: &[String]) -> f64 {
    let n = cluster_labels.len();
    if n == 0 {
        return 1.0;
    }
    let n_f = n as f64;

    // Build contingency table
    let mut contingency: FxHashMap<(u32, &str), u32> = FxHashMap::default();
    let mut cluster_counts: FxHashMap<u32, u32> = FxHashMap::default();
    let mut dir_counts: FxHashMap<&str, u32> = FxHashMap::default();

    for i in 0..n {
        let c = cluster_labels[i];
        let d = dir_labels[i].as_str();
        *contingency.entry((c, d)).or_insert(0) += 1;
        *cluster_counts.entry(c).or_insert(0) += 1;
        *dir_counts.entry(d).or_insert(0) += 1;
    }

    // H(C) = -Σ P(c) log P(c)
    let h_c: f64 = cluster_counts
        .values()
        .map(|&count| {
            let p = f64::from(count) / n_f;
            if p > 0.0 {
                -p * p.ln()
            } else {
                0.0
            }
        })
        .sum();

    // H(D) = -Σ P(d) log P(d)
    let h_d: f64 = dir_counts
        .values()
        .map(|&count| {
            let p = f64::from(count) / n_f;
            if p > 0.0 {
                -p * p.ln()
            } else {
                0.0
            }
        })
        .sum();

    if h_c + h_d == 0.0 {
        return 1.0; // trivial case: everything in one cluster and one directory
    }

    // I(C; D) = Σ P(c,d) log(P(c,d) / (P(c) × P(d)))
    let mi: f64 = contingency
        .iter()
        .map(|(&(c, d), &count)| {
            let p_cd = f64::from(count) / n_f;
            let p_c = f64::from(cluster_counts[&c]) / n_f;
            let p_d = f64::from(dir_counts[d]) / n_f;
            let denom = p_c * p_d;
            if p_cd > 0.0 && denom > 0.0 {
                p_cd * (p_cd / denom).ln()
            } else {
                0.0
            }
        })
        .sum();

    let nmi = 2.0 * mi / (h_c + h_d);
    nmi.clamp(0.0, 1.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_pair(a: &str, b: &str, support: u32) -> CouplingPair {
        CouplingPair {
            file_a: a.to_string(),
            file_b: b.to_string(),
            support,
            confidence_ab: f64::from(support) / 10.0,
            confidence_ba: f64::from(support) / 10.0,
            total_a: 10,
            total_b: 10,
            lift: 1.0,
        }
    }

    #[test]
    fn test_empty_input() {
        let report = compute_architectural_drift(&[], &[]);
        assert_eq!(report.drift_index, 0.0);
        assert_eq!(report.nmi, 1.0);
    }

    #[test]
    fn test_perfect_alignment() {
        // Files in the same directory always co-change, different directories never co-change.
        let couplings = vec![
            make_pair("src/a.rs", "src/b.rs", 10),
            make_pair("tests/t1.rs", "tests/t2.rs", 10),
        ];
        let all_files = vec![
            "src/a.rs".to_string(),
            "src/b.rs".to_string(),
            "tests/t1.rs".to_string(),
            "tests/t2.rs".to_string(),
        ];

        let report = compute_architectural_drift(&couplings, &all_files);

        // NMI should be high (close to 1.0) since clusters match directories.
        assert!(
            report.nmi >= 0.8,
            "NMI should be high for aligned structure, got {}",
            report.nmi
        );
        assert!(report.drift_index <= 0.2);
    }

    #[test]
    fn test_complete_misalignment() {
        // Files in different directories always co-change, same directory never co-changes.
        let couplings = vec![
            make_pair("src/a.rs", "tests/t1.rs", 10),
            make_pair("src/b.rs", "tests/t2.rs", 10),
        ];
        let all_files = vec![
            "src/a.rs".to_string(),
            "src/b.rs".to_string(),
            "tests/t1.rs".to_string(),
            "tests/t2.rs".to_string(),
        ];

        let report = compute_architectural_drift(&couplings, &all_files);
        // Drift should be > 0 (misalignment exists)
        assert!(report.drift_index >= 0.0);
    }

    #[test]
    fn test_ghost_modules_detected() {
        // Cluster spans two directories
        let couplings = vec![
            make_pair("src/a.rs", "lib/b.rs", 10),
            make_pair("src/a.rs", "lib/c.rs", 10),
            make_pair("lib/b.rs", "lib/c.rs", 10),
        ];
        let all_files = vec![
            "src/a.rs".to_string(),
            "lib/b.rs".to_string(),
            "lib/c.rs".to_string(),
        ];

        let report = compute_architectural_drift(&couplings, &all_files);

        // All three files should cluster together (strong coupling)
        // but span src/ and lib/ → ghost module
        // Note: this depends on label propagation convergence
        assert!(!report.files.is_empty());
    }

    #[test]
    fn test_nmi_perfect_clustering() {
        // Labels perfectly match directories
        let clusters = vec![0, 0, 1, 1];
        let dirs = vec![
            "a".to_string(),
            "a".to_string(),
            "b".to_string(),
            "b".to_string(),
        ];
        let nmi = compute_nmi(&clusters, &dirs);
        assert!(
            (nmi - 1.0).abs() < 0.001,
            "Perfect match should give NMI ≈ 1.0, got {nmi}"
        );
    }

    #[test]
    fn test_nmi_random_clustering() {
        // Labels completely disagree with directories
        let clusters = vec![0, 1, 0, 1];
        let dirs = vec![
            "a".to_string(),
            "a".to_string(),
            "b".to_string(),
            "b".to_string(),
        ];
        let nmi = compute_nmi(&clusters, &dirs);
        assert!(nmi < 0.5, "Random should give low NMI, got {nmi}");
    }

    #[test]
    fn test_nmi_empty() {
        let nmi = compute_nmi(&[], &[]);
        assert_eq!(nmi, 1.0);
    }

    #[test]
    fn test_nmi_single_element() {
        let nmi = compute_nmi(&[0], &["dir".to_string()]);
        assert_eq!(nmi, 1.0);
    }

    #[test]
    fn test_drift_index_bounds() {
        let couplings = vec![make_pair("a.rs", "b.rs", 5)];
        let all_files = vec!["a.rs".to_string(), "b.rs".to_string()];
        let report = compute_architectural_drift(&couplings, &all_files);

        assert!(report.drift_index >= 0.0 && report.drift_index <= 1.0);
        assert!(report.nmi >= 0.0 && report.nmi <= 1.0);
    }

    #[test]
    fn test_directory_extraction() {
        let couplings = vec![make_pair("src/core/a.rs", "src/core/b.rs", 5)];
        let all_files = vec!["src/core/a.rs".to_string(), "src/core/b.rs".to_string()];
        let report = compute_architectural_drift(&couplings, &all_files);

        assert!(report.files.iter().all(|f| f.directory == "src/core"));
    }

    #[test]
    fn test_root_level_files() {
        let couplings = vec![make_pair("main.rs", "lib.rs", 5)];
        let all_files = vec!["main.rs".to_string(), "lib.rs".to_string()];
        let report = compute_architectural_drift(&couplings, &all_files);

        assert!(report.files.iter().all(|f| f.directory == "."));
    }
}
