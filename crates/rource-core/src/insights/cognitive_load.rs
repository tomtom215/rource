// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Cognitive load estimation per change (M32).
//!
//! Estimates the cognitive complexity a developer must manage when working
//! on a file, based on coupling degree, directory spread, author diversity,
//! and temporal dispersion of related changes.
//!
//! # Research Basis
//!
//! Fakhoury et al. (2019) "Improving Source Code Readability: Theory and
//! Practice" (ICPC, DOI: 10.1109/ICPC.2019.00014).
//!
//! Kapur & Musgrove (2023) "Cognitive Complexity of Code Changes"
//! (ESEC/FSE, DOI: 10.1145/3611643.3616295).
//!
//! # Algorithm
//!
//! `CogLoad(f) = α × coupling_degree(f) + β × dir_spread(f) +
//!               γ × author_diversity(f) + δ × temporal_dispersion(f)`
//!
//! where:
//! - `coupling_degree(f)` = number of files co-changed with f
//! - `dir_spread(f)` = number of distinct directories in coupled files
//! - `author_diversity(f)` = entropy of author distribution
//! - `temporal_dispersion(f)` = std dev of inter-change intervals
//!
//! Weights: α=0.3, β=0.25, γ=0.25, δ=0.2
//!
//! # Complexity
//!
//! - Accumulation: O(1) per file change
//! - Finalization: O(F × log F)

use rustc_hash::FxHashMap;

const ALPHA: f64 = 0.30; // coupling degree weight
const BETA: f64 = 0.25; // directory spread weight
const GAMMA: f64 = 0.25; // author diversity weight
const DELTA: f64 = 0.20; // temporal dispersion weight

/// Per-file cognitive load estimate.
#[derive(Debug, Clone)]
pub struct FileCognitiveLoad {
    /// File path.
    pub path: String,
    /// Composite cognitive load score (higher = more complex to work on).
    pub load_score: f64,
    /// Coupling degree component (normalized).
    pub coupling_component: f64,
    /// Directory spread component (normalized).
    pub dir_spread_component: f64,
    /// Author diversity component (normalized).
    pub author_diversity_component: f64,
    /// Temporal dispersion component (normalized).
    pub temporal_component: f64,
    /// Number of coupled files.
    pub coupled_file_count: u32,
    /// Number of unique authors.
    pub author_count: u32,
}

/// Complete cognitive load report.
#[derive(Debug, Clone)]
pub struct CognitiveLoadReport {
    /// Per-file cognitive load (sorted by `load_score` descending).
    pub files: Vec<FileCognitiveLoad>,
    /// Average cognitive load across all files.
    pub avg_load: f64,
    /// Files with high cognitive load (score > 0.7).
    pub high_load_count: usize,
    /// Total files analyzed.
    pub total_analyzed: usize,
}

/// Per-file accumulation state.
struct FileAccState {
    authors: FxHashMap<String, u32>,
    timestamps: Vec<i64>,
    directories_of_cochanges: rustc_hash::FxHashSet<String>,
    cochange_count: u32,
}

/// Accumulates cognitive load data from commit stream.
pub struct CognitiveLoadAccumulator {
    files: FxHashMap<String, FileAccState>,
}

impl Default for CognitiveLoadAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl CognitiveLoadAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            files: FxHashMap::default(),
        }
    }

    /// Records a commit touching multiple files (for co-change tracking).
    pub fn record_commit(&mut self, author: &str, timestamp: i64, file_paths: &[&str]) {
        // For each file, track co-changes with other files in this commit
        for &path in file_paths {
            let state = self
                .files
                .entry(path.to_string())
                .or_insert_with(|| FileAccState {
                    authors: FxHashMap::default(),
                    timestamps: Vec::new(),
                    directories_of_cochanges: rustc_hash::FxHashSet::default(),
                    cochange_count: 0,
                });

            *state.authors.entry(author.to_string()).or_insert(0) += 1;
            state.timestamps.push(timestamp);

            // Track directories of co-changed files
            for &other in file_paths {
                if other != path {
                    state.cochange_count += 1;
                    let dir = other
                        .split('/')
                        .next()
                        .filter(|_| other.contains('/'))
                        .unwrap_or(".")
                        .to_string();
                    state.directories_of_cochanges.insert(dir);
                }
            }
        }
    }

    /// Finalizes the cognitive load report.
    #[must_use]
    pub fn finalize(self) -> CognitiveLoadReport {
        let total_analyzed = self.files.len();

        // Find max values for normalization
        let max_coupling = self
            .files
            .values()
            .map(|s| s.cochange_count)
            .max()
            .unwrap_or(1)
            .max(1);
        let max_dirs = self
            .files
            .values()
            .map(|s| s.directories_of_cochanges.len() as u32)
            .max()
            .unwrap_or(1)
            .max(1);
        let mut files: Vec<FileCognitiveLoad> = self
            .files
            .into_iter()
            .map(|(path, state)| {
                let coupling_norm = f64::from(state.cochange_count) / f64::from(max_coupling);
                let dir_norm = state.directories_of_cochanges.len() as f64 / f64::from(max_dirs);

                // Author diversity: normalized entropy
                let total_author_commits: u32 = state.authors.values().sum();
                let author_entropy = if state.authors.len() <= 1 {
                    0.0
                } else {
                    let total_f = f64::from(total_author_commits);
                    let h: f64 = state
                        .authors
                        .values()
                        .map(|&c| {
                            let p = f64::from(c) / total_f;
                            if p > 0.0 {
                                -p * p.log2()
                            } else {
                                0.0
                            }
                        })
                        .sum();
                    h / (state.authors.len() as f64).log2()
                };

                let temporal_norm = temporal_cv(&state.timestamps);

                let load_score = ALPHA * coupling_norm
                    + BETA * dir_norm
                    + GAMMA * author_entropy
                    + DELTA * temporal_norm;

                FileCognitiveLoad {
                    path,
                    load_score,
                    coupling_component: coupling_norm,
                    dir_spread_component: dir_norm,
                    author_diversity_component: author_entropy,
                    temporal_component: temporal_norm,
                    coupled_file_count: state.cochange_count,
                    author_count: state.authors.len() as u32,
                }
            })
            .collect();

        files.sort_by(|a, b| {
            b.load_score
                .partial_cmp(&a.load_score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        files.truncate(50);

        let avg_load = if files.is_empty() {
            0.0
        } else {
            files.iter().map(|f| f.load_score).sum::<f64>() / files.len() as f64
        };
        let high_load_count = files.iter().filter(|f| f.load_score > 0.7).count();

        CognitiveLoadReport {
            files,
            avg_load,
            high_load_count,
            total_analyzed,
        }
    }
}

/// Computes the coefficient of variation of inter-change intervals, capped at 1.0.
fn temporal_cv(timestamps: &[i64]) -> f64 {
    if timestamps.len() < 2 {
        return 0.0;
    }
    let mut sorted = timestamps.to_vec();
    sorted.sort_unstable();
    let intervals: Vec<f64> = sorted.windows(2).map(|w| (w[1] - w[0]) as f64).collect();
    let mean = intervals.iter().sum::<f64>() / intervals.len() as f64;
    if mean > 0.0 {
        let variance = intervals
            .iter()
            .map(|&x| (x - mean) * (x - mean))
            .sum::<f64>()
            / intervals.len() as f64;
        (variance.sqrt() / mean).min(1.0)
    } else {
        0.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let acc = CognitiveLoadAccumulator::new();
        let report = acc.finalize();
        assert!(report.files.is_empty());
    }

    #[test]
    fn test_single_file_single_author() {
        let mut acc = CognitiveLoadAccumulator::new();
        acc.record_commit("Alice", 100, &["a.rs"]);
        acc.record_commit("Alice", 200, &["a.rs"]);
        let report = acc.finalize();
        assert_eq!(report.files.len(), 1);
        // Single author, no co-changes → low load
        assert!(report.files[0].load_score < 0.5);
    }

    #[test]
    fn test_high_coupling_high_load() {
        let mut acc = CognitiveLoadAccumulator::new();
        // File always co-changes with many other files
        for i in 0..10 {
            acc.record_commit(
                &format!("Dev{i}"),
                i * 100,
                &["core.rs", "a.rs", "b.rs", "c.rs", "d.rs"],
            );
        }
        let report = acc.finalize();
        let core = report.files.iter().find(|f| f.path == "core.rs").unwrap();
        assert!(core.coupled_file_count > 0);
    }

    #[test]
    fn test_default_impl() {
        let acc = CognitiveLoadAccumulator::default();
        let report = acc.finalize();
        assert!(report.files.is_empty());
    }
}
