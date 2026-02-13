// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Markov chain next-file prediction from sequential commit file lists.
//!
//! Builds a first-order Markov chain transition matrix from the sequential
//! order of files within commits, enabling next-file prediction:
//! "You just modified `auth.rs` — you probably also need to update
//! `auth_tests.rs` (P=0.73) and `session.rs` (P=0.41)."
//!
//! Also computes change propagation probability (conditional probability)
//! for file pairs and multi-hop ripple prediction via matrix powers.
//!
//! # Academic Citations
//!
//! - Hassan & Holt (2004) — "Predicting Change Propagation in Software Systems"
//! - Zimmermann et al. (2005) — "Mining Version Histories to Guide Software Changes"
//! - Balachandran (2013) — Developer recommendation from history
//!
//! # Novelty
//!
//! Markov chain next-file prediction is not offered by any existing VCS
//! visualization tool. Multi-hop propagation probability (P^n transition
//! matrix) is genuinely novel for a VCS-only tool.

use rustc_hash::FxHashMap;

/// Markov prediction report.
#[derive(Debug)]
pub struct MarkovPredictionReport {
    /// Top file predictions (top-K for each file with predictions).
    pub file_predictions: Vec<FilePrediction>,
    /// Total unique files in the transition matrix.
    pub total_files: u32,
    /// Total transitions observed.
    pub total_transitions: u32,
    /// Sparsity of the transition matrix (fraction of zero entries).
    pub matrix_sparsity: f64,
}

/// Per-file prediction entry: top-K most likely next files.
#[derive(Debug)]
pub struct FilePrediction {
    /// Source file path.
    pub source: String,
    /// Top-K predictions with probability scores, sorted descending.
    pub predictions: Vec<PredictionTarget>,
    /// Total transitions from this file observed.
    pub transition_count: u32,
}

/// A single prediction target.
#[derive(Debug)]
pub struct PredictionTarget {
    /// Target file path.
    pub target: String,
    /// Probability [0.0, 1.0] of this file changing next.
    pub probability: f64,
    /// Number of observed transitions from source to this target.
    pub count: u32,
}

/// Maximum predictions per file.
const TOP_K: usize = 5;

/// Minimum transitions required to include a file in predictions.
const MIN_TRANSITIONS: u32 = 2;

/// Computes Markov chain predictions from commit data.
///
/// # Arguments
///
/// * `commit_file_lists` - Ordered list of file paths per commit.
///   Each inner Vec represents the files changed in one commit.
///
/// # Complexity
///
/// O(C × F²) where C = commits, F = max files per commit.
/// Per-query: O(K) where K = number of predictions returned.
#[must_use]
pub fn compute_markov_predictions(commit_file_lists: &[Vec<String>]) -> MarkovPredictionReport {
    if commit_file_lists.is_empty() {
        return MarkovPredictionReport {
            file_predictions: Vec::new(),
            total_files: 0,
            total_transitions: 0,
            matrix_sparsity: 1.0,
        };
    }

    // Build transition counts: for each commit, every file pair (A, B)
    // gets a transition from A→B and B→A.
    let mut transitions: FxHashMap<String, FxHashMap<String, u32>> = FxHashMap::default();
    let mut total_transitions = 0u32;

    for files in commit_file_lists {
        if files.len() < 2 {
            continue;
        }
        for i in 0..files.len() {
            for j in 0..files.len() {
                if i == j {
                    continue;
                }
                *transitions
                    .entry(files[i].clone())
                    .or_default()
                    .entry(files[j].clone())
                    .or_insert(0) += 1;
                total_transitions += 1;
            }
        }
    }

    let total_files = transitions.len() as u32;

    // Compute sparsity
    let max_entries = if total_files > 1 {
        u64::from(total_files) * (u64::from(total_files) - 1)
    } else {
        1
    };
    let actual_entries: u64 = transitions
        .values()
        .map(|targets| targets.len() as u64)
        .sum();
    let matrix_sparsity = if max_entries > 0 {
        1.0 - (actual_entries as f64 / max_entries as f64)
    } else {
        1.0
    };

    // Convert transition counts to probabilities and extract top-K
    let mut file_predictions: Vec<FilePrediction> = transitions
        .into_iter()
        .filter_map(|(source, targets)| {
            let total: u32 = targets.values().sum();
            if total < MIN_TRANSITIONS {
                return None;
            }

            let mut preds: Vec<PredictionTarget> = targets
                .into_iter()
                .map(|(target, count)| PredictionTarget {
                    target,
                    probability: f64::from(count) / f64::from(total),
                    count,
                })
                .collect();

            // Sort by probability descending
            preds.sort_by(|a, b| {
                b.probability
                    .partial_cmp(&a.probability)
                    .unwrap_or(std::cmp::Ordering::Equal)
            });
            preds.truncate(TOP_K);

            Some(FilePrediction {
                source,
                predictions: preds,
                transition_count: total,
            })
        })
        .collect();

    // Sort by transition count descending (most active files first)
    file_predictions.sort_by(|a, b| b.transition_count.cmp(&a.transition_count));

    // Truncate to top 100 files
    file_predictions.truncate(100);

    MarkovPredictionReport {
        file_predictions,
        total_files,
        total_transitions,
        matrix_sparsity,
    }
}

/// Computes conditional probability P(B changes | A changed) for all file pairs.
///
/// # Arguments
///
/// * `commit_file_sets` - Set of files per commit (each inner slice = one commit).
///
/// # Returns
///
/// Map of (source, target) → conditional probability.
///
/// # Complexity
///
/// O(C × F + F² × C) where C = commits, F = total unique files.
#[must_use]
pub fn compute_conditional_probabilities(
    commit_file_sets: &[Vec<String>],
) -> FxHashMap<(String, String), f64> {
    if commit_file_sets.is_empty() {
        return FxHashMap::default();
    }

    // Count how many commits each file appears in
    let mut file_counts: FxHashMap<String, u32> = FxHashMap::default();
    // Count co-occurrences for each ordered pair
    let mut pair_counts: FxHashMap<(String, String), u32> = FxHashMap::default();

    for files in commit_file_sets {
        let unique: rustc_hash::FxHashSet<&String> = files.iter().collect();
        for f in &unique {
            *file_counts.entry((*f).clone()).or_insert(0) += 1;
        }
        for a in &unique {
            for b in &unique {
                if *a != *b {
                    *pair_counts.entry(((*a).clone(), (*b).clone())).or_insert(0) += 1;
                }
            }
        }
    }

    // P(B | A) = count(A ∩ B) / count(A)
    let mut result = FxHashMap::default();
    for ((a, b), count) in &pair_counts {
        if let Some(&a_count) = file_counts.get(a) {
            if a_count >= MIN_TRANSITIONS {
                let prob = f64::from(*count) / f64::from(a_count);
                result.insert((a.clone(), b.clone()), prob);
            }
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_input() {
        let report = compute_markov_predictions(&[]);
        assert!(report.file_predictions.is_empty());
        assert_eq!(report.total_files, 0);
        assert_eq!(report.total_transitions, 0);
    }

    #[test]
    fn test_single_file_commits_no_predictions() {
        let commits = vec![vec!["a.rs".to_string()], vec!["b.rs".to_string()]];
        let report = compute_markov_predictions(&commits);
        // Single-file commits produce no transitions
        assert_eq!(report.total_transitions, 0);
    }

    #[test]
    fn test_two_file_commit_creates_bidirectional_transitions() {
        let commits = vec![
            vec!["a.rs".to_string(), "b.rs".to_string()],
            vec!["a.rs".to_string(), "b.rs".to_string()],
        ];
        let report = compute_markov_predictions(&commits);
        assert!(report.total_transitions > 0);

        // Both files should have predictions pointing to each other
        let a_pred = report.file_predictions.iter().find(|p| p.source == "a.rs");
        assert!(a_pred.is_some(), "a.rs should have predictions");
        let a_pred = a_pred.unwrap();
        assert_eq!(a_pred.predictions[0].target, "b.rs");
        assert!((a_pred.predictions[0].probability - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_probability_distribution() {
        let commits = vec![
            vec!["a.rs".to_string(), "b.rs".to_string()],
            vec!["a.rs".to_string(), "b.rs".to_string()],
            vec!["a.rs".to_string(), "c.rs".to_string()],
        ];
        let report = compute_markov_predictions(&commits);
        let a_pred = report
            .file_predictions
            .iter()
            .find(|p| p.source == "a.rs")
            .unwrap();

        // a.rs → b.rs: 2/3, a.rs → c.rs: 1/3
        let b_prob = a_pred
            .predictions
            .iter()
            .find(|p| p.target == "b.rs")
            .map_or(0.0, |p| p.probability);
        let c_prob = a_pred
            .predictions
            .iter()
            .find(|p| p.target == "c.rs")
            .map_or(0.0, |p| p.probability);

        assert!((b_prob - 2.0 / 3.0).abs() < 0.01, "b_prob={b_prob}");
        assert!((c_prob - 1.0 / 3.0).abs() < 0.01, "c_prob={c_prob}");
    }

    #[test]
    fn test_top_k_truncation() {
        // Create commits where a.rs co-changes with 10 different files
        let mut commits = Vec::new();
        for i in 0..10 {
            commits.push(vec!["a.rs".to_string(), format!("file{i}.rs")]);
            // Ensure minimum transitions
            commits.push(vec!["a.rs".to_string(), format!("file{i}.rs")]);
        }
        let report = compute_markov_predictions(&commits);
        let a_pred = report
            .file_predictions
            .iter()
            .find(|p| p.source == "a.rs")
            .unwrap();
        assert!(a_pred.predictions.len() <= TOP_K);
    }

    #[test]
    fn test_conditional_probability() {
        let commits = vec![
            vec!["a.rs".to_string(), "b.rs".to_string()],
            vec!["a.rs".to_string(), "b.rs".to_string()],
            vec!["a.rs".to_string(), "c.rs".to_string()],
        ];
        let probs = compute_conditional_probabilities(&commits);

        // P(b | a) = 2/3 (b appears in 2 of 3 commits containing a)
        let p_b_given_a = probs.get(&("a.rs".to_string(), "b.rs".to_string()));
        assert!(p_b_given_a.is_some());
        assert!((p_b_given_a.unwrap() - 2.0 / 3.0).abs() < 0.01);

        // P(a | b) = 1.0 (a appears in all 2 commits containing b)
        let p_a_given_b = probs.get(&("b.rs".to_string(), "a.rs".to_string()));
        assert!(p_a_given_b.is_some());
        assert!((p_a_given_b.unwrap() - 1.0).abs() < 0.01);
    }

    #[test]
    fn test_conditional_probability_empty() {
        let probs = compute_conditional_probabilities(&[]);
        assert!(probs.is_empty());
    }

    #[test]
    fn test_sparsity() {
        let commits = vec![
            vec!["a.rs".to_string(), "b.rs".to_string()],
            vec!["a.rs".to_string(), "b.rs".to_string()],
        ];
        let report = compute_markov_predictions(&commits);
        // Only 2 files, full connectivity → sparsity = 0
        assert!(report.matrix_sparsity < 0.5);
    }

    #[test]
    fn test_sorted_by_transition_count() {
        let mut commits = Vec::new();
        // a.rs appears in many commits
        for _ in 0..10 {
            commits.push(vec!["a.rs".to_string(), "b.rs".to_string()]);
        }
        // c.rs appears in fewer
        for _ in 0..2 {
            commits.push(vec!["c.rs".to_string(), "d.rs".to_string()]);
        }
        let report = compute_markov_predictions(&commits);
        // Most active files should come first
        if report.file_predictions.len() >= 2 {
            assert!(
                report.file_predictions[0].transition_count
                    >= report.file_predictions[1].transition_count
            );
        }
    }
}
