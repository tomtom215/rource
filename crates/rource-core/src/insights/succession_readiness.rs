// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Developer Succession Readiness analysis.
//!
//! For each file, a score indicating how prepared the team is for the primary
//! contributor to become unavailable, combining knowledge freshness, contributor
//! depth, and change-pattern similarity.
//!
//! # Research Basis
//!
//! - Ricca et al. (JSS 2011, DOI: 10.1016/j.jss.2011.03.033) — developer succession
//! - Rigby & Bird (FSE 2013, DOI: 10.1145/2491411.2491444) — knowledge distribution
//! - Depends on Knowledge Half-Life (M5) for K(d, f, now) values
//!
//! # Novelty
//!
//! Combining exponential knowledge decay with Jaccard directory similarity and
//! depth-weighted successor scoring is new. Existing succession metrics are
//! binary (successor exists or not) rather than continuous and multi-dimensional.
//!
//! # Algorithm
//!
//! For file f with primary contributor p (highest K(d, f, now)):
//!
//! For each candidate `d ≠ p` with `K(d, f, now) > 0`:
//!   `successor_score(d, f) = recency(d,f) × depth(d,f) × similarity(d,f)`
//!
//! where:
//!   recency(d, f) = K(d, f, now) / K(p, f, now)  (normalized to primary)
//!   depth(d, f) = commits(d, f) / commits(p, f)
//!   similarity(d, f) = |dirs(d) ∩ dirs(p)| / |dirs(d) ∪ dirs(p)|  (Jaccard)
//!
//! `SR(f) = max successor_score` across candidates
//!
//! # Complexity
//!
//! - Per file: O(|candidates| × max(|dirs|)) — small in practice
//! - Total: O(F × D̄) where F = files, D̄ = mean candidates per file

use rustc_hash::{FxHashMap, FxHashSet};

/// Per-file succession readiness.
#[derive(Debug, Clone)]
pub struct FileSuccessionReadiness {
    /// File path.
    pub path: String,
    /// Primary contributor (highest current knowledge).
    pub primary_contributor: String,
    /// Succession readiness score [0, 1].
    /// 0 = no viable successor, 1 = strong successor ready.
    pub readiness: f64,
    /// Best successor candidate (if any).
    pub best_successor: Option<String>,
    /// Best successor's score.
    pub best_successor_score: f64,
    /// Gap: 1.0 - readiness.
    pub succession_gap: f64,
    /// All candidates with scores (sorted by score descending).
    pub candidates: Vec<(String, f64)>,
}

/// Aggregate succession readiness report.
#[derive(Debug, Clone)]
pub struct SuccessionReadinessReport {
    /// Per-file succession readiness (least ready first).
    pub files: Vec<FileSuccessionReadiness>,
    /// Codebase Succession Readiness (importance-weighted by hotspot score).
    pub codebase_readiness: f64,
    /// Number of files with readiness = 0 (single point of failure).
    pub single_point_of_failure_count: u32,
    /// Number of files with readiness > 0.5 (adequate succession).
    pub adequate_succession_count: u32,
    /// Total files analyzed.
    pub total_files: u32,
}

/// Developer knowledge state for a file (input from Knowledge Half-Life M5).
pub struct DeveloperFileKnowledge {
    /// Developer name.
    pub author: String,
    /// Current knowledge K(d, f, now).
    pub knowledge: f64,
    /// Number of commits to this file.
    pub commit_count: u32,
}

/// Computes succession readiness from knowledge half-life data.
///
/// # Arguments
///
/// * `file_knowledge` - Per-file list of developer knowledge states
/// * `developer_dirs` - Per-developer set of directories they've worked in
/// * `file_hotspot_scores` - Per-file hotspot scores (for importance weighting)
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn compute_succession_readiness(
    file_knowledge: &FxHashMap<String, Vec<DeveloperFileKnowledge>>,
    developer_dirs: &FxHashMap<String, FxHashSet<String>>,
    file_hotspot_scores: &FxHashMap<String, f64>,
) -> SuccessionReadinessReport {
    if file_knowledge.is_empty() {
        return SuccessionReadinessReport {
            files: Vec::new(),
            codebase_readiness: 0.0,
            single_point_of_failure_count: 0,
            adequate_succession_count: 0,
            total_files: 0,
        };
    }

    let mut results: Vec<FileSuccessionReadiness> = Vec::with_capacity(file_knowledge.len());

    for (path, devs) in file_knowledge {
        if devs.is_empty() {
            continue;
        }

        // Find primary contributor (highest knowledge)
        let primary = devs
            .iter()
            .max_by(|a, b| {
                a.knowledge
                    .partial_cmp(&b.knowledge)
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
            .unwrap();

        let primary_k = primary.knowledge;
        let primary_commits = primary.commit_count;
        let primary_name = &primary.author;

        if primary_k <= 0.0 || primary_commits == 0 {
            results.push(FileSuccessionReadiness {
                path: path.clone(),
                primary_contributor: primary_name.clone(),
                readiness: 0.0,
                best_successor: None,
                best_successor_score: 0.0,
                succession_gap: 1.0,
                candidates: Vec::new(),
            });
            continue;
        }

        let primary_dirs = developer_dirs.get(primary_name);

        // Score each candidate
        let mut candidates: Vec<(String, f64)> = devs
            .iter()
            .filter(|d| d.author != *primary_name && d.knowledge > 0.0)
            .map(|d| {
                let recency = d.knowledge / primary_k;
                let depth = if primary_commits > 0 {
                    (f64::from(d.commit_count) / f64::from(primary_commits)).min(1.0)
                } else {
                    0.0
                };

                let similarity = if let (Some(p_dirs), Some(d_dirs)) =
                    (primary_dirs, developer_dirs.get(&d.author))
                {
                    jaccard_similarity(p_dirs, d_dirs)
                } else {
                    0.0
                };

                let score = recency * depth * similarity;
                (d.author.clone(), score)
            })
            .collect();

        candidates
            .sort_unstable_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));

        let readiness = candidates.first().map_or(0.0, |(_, s)| *s).min(1.0);
        let best_successor = candidates.first().map(|(name, _)| name.clone());
        let best_successor_score = candidates.first().map_or(0.0, |(_, s)| *s);

        results.push(FileSuccessionReadiness {
            path: path.clone(),
            primary_contributor: primary_name.clone(),
            readiness,
            best_successor,
            best_successor_score,
            succession_gap: 1.0 - readiness,
            candidates,
        });
    }

    // Sort: least ready first
    results.sort_unstable_by(|a, b| {
        a.readiness
            .partial_cmp(&b.readiness)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let total_files = results.len() as u32;
    let spof_count = results.iter().filter(|f| f.readiness == 0.0).count() as u32;
    let adequate_count = results.iter().filter(|f| f.readiness > 0.5).count() as u32;

    // Codebase succession readiness (importance-weighted)
    let (weighted_sum, weight_total) = results.iter().fold((0.0, 0.0), |(ws, wt), f| {
        let hotspot = file_hotspot_scores.get(&f.path).copied().unwrap_or(1.0);
        (ws + f.readiness * hotspot, wt + hotspot)
    });
    let codebase_readiness = if weight_total > 0.0 {
        weighted_sum / weight_total
    } else {
        0.0
    };

    SuccessionReadinessReport {
        files: results,
        codebase_readiness,
        single_point_of_failure_count: spof_count,
        adequate_succession_count: adequate_count,
        total_files,
    }
}

/// Jaccard similarity: |A ∩ B| / |A ∪ B|.
fn jaccard_similarity(a: &FxHashSet<String>, b: &FxHashSet<String>) -> f64 {
    if a.is_empty() && b.is_empty() {
        return 0.0;
    }
    let intersection = a.intersection(b).count();
    let union = a.union(b).count();
    if union == 0 {
        0.0
    } else {
        intersection as f64 / union as f64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_dirs(dirs: &[&str]) -> FxHashSet<String> {
        dirs.iter().map(ToString::to_string).collect()
    }

    #[test]
    fn test_empty_input() {
        let report = compute_succession_readiness(
            &FxHashMap::default(),
            &FxHashMap::default(),
            &FxHashMap::default(),
        );
        assert_eq!(report.total_files, 0);
    }

    #[test]
    fn test_single_developer_no_successor() {
        let mut file_knowledge: FxHashMap<String, Vec<DeveloperFileKnowledge>> =
            FxHashMap::default();
        file_knowledge.insert(
            "a.rs".to_string(),
            vec![DeveloperFileKnowledge {
                author: "Alice".to_string(),
                knowledge: 1.0,
                commit_count: 10,
            }],
        );

        let report = compute_succession_readiness(
            &file_knowledge,
            &FxHashMap::default(),
            &FxHashMap::default(),
        );

        assert_eq!(report.files.len(), 1);
        assert_eq!(report.files[0].readiness, 0.0);
        assert!(report.files[0].best_successor.is_none());
        assert_eq!(report.single_point_of_failure_count, 1);
    }

    #[test]
    fn test_strong_successor() {
        let mut file_knowledge: FxHashMap<String, Vec<DeveloperFileKnowledge>> =
            FxHashMap::default();
        file_knowledge.insert(
            "a.rs".to_string(),
            vec![
                DeveloperFileKnowledge {
                    author: "Alice".to_string(),
                    knowledge: 1.0,
                    commit_count: 10,
                },
                DeveloperFileKnowledge {
                    author: "Bob".to_string(),
                    knowledge: 0.9,
                    commit_count: 8,
                },
            ],
        );

        let mut dev_dirs: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
        dev_dirs.insert("Alice".to_string(), make_dirs(&["src", "tests"]));
        dev_dirs.insert("Bob".to_string(), make_dirs(&["src", "tests"]));

        let report =
            compute_succession_readiness(&file_knowledge, &dev_dirs, &FxHashMap::default());

        assert_eq!(report.files.len(), 1);
        assert!(report.files[0].readiness > 0.5);
        assert_eq!(report.files[0].best_successor.as_deref(), Some("Bob"));
    }

    #[test]
    fn test_weak_successor_different_dirs() {
        let mut file_knowledge: FxHashMap<String, Vec<DeveloperFileKnowledge>> =
            FxHashMap::default();
        file_knowledge.insert(
            "a.rs".to_string(),
            vec![
                DeveloperFileKnowledge {
                    author: "Alice".to_string(),
                    knowledge: 1.0,
                    commit_count: 10,
                },
                DeveloperFileKnowledge {
                    author: "Bob".to_string(),
                    knowledge: 0.5,
                    commit_count: 3,
                },
            ],
        );

        let mut dev_dirs: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
        dev_dirs.insert("Alice".to_string(), make_dirs(&["src", "core"]));
        dev_dirs.insert("Bob".to_string(), make_dirs(&["docs", "scripts"]));

        let report =
            compute_succession_readiness(&file_knowledge, &dev_dirs, &FxHashMap::default());

        // Low Jaccard similarity + lower knowledge → low readiness
        assert!(report.files[0].readiness < 0.3);
    }

    #[test]
    fn test_readiness_range() {
        let mut file_knowledge: FxHashMap<String, Vec<DeveloperFileKnowledge>> =
            FxHashMap::default();
        file_knowledge.insert(
            "a.rs".to_string(),
            vec![
                DeveloperFileKnowledge {
                    author: "Alice".to_string(),
                    knowledge: 1.0,
                    commit_count: 10,
                },
                DeveloperFileKnowledge {
                    author: "Bob".to_string(),
                    knowledge: 0.8,
                    commit_count: 9,
                },
            ],
        );

        let mut dev_dirs: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
        dev_dirs.insert("Alice".to_string(), make_dirs(&["src"]));
        dev_dirs.insert("Bob".to_string(), make_dirs(&["src"]));

        let report =
            compute_succession_readiness(&file_knowledge, &dev_dirs, &FxHashMap::default());

        for file in &report.files {
            assert!(file.readiness >= 0.0 && file.readiness <= 1.0);
            assert!((file.succession_gap - (1.0 - file.readiness)).abs() < f64::EPSILON);
        }
    }

    #[test]
    fn test_codebase_readiness_weighted() {
        let mut file_knowledge: FxHashMap<String, Vec<DeveloperFileKnowledge>> =
            FxHashMap::default();
        file_knowledge.insert(
            "hot.rs".to_string(),
            vec![DeveloperFileKnowledge {
                author: "Alice".to_string(),
                knowledge: 1.0,
                commit_count: 10,
            }],
        );
        file_knowledge.insert(
            "cold.rs".to_string(),
            vec![
                DeveloperFileKnowledge {
                    author: "Alice".to_string(),
                    knowledge: 1.0,
                    commit_count: 5,
                },
                DeveloperFileKnowledge {
                    author: "Bob".to_string(),
                    knowledge: 0.9,
                    commit_count: 4,
                },
            ],
        );

        let mut dev_dirs: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
        dev_dirs.insert("Alice".to_string(), make_dirs(&["src"]));
        dev_dirs.insert("Bob".to_string(), make_dirs(&["src"]));

        let mut hotspot_scores: FxHashMap<String, f64> = FxHashMap::default();
        hotspot_scores.insert("hot.rs".to_string(), 10.0);
        hotspot_scores.insert("cold.rs".to_string(), 1.0);

        let report = compute_succession_readiness(&file_knowledge, &dev_dirs, &hotspot_scores);

        assert!(report.codebase_readiness >= 0.0 && report.codebase_readiness <= 1.0);
    }

    #[test]
    fn test_jaccard_identical() {
        let a = make_dirs(&["src", "tests"]);
        let b = make_dirs(&["src", "tests"]);
        assert!((jaccard_similarity(&a, &b) - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_jaccard_disjoint() {
        let a = make_dirs(&["src"]);
        let b = make_dirs(&["tests"]);
        assert_eq!(jaccard_similarity(&a, &b), 0.0);
    }

    #[test]
    fn test_jaccard_partial() {
        let a = make_dirs(&["src", "tests"]);
        let b = make_dirs(&["src", "docs"]);
        // Intersection: {src}, Union: {src, tests, docs}
        assert!((jaccard_similarity(&a, &b) - 1.0 / 3.0).abs() < 0.001);
    }

    #[test]
    fn test_jaccard_empty() {
        let a = FxHashSet::default();
        let b = FxHashSet::default();
        assert_eq!(jaccard_similarity(&a, &b), 0.0);
    }
}
