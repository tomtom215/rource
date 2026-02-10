// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Knowledge map and knowledge silo detection.
//!
//! Extends ownership analysis to compute per-file knowledge distribution
//! and identify "knowledge silos" — files where institutional knowledge is
//! concentrated in a single contributor.
//!
//! # Research Basis
//!
//! Rigby & Bird (2013) "Convergent Contemporary Software Peer Review Practices"
//! (ESEC/FSE) showed that broad code review correlates with fewer defects.
//! Fritz et al. (2014) modeled degree-of-knowledge, showing that knowledge
//! concentration predicts code quality.
//!
//! # Algorithm
//!
//! For each file, compute Shannon entropy over the ownership distribution:
//! - entropy = -Σ `p_i` * `log2(p_i)` where `p_i` = `changes_by_author_i` / `total_changes`
//! - High entropy = distributed knowledge = lower risk
//! - Low entropy (especially 0) = concentrated knowledge = knowledge silo
//!
//! A file is classified as a "silo" when `contributor_count` == 1.
//!
//! # Complexity
//!
//! - Computation: O(F * A) where F = files, A = max contributors per file

use rustc_hash::FxHashMap;

/// Knowledge distribution for a single file.
#[derive(Debug, Clone)]
pub struct FileKnowledge {
    /// File path relative to repository root.
    pub path: String,
    /// Shannon entropy of the ownership distribution (bits).
    /// 0.0 = single owner; higher = more distributed.
    pub knowledge_entropy: f64,
    /// Whether this file is a knowledge silo (single contributor).
    pub is_silo: bool,
    /// The sole owner if this is a silo, otherwise the top contributor.
    pub primary_owner: String,
    /// Number of distinct contributors.
    pub contributor_count: usize,
}

/// Per-directory knowledge aggregation.
#[derive(Debug, Clone)]
pub struct DirectoryKnowledge {
    /// Directory path.
    pub directory: String,
    /// Average knowledge entropy across files in this directory.
    pub avg_entropy: f64,
    /// Percentage of files that are silos (0.0-100.0).
    pub silo_percentage: f64,
    /// Total files in this directory.
    pub file_count: usize,
    /// Number of silo files.
    pub silo_count: usize,
}

/// Aggregate knowledge report for the repository.
#[derive(Debug, Clone)]
pub struct KnowledgeReport {
    /// Per-file knowledge distribution, sorted by entropy ascending (silos first).
    pub files: Vec<FileKnowledge>,
    /// Per-directory aggregation, sorted by silo percentage descending.
    pub directories: Vec<DirectoryKnowledge>,
    /// Total knowledge silos in the repository.
    pub total_silos: usize,
    /// Percentage of files that are silos (0.0-100.0).
    pub silo_percentage: f64,
    /// Average knowledge entropy across all files.
    pub avg_entropy: f64,
}

/// Computes knowledge distribution from file-author ownership data.
///
/// # Arguments
///
/// * `file_authors` - Map of file path → (author → change count)
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn compute_knowledge(
    file_authors: &FxHashMap<String, FxHashMap<String, u32>>,
) -> KnowledgeReport {
    if file_authors.is_empty() {
        return KnowledgeReport {
            files: Vec::new(),
            directories: Vec::new(),
            total_silos: 0,
            silo_percentage: 0.0,
            avg_entropy: 0.0,
        };
    }

    let mut files: Vec<FileKnowledge> = file_authors
        .iter()
        .map(|(path, authors)| compute_file_knowledge(path.clone(), authors))
        .collect();

    // Sort by entropy ascending (silos/concentrated knowledge first)
    files.sort_by(|a, b| {
        a.knowledge_entropy
            .partial_cmp(&b.knowledge_entropy)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let total_silos = files.iter().filter(|f| f.is_silo).count();
    let silo_percentage = total_silos as f64 / files.len() as f64 * 100.0;
    let avg_entropy = files.iter().map(|f| f.knowledge_entropy).sum::<f64>() / files.len() as f64;

    let directories = compute_directory_knowledge(&files);

    KnowledgeReport {
        files,
        directories,
        total_silos,
        silo_percentage,
        avg_entropy,
    }
}

/// Computes knowledge entropy for a single file.
fn compute_file_knowledge(path: String, authors: &FxHashMap<String, u32>) -> FileKnowledge {
    let total: u32 = authors.values().sum();
    let contributor_count = authors.len();

    if total == 0 || contributor_count == 0 {
        return FileKnowledge {
            path,
            knowledge_entropy: 0.0,
            is_silo: true,
            primary_owner: String::new(),
            contributor_count: 0,
        };
    }

    let total_f = f64::from(total);
    let entropy: f64 = authors
        .values()
        .map(|&count| {
            let p = f64::from(count) / total_f;
            if p > 0.0 {
                -p * p.log2()
            } else {
                0.0
            }
        })
        .sum();

    let primary_owner = authors
        .iter()
        .max_by_key(|(_, &v)| v)
        .map_or_else(String::new, |(k, _)| k.clone());

    let is_silo = contributor_count == 1;

    FileKnowledge {
        path,
        knowledge_entropy: entropy,
        is_silo,
        primary_owner,
        contributor_count,
    }
}

/// Aggregates file knowledge into per-directory summaries.
fn compute_directory_knowledge(files: &[FileKnowledge]) -> Vec<DirectoryKnowledge> {
    let mut dir_files: FxHashMap<String, Vec<&FileKnowledge>> = FxHashMap::default();
    for file in files {
        let dir = extract_directory(&file.path);
        dir_files.entry(dir).or_default().push(file);
    }

    let mut dirs: Vec<DirectoryKnowledge> = dir_files
        .into_iter()
        .map(|(directory, files)| {
            let file_count = files.len();
            let silo_count = files.iter().filter(|f| f.is_silo).count();
            let avg_entropy =
                files.iter().map(|f| f.knowledge_entropy).sum::<f64>() / file_count as f64;
            let silo_percentage = silo_count as f64 / file_count as f64 * 100.0;

            DirectoryKnowledge {
                directory,
                avg_entropy,
                silo_percentage,
                file_count,
                silo_count,
            }
        })
        .collect();

    // Sort by silo percentage descending (most siloed directories first)
    dirs.sort_by(|a, b| {
        b.silo_percentage
            .partial_cmp(&a.silo_percentage)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    dirs
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

    fn make_file_authors(
        entries: &[(&str, &[(&str, u32)])],
    ) -> FxHashMap<String, FxHashMap<String, u32>> {
        entries
            .iter()
            .map(|(path, authors)| {
                let author_map: FxHashMap<String, u32> =
                    authors.iter().map(|(a, c)| (a.to_string(), *c)).collect();
                (path.to_string(), author_map)
            })
            .collect()
    }

    #[test]
    fn test_empty_input() {
        let report = compute_knowledge(&FxHashMap::default());
        assert!(report.files.is_empty());
        assert_eq!(report.total_silos, 0);
        assert!((report.silo_percentage - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_single_owner_is_silo() {
        let data = make_file_authors(&[("src/main.rs", &[("Alice", 10)])]);
        let report = compute_knowledge(&data);
        assert_eq!(report.files.len(), 1);
        assert!(report.files[0].is_silo);
        assert_eq!(report.files[0].primary_owner, "Alice");
        assert!((report.files[0].knowledge_entropy - 0.0).abs() < f64::EPSILON);
        assert_eq!(report.total_silos, 1);
        assert!((report.silo_percentage - 100.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_two_equal_owners_not_silo() {
        let data = make_file_authors(&[("src/lib.rs", &[("Alice", 5), ("Bob", 5)])]);
        let report = compute_knowledge(&data);
        assert_eq!(report.files.len(), 1);
        assert!(!report.files[0].is_silo);
        // Shannon entropy for 50/50 split = 1.0 bit
        assert!(
            (report.files[0].knowledge_entropy - 1.0).abs() < f64::EPSILON,
            "entropy={}, expected=1.0",
            report.files[0].knowledge_entropy
        );
    }

    #[test]
    fn test_entropy_three_equal_owners() {
        let data = make_file_authors(&[("test.rs", &[("Alice", 10), ("Bob", 10), ("Carol", 10)])]);
        let report = compute_knowledge(&data);
        // Entropy for uniform 1/3 distribution = log2(3) ≈ 1.585
        let expected = 3.0_f64.log2();
        assert!(
            (report.files[0].knowledge_entropy - expected).abs() < 1e-10,
            "entropy={}, expected={}",
            report.files[0].knowledge_entropy,
            expected
        );
    }

    #[test]
    fn test_silo_percentage() {
        let data = make_file_authors(&[
            ("a.rs", &[("Alice", 10)]),            // silo
            ("b.rs", &[("Alice", 5), ("Bob", 5)]), // not silo
            ("c.rs", &[("Carol", 10)]),            // silo
        ]);
        let report = compute_knowledge(&data);
        assert_eq!(report.total_silos, 2);
        // 2/3 = 66.67%
        assert!(
            (report.silo_percentage - 200.0 / 3.0).abs() < 0.01,
            "silo_percentage={}, expected=66.67",
            report.silo_percentage
        );
    }

    #[test]
    fn test_sorted_by_entropy_ascending() {
        let data = make_file_authors(&[
            ("high.rs", &[("Alice", 5), ("Bob", 5)]), // entropy = 1.0
            ("low.rs", &[("Alice", 10)]),             // entropy = 0.0
            ("mid.rs", &[("Alice", 7), ("Bob", 3)]),  // entropy ≈ 0.88
        ]);
        let report = compute_knowledge(&data);
        assert_eq!(report.files[0].path, "low.rs");
        assert!(report.files[0].knowledge_entropy <= report.files[1].knowledge_entropy);
        assert!(report.files[1].knowledge_entropy <= report.files[2].knowledge_entropy);
    }

    #[test]
    fn test_directory_aggregation() {
        let data = make_file_authors(&[
            ("src/a.rs", &[("Alice", 10)]),              // silo
            ("src/b.rs", &[("Alice", 10)]),              // silo
            ("tests/c.rs", &[("Alice", 5), ("Bob", 5)]), // not silo
        ]);
        let report = compute_knowledge(&data);
        let src = report.directories.iter().find(|d| d.directory == "src");
        assert!(src.is_some());
        let src = src.unwrap();
        assert_eq!(src.file_count, 2);
        assert_eq!(src.silo_count, 2);
        assert!((src.silo_percentage - 100.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_root_directory_files() {
        let data = make_file_authors(&[("README.md", &[("Alice", 1)])]);
        let report = compute_knowledge(&data);
        let root = report.directories.iter().find(|d| d.directory == ".");
        assert!(root.is_some());
        assert_eq!(root.unwrap().file_count, 1);
    }

    #[test]
    fn test_avg_entropy() {
        let data = make_file_authors(&[
            ("a.rs", &[("Alice", 10)]),            // entropy = 0
            ("b.rs", &[("Alice", 5), ("Bob", 5)]), // entropy = 1.0
        ]);
        let report = compute_knowledge(&data);
        assert!(
            (report.avg_entropy - 0.5).abs() < f64::EPSILON,
            "avg_entropy={}, expected=0.5",
            report.avg_entropy
        );
    }

    #[test]
    fn test_entropy_asymmetric_ownership() {
        // Alice: 9/10, Bob: 1/10
        // H = -(0.9 * log2(0.9) + 0.1 * log2(0.1)) ≈ 0.469
        let data = make_file_authors(&[("test.rs", &[("Alice", 9), ("Bob", 1)])]);
        let report = compute_knowledge(&data);
        let expected = -(0.9_f64 * 0.9_f64.log2() + 0.1_f64 * 0.1_f64.log2());
        assert!(
            (report.files[0].knowledge_entropy - expected).abs() < 1e-10,
            "entropy={}, expected={}",
            report.files[0].knowledge_entropy,
            expected
        );
    }

    #[test]
    fn test_two_contributors_not_silo() {
        // Kills mutant: contributor_count == 1 → contributor_count != 1
        let data = make_file_authors(&[("a.rs", &[("Alice", 8), ("Bob", 2)])]);
        let report = compute_knowledge(&data);
        assert!(
            !report.files[0].is_silo,
            "2 contributors should not be a silo"
        );
        assert_eq!(report.files[0].contributor_count, 2);
        assert_eq!(report.total_silos, 0);
    }

    #[test]
    fn test_silo_percentage_division() {
        // Kills mutant: replace / with * in silo_percentage = silos / total * 100
        // 1 silo out of 4 files = 25% (not 1*4*100 = 400)
        let data = make_file_authors(&[
            ("a.rs", &[("Alice", 10)]),              // silo
            ("b.rs", &[("Alice", 5), ("Bob", 5)]),   // not silo
            ("c.rs", &[("Alice", 3), ("Carol", 7)]), // not silo
            ("d.rs", &[("Alice", 1), ("Dave", 9)]),  // not silo
        ]);
        let report = compute_knowledge(&data);
        assert_eq!(report.total_silos, 1);
        assert!(
            (report.silo_percentage - 25.0).abs() < f64::EPSILON,
            "silo_pct={}, expected=25.0",
            report.silo_percentage
        );
    }

    #[test]
    fn test_avg_entropy_division() {
        // Kills mutant: replace / with * in avg_entropy calculation
        // 3 files with entropy [0, 1.0, log2(3)]
        // avg = (0 + 1.0 + log2(3)) / 3
        let data = make_file_authors(&[
            ("a.rs", &[("Alice", 10)]),                             // entropy = 0
            ("b.rs", &[("Alice", 5), ("Bob", 5)]),                  // entropy = 1.0
            ("c.rs", &[("Alice", 10), ("Bob", 10), ("Carol", 10)]), // entropy = log2(3)
        ]);
        let report = compute_knowledge(&data);
        let expected = (0.0 + 1.0 + 3.0_f64.log2()) / 3.0;
        assert!(
            (report.avg_entropy - expected).abs() < 1e-10,
            "avg_entropy={}, expected={}",
            report.avg_entropy,
            expected
        );
    }

    #[test]
    fn test_extract_directory_deep_path() {
        // "a/b/c.rs" → should give "a" (top-level only)
        let data = make_file_authors(&[("a/b/c.rs", &[("Alice", 5)])]);
        let report = compute_knowledge(&data);
        assert!(
            report.directories.iter().any(|d| d.directory == "a"),
            "deep path should map to top-level dir"
        );
    }

    #[test]
    fn test_directory_silo_percentage_exact() {
        // Kills mutant: replace / with * in directory silo_percentage
        let data = make_file_authors(&[
            ("src/a.rs", &[("Alice", 10)]),            // silo
            ("src/b.rs", &[("Alice", 5), ("Bob", 5)]), // not silo
            ("src/c.rs", &[("Alice", 5), ("Bob", 5)]), // not silo
        ]);
        let report = compute_knowledge(&data);
        let src = report
            .directories
            .iter()
            .find(|d| d.directory == "src")
            .unwrap();
        // 1 silo / 3 files * 100 = 33.33%
        let expected = 100.0 / 3.0;
        assert!(
            (src.silo_percentage - expected).abs() < 0.01,
            "dir_silo_pct={}, expected={}",
            src.silo_percentage,
            expected
        );
    }
}
