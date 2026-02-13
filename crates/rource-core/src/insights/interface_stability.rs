// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Interface stability score analysis (M23).
//!
//! Measures how stable the boundaries between modules are. Stable interfaces
//! enable independent development; unstable interfaces force coordination.
//!
//! # Research Basis
//!
//! Martin (2003) "Agile Software Development: Principles, Patterns, and
//! Practices" — Stable Dependencies Principle (SDP) and Stable Abstractions
//! Principle (SAP).
//!
//! `MacCormack` et al. (2006) "Exploring the Structure of Complex Software
//! Designs: An Empirical Study of Open Source and Proprietary Code"
//! (Management Science, DOI: 10.1287/mnsc.1060.0552).
//!
//! # Algorithm
//!
//! For each directory boundary:
//! 1. Track files that are modified by authors from multiple directories
//!    (proxy for "interface" files).
//! 2. `Stability(boundary) = 1 - (interface_changes / total_boundary_file_changes)`
//! 3. Low stability = volatile boundary requiring frequent coordination.
//!
//! # Complexity
//!
//! - Accumulation: O(1) per file change
//! - Finalization: O(F) where F = unique files

use rustc_hash::FxHashMap;

/// Stability assessment for a directory boundary.
#[derive(Debug, Clone)]
pub struct DirectoryStability {
    /// Directory path.
    pub directory: String,
    /// Stability score ∈ [0, 1]. Higher = more stable.
    pub stability: f64,
    /// Total changes to files in this directory.
    pub total_changes: u32,
    /// Changes from authors whose primary directory is different.
    pub cross_boundary_changes: u32,
    /// Number of unique external contributors.
    pub external_contributor_count: u32,
    /// Number of files in this directory.
    pub file_count: u32,
}

/// Complete interface stability report.
#[derive(Debug, Clone)]
pub struct InterfaceStabilityReport {
    /// Per-directory stability scores (sorted by stability ascending = least stable first).
    pub directories: Vec<DirectoryStability>,
    /// Average stability across all directories.
    pub avg_stability: f64,
    /// Directories with stability < 0.5 (volatile boundaries).
    pub volatile_count: usize,
    /// Directories with stability >= 0.8 (stable boundaries).
    pub stable_count: usize,
    /// Total directories analyzed.
    pub total_analyzed: usize,
}

/// Per-file tracking state.
struct FileEntry {
    directory: String,
    changes: u32,
    authors: FxHashMap<String, u32>,
}

/// Per-author tracking: which directory is their "home".
struct AuthorProfile {
    dir_commits: FxHashMap<String, u32>,
}

/// Accumulates interface stability data from commit stream.
pub struct InterfaceStabilityAccumulator {
    files: FxHashMap<String, FileEntry>,
    authors: FxHashMap<String, AuthorProfile>,
}

impl Default for InterfaceStabilityAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl InterfaceStabilityAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            files: FxHashMap::default(),
            authors: FxHashMap::default(),
        }
    }

    /// Records a file change within a commit.
    pub fn record_file(&mut self, path: &str, author: &str) {
        let dir = extract_directory(path);

        let entry = self
            .files
            .entry(path.to_string())
            .or_insert_with(|| FileEntry {
                directory: dir.clone(),
                changes: 0,
                authors: FxHashMap::default(),
            });
        entry.changes += 1;
        *entry.author_commits_entry(author) += 1;

        let profile = self
            .authors
            .entry(author.to_string())
            .or_insert_with(|| AuthorProfile {
                dir_commits: FxHashMap::default(),
            });
        *profile.dir_commits.entry(dir).or_insert(0) += 1;
    }

    /// Finalizes the interface stability report.
    #[must_use]
    pub fn finalize(self) -> InterfaceStabilityReport {
        // Determine each author's primary directory
        let author_primary: FxHashMap<&str, &str> = self
            .authors
            .iter()
            .map(|(author, profile)| {
                let primary = profile
                    .dir_commits
                    .iter()
                    .max_by_key(|(_, &v)| v)
                    .map_or(".", |(k, _)| k.as_str());
                (author.as_str(), primary)
            })
            .collect();

        // Aggregate per-directory
        let mut dir_stats: FxHashMap<String, (u32, u32, rustc_hash::FxHashSet<String>, u32)> =
            FxHashMap::default();

        for entry in self.files.values() {
            let stat = dir_stats
                .entry(entry.directory.clone())
                .or_insert_with(|| (0, 0, rustc_hash::FxHashSet::default(), 0));
            stat.0 += entry.changes; // total changes
            stat.3 += 1; // file count

            for (author, &count) in &entry.authors {
                let primary = author_primary.get(author.as_str()).copied().unwrap_or(".");
                if primary != entry.directory {
                    stat.1 += count; // cross-boundary changes
                    stat.2.insert(author.clone()); // external contributors
                }
            }
        }

        let total_analyzed = dir_stats.len();
        let mut directories: Vec<DirectoryStability> = dir_stats
            .into_iter()
            .map(
                |(directory, (total_changes, cross_boundary, external_authors, file_count))| {
                    let stability = if total_changes == 0 {
                        1.0
                    } else {
                        1.0 - f64::from(cross_boundary) / f64::from(total_changes)
                    };
                    DirectoryStability {
                        directory,
                        stability,
                        total_changes,
                        cross_boundary_changes: cross_boundary,
                        external_contributor_count: external_authors.len() as u32,
                        file_count,
                    }
                },
            )
            .collect();

        directories.sort_by(|a, b| {
            a.stability
                .partial_cmp(&b.stability)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        directories.truncate(50);

        let volatile_count = directories.iter().filter(|d| d.stability < 0.5).count();
        let stable_count = directories.iter().filter(|d| d.stability >= 0.8).count();
        let avg_stability = if directories.is_empty() {
            1.0
        } else {
            directories.iter().map(|d| d.stability).sum::<f64>() / directories.len() as f64
        };

        InterfaceStabilityReport {
            directories,
            avg_stability,
            volatile_count,
            stable_count,
            total_analyzed,
        }
    }
}

impl FileEntry {
    fn author_commits_entry(&mut self, author: &str) -> &mut u32 {
        self.authors.entry(author.to_string()).or_insert(0)
    }
}

/// Extracts the top-level directory from a file path.
fn extract_directory(path: &str) -> String {
    path.rsplit_once('/').map_or_else(
        || ".".to_string(),
        |(d, _)| d.split('/').next().unwrap_or(".").to_string(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let acc = InterfaceStabilityAccumulator::new();
        let report = acc.finalize();
        assert!(report.directories.is_empty());
        assert!((report.avg_stability - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_single_author_single_dir() {
        let mut acc = InterfaceStabilityAccumulator::new();
        acc.record_file("src/main.rs", "Alice");
        acc.record_file("src/lib.rs", "Alice");
        let report = acc.finalize();
        assert_eq!(report.directories.len(), 1);
        assert!((report.directories[0].stability - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_cross_boundary_author() {
        let mut acc = InterfaceStabilityAccumulator::new();
        // Alice primarily works in src/
        for _ in 0..10 {
            acc.record_file("src/main.rs", "Alice");
        }
        // Bob primarily works in tests/
        for _ in 0..10 {
            acc.record_file("tests/test.rs", "Bob");
        }
        // Bob also touches src/ (cross-boundary)
        acc.record_file("src/lib.rs", "Bob");

        let report = acc.finalize();
        let src_dir = report
            .directories
            .iter()
            .find(|d| d.directory == "src")
            .unwrap();
        // 11 total changes to src/, 1 from Bob (cross-boundary)
        assert_eq!(src_dir.total_changes, 11);
        assert_eq!(src_dir.cross_boundary_changes, 1);
        assert!(src_dir.stability < 1.0);
    }

    #[test]
    fn test_default_impl() {
        let acc = InterfaceStabilityAccumulator::default();
        let report = acc.finalize();
        assert!(report.directories.is_empty());
    }
}
