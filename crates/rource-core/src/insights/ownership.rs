// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Code ownership and bus factor analysis.
//!
//! # Code Ownership
//!
//! Tracks per-file contribution distribution to identify:
//! - **Concentrated ownership**: Single contributor dominates (key-person risk)
//! - **Diffuse ownership**: Many low-expertise contributors (quality risk)
//!
//! Research: Bird et al. (2011) "Don't Touch My Code!" found that ownership
//! metrics correlate with both pre-release defects and post-release failures.
//!
//! # Bus Factor
//!
//! The minimum number of people who must leave before a directory becomes
//! unmaintained. Computed using a greedy set cover algorithm.
//!
//! Research: Avelino et al. (2016) showed that many projects have bus factor
//! of 1-2, representing extreme knowledge concentration risk.

use rustc_hash::FxHashMap;

/// Ownership data for a single file.
#[derive(Debug, Clone)]
pub struct FileOwnership {
    /// File path relative to repository root.
    pub path: String,
    /// Name of the top contributor.
    pub top_owner: String,
    /// Share of changes by the top contributor (0.0-1.0).
    pub top_owner_share: f64,
    /// Total number of changes to this file.
    pub total_changes: u32,
    /// Number of distinct contributors.
    pub contributor_count: usize,
    /// All contributors sorted by change count descending.
    pub contributors: Vec<ContributorShare>,
}

/// A contributor's share of ownership for a file.
#[derive(Debug, Clone)]
pub struct ContributorShare {
    /// Contributor name.
    pub author: String,
    /// Number of changes by this contributor.
    pub changes: u32,
    /// Share of total changes (0.0-1.0).
    pub share: f64,
}

/// Bus factor for a directory.
#[derive(Debug, Clone)]
pub struct DirectoryBusFactor {
    /// Directory path.
    pub directory: String,
    /// Bus factor (minimum contributors whose departure causes knowledge loss).
    pub bus_factor: usize,
    /// Total unique files in this directory.
    pub file_count: usize,
    /// Total unique contributors to this directory.
    pub contributor_count: usize,
    /// The critical contributors (whose removal would be most damaging).
    pub critical_contributors: Vec<String>,
}

/// Computes ownership data for a single file.
///
/// # Arguments
///
/// * `path` - File path
/// * `authors` - Map of author name → change count for this file
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn compute_file_ownership(path: String, authors: &FxHashMap<String, u32>) -> FileOwnership {
    let total: u32 = authors.values().sum();
    let mut contributors: Vec<ContributorShare> = authors
        .iter()
        .map(|(author, &changes)| ContributorShare {
            author: author.clone(),
            changes,
            share: if total > 0 {
                f64::from(changes) / f64::from(total)
            } else {
                0.0
            },
        })
        .collect();

    // Sort by change count descending
    contributors.sort_by(|a, b| b.changes.cmp(&a.changes));

    let top_owner = contributors
        .first()
        .map_or_else(String::new, |c| c.author.clone());
    let top_owner_share = contributors.first().map_or(0.0, |c| c.share);

    FileOwnership {
        path,
        top_owner,
        top_owner_share,
        total_changes: total,
        contributor_count: contributors.len(),
        contributors,
    }
}

/// Computes bus factor for each top-level directory.
///
/// Uses a greedy set cover algorithm: repeatedly remove the contributor
/// who covers the most uncovered files, until some file has no contributor.
/// The bus factor is the number of removals needed to reach that state.
///
/// # Arguments
///
/// * `ownership` - Per-file ownership data
#[must_use]
pub fn compute_bus_factors(ownership: &[FileOwnership]) -> Vec<DirectoryBusFactor> {
    // Group files by top-level directory
    let mut dir_files: FxHashMap<String, Vec<&FileOwnership>> = FxHashMap::default();
    for file in ownership {
        let dir = extract_top_directory(&file.path);
        dir_files.entry(dir).or_default().push(file);
    }

    let mut results: Vec<DirectoryBusFactor> = dir_files
        .into_iter()
        .map(|(dir, files)| compute_single_bus_factor(dir, &files))
        .collect();

    // Sort by bus factor ascending (most at-risk first)
    results.sort_by_key(|d| d.bus_factor);
    results
}

/// Extracts the top-level directory from a file path.
///
/// "src/core/main.rs" → "src"
/// "README.md" → "."
fn extract_top_directory(path: &str) -> String {
    path.split('/')
        .next()
        .filter(|_| path.contains('/'))
        .unwrap_or(".")
        .to_string()
}

/// Computes bus factor for a single directory using greedy set cover.
fn compute_single_bus_factor(directory: String, files: &[&FileOwnership]) -> DirectoryBusFactor {
    // Build contributor → set of files mapping
    let mut contributor_files: FxHashMap<String, Vec<usize>> = FxHashMap::default();
    let mut all_contributors: FxHashMap<String, bool> = FxHashMap::default();

    for (idx, file) in files.iter().enumerate() {
        for contrib in &file.contributors {
            contributor_files
                .entry(contrib.author.clone())
                .or_default()
                .push(idx);
            all_contributors
                .entry(contrib.author.clone())
                .or_insert(true);
        }
    }

    let file_count = files.len();
    let contributor_count = all_contributors.len();

    if contributor_count == 0 {
        return DirectoryBusFactor {
            directory,
            bus_factor: 0,
            file_count,
            contributor_count: 0,
            critical_contributors: Vec::new(),
        };
    }

    // Greedy set cover: find minimum removal set
    let mut removed: FxHashMap<String, bool> = FxHashMap::default();
    let mut critical: Vec<String> = Vec::new();

    loop {
        // For each remaining contributor, count how many files they uniquely cover
        // (i.e., files where they are the only remaining contributor)
        let mut best_contributor: Option<String> = None;
        let mut best_coverage = 0usize;

        for author in all_contributors.keys() {
            if removed.contains_key(author) {
                continue;
            }
            let coverage = contributor_files.get(author).map_or(0, Vec::len);
            if coverage > best_coverage {
                best_coverage = coverage;
                best_contributor = Some(author.clone());
            }
        }

        let Some(contributor) = best_contributor else {
            break;
        };

        // Remove this contributor
        removed.insert(contributor.clone(), true);
        critical.push(contributor.clone());

        // Check if any file now has zero remaining contributors
        let has_orphan = (0..file_count).any(|file_idx| {
            // Count remaining contributors for this file
            files[file_idx]
                .contributors
                .iter()
                .all(|c| removed.contains_key(&c.author))
        });

        if has_orphan {
            break;
        }
    }

    DirectoryBusFactor {
        directory,
        bus_factor: critical.len(),
        file_count,
        contributor_count,
        critical_contributors: critical,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_authors(entries: &[(&str, u32)]) -> FxHashMap<String, u32> {
        entries.iter().map(|(k, v)| (k.to_string(), *v)).collect()
    }

    #[test]
    fn test_single_owner() {
        let authors = make_authors(&[("Alice", 10)]);
        let ownership = compute_file_ownership("test.rs".to_string(), &authors);

        assert_eq!(ownership.top_owner, "Alice");
        assert!((ownership.top_owner_share - 1.0).abs() < f64::EPSILON);
        assert_eq!(ownership.contributor_count, 1);
        assert_eq!(ownership.total_changes, 10);
    }

    #[test]
    fn test_two_owners() {
        let authors = make_authors(&[("Alice", 6), ("Bob", 4)]);
        let ownership = compute_file_ownership("test.rs".to_string(), &authors);

        assert_eq!(ownership.top_owner, "Alice");
        assert!((ownership.top_owner_share - 0.6).abs() < 0.01);
        assert_eq!(ownership.contributor_count, 2);
        assert_eq!(ownership.total_changes, 10);
    }

    #[test]
    fn test_contributors_sorted_by_changes() {
        let authors = make_authors(&[("Alice", 3), ("Bob", 7), ("Carol", 5)]);
        let ownership = compute_file_ownership("test.rs".to_string(), &authors);

        assert_eq!(ownership.contributors[0].author, "Bob");
        assert_eq!(ownership.contributors[1].author, "Carol");
        assert_eq!(ownership.contributors[2].author, "Alice");
    }

    #[test]
    fn test_empty_authors() {
        let authors: FxHashMap<String, u32> = FxHashMap::default();
        let ownership = compute_file_ownership("test.rs".to_string(), &authors);

        assert_eq!(ownership.contributor_count, 0);
        assert_eq!(ownership.total_changes, 0);
        assert!(ownership.top_owner.is_empty());
    }

    #[test]
    fn test_extract_top_directory() {
        assert_eq!(extract_top_directory("src/core/main.rs"), "src");
        assert_eq!(extract_top_directory("README.md"), ".");
        assert_eq!(extract_top_directory("docs/api/v2/ref.md"), "docs");
    }

    #[test]
    fn test_bus_factor_single_contributor() {
        let ownership = vec![FileOwnership {
            path: "src/main.rs".to_string(),
            top_owner: "Alice".to_string(),
            top_owner_share: 1.0,
            total_changes: 5,
            contributor_count: 1,
            contributors: vec![ContributorShare {
                author: "Alice".to_string(),
                changes: 5,
                share: 1.0,
            }],
        }];

        let factors = compute_bus_factors(&ownership);
        let src = factors.iter().find(|f| f.directory == "src");
        assert!(src.is_some());
        assert_eq!(src.unwrap().bus_factor, 1);
    }

    #[test]
    fn test_bus_factor_two_contributors_overlapping() {
        // Both Alice and Bob contributed to src/main.rs
        let ownership = vec![FileOwnership {
            path: "src/main.rs".to_string(),
            top_owner: "Alice".to_string(),
            top_owner_share: 0.6,
            total_changes: 10,
            contributor_count: 2,
            contributors: vec![
                ContributorShare {
                    author: "Alice".to_string(),
                    changes: 6,
                    share: 0.6,
                },
                ContributorShare {
                    author: "Bob".to_string(),
                    changes: 4,
                    share: 0.4,
                },
            ],
        }];

        let factors = compute_bus_factors(&ownership);
        let src = factors.iter().find(|f| f.directory == "src");
        assert!(src.is_some());
        // Need to remove both Alice AND Bob before the file is orphaned
        assert_eq!(src.unwrap().bus_factor, 2);
    }

    #[test]
    fn test_bus_factor_disjoint_files() {
        // Alice owns file1, Bob owns file2 — bus factor is 1
        // (removing either orphans their file)
        let ownership = vec![
            FileOwnership {
                path: "src/file1.rs".to_string(),
                top_owner: "Alice".to_string(),
                top_owner_share: 1.0,
                total_changes: 5,
                contributor_count: 1,
                contributors: vec![ContributorShare {
                    author: "Alice".to_string(),
                    changes: 5,
                    share: 1.0,
                }],
            },
            FileOwnership {
                path: "src/file2.rs".to_string(),
                top_owner: "Bob".to_string(),
                top_owner_share: 1.0,
                total_changes: 3,
                contributor_count: 1,
                contributors: vec![ContributorShare {
                    author: "Bob".to_string(),
                    changes: 3,
                    share: 1.0,
                }],
            },
        ];

        let factors = compute_bus_factors(&ownership);
        let src = factors.iter().find(|f| f.directory == "src");
        assert!(src.is_some());
        // Removing the greedy-chosen contributor orphans their file
        assert_eq!(src.unwrap().bus_factor, 1);
    }

    #[test]
    fn test_bus_factor_empty() {
        let factors = compute_bus_factors(&[]);
        assert!(factors.is_empty());
    }

    #[test]
    fn test_share_precision() {
        let authors = make_authors(&[("Alice", 1), ("Bob", 2)]);
        let ownership = compute_file_ownership("test.rs".to_string(), &authors);
        let alice = ownership
            .contributors
            .iter()
            .find(|c| c.author == "Alice")
            .unwrap();
        let bob = ownership
            .contributors
            .iter()
            .find(|c| c.author == "Bob")
            .unwrap();

        assert!((alice.share - 1.0 / 3.0).abs() < 0.001);
        assert!((bob.share - 2.0 / 3.0).abs() < 0.001);
    }
}
