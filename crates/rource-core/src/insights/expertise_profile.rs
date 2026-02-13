// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Expertise breadth vs depth profile analysis (M11).
//!
//! Classifies developers as specialists (deep in few files) or generalists
//! (shallow across many). Neither is inherently better — the team needs both.
//!
//! # Research Basis
//!
//! Mockus & Herbsleb (2002) "Expertise Browser: A Quantitative Approach to
//! Identifying Expertise" (ICSE, DOI: 10.1145/581339.581401).
//!
//! Fritz et al. (2010) "A Degree-of-Knowledge Model for Capturing Source
//! Code Familiarity" (FSE, DOI: 10.1145/1882291.1882300).
//!
//! # Algorithm
//!
//! Per developer:
//! - `breadth = unique_files_touched / total_files_in_repo`
//! - `depth = total_commits / unique_files_touched`
//! - Quadrant: Specialist-Deep (low breadth, high depth),
//!   Specialist-Shallow (low breadth, low depth),
//!   Generalist-Deep (high breadth, high depth),
//!   Generalist-Shallow (high breadth, low depth)
//!
//! # Complexity
//!
//! - Computed from `file_authors` map: O(A × F) where A = authors, F = files

use rustc_hash::FxHashMap;

/// Expertise quadrant classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpertiseQuadrant {
    /// Deep expertise in few areas.
    SpecialistDeep,
    /// Shallow in few areas (new contributor or disengaged).
    SpecialistShallow,
    /// Deep expertise across many areas (senior/architect).
    GeneralistDeep,
    /// Shallow across many areas (drive-by contributor).
    GeneralistShallow,
}

impl ExpertiseQuadrant {
    /// Returns a human-readable label.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::SpecialistDeep => "Specialist (Deep)",
            Self::SpecialistShallow => "Specialist (Shallow)",
            Self::GeneralistDeep => "Generalist (Deep)",
            Self::GeneralistShallow => "Generalist (Shallow)",
        }
    }
}

/// Per-developer expertise profile.
#[derive(Debug, Clone)]
pub struct DeveloperExpertiseProfile {
    /// Developer name.
    pub author: String,
    /// Quadrant classification.
    pub quadrant: ExpertiseQuadrant,
    /// Breadth score: `unique_files / total_files` ∈ [0, 1].
    pub breadth: f64,
    /// Depth score: `total_commits / unique_files`.
    pub depth: f64,
    /// Unique files touched.
    pub unique_files: u32,
    /// Total commits.
    pub total_commits: u32,
}

/// Complete expertise profile report.
#[derive(Debug, Clone)]
pub struct ExpertiseProfileReport {
    /// Per-developer expertise profiles.
    pub developers: Vec<DeveloperExpertiseProfile>,
    /// Count by quadrant.
    pub specialist_deep_count: usize,
    /// Count by quadrant.
    pub specialist_shallow_count: usize,
    /// Count by quadrant.
    pub generalist_deep_count: usize,
    /// Count by quadrant.
    pub generalist_shallow_count: usize,
    /// Median breadth across all developers.
    pub median_breadth: f64,
    /// Median depth across all developers.
    pub median_depth: f64,
}

/// Computes expertise profiles from `file_authors` data.
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn compute_expertise_profiles(
    file_authors: &FxHashMap<String, FxHashMap<String, u32>>,
) -> ExpertiseProfileReport {
    let total_files = file_authors.len() as f64;
    if total_files < 1.0 {
        return ExpertiseProfileReport {
            developers: Vec::new(),
            specialist_deep_count: 0,
            specialist_shallow_count: 0,
            generalist_deep_count: 0,
            generalist_shallow_count: 0,
            median_breadth: 0.0,
            median_depth: 0.0,
        };
    }

    // Aggregate per-developer
    let mut dev_stats: FxHashMap<String, (u32, u32)> = FxHashMap::default();
    for authors in file_authors.values() {
        for (author, &count) in authors {
            let entry = dev_stats.entry(author.clone()).or_insert((0, 0));
            entry.0 += count; // total commits
            entry.1 += 1; // unique files
        }
    }

    let mut developers: Vec<DeveloperExpertiseProfile> = dev_stats
        .into_iter()
        .map(|(author, (total_commits, unique_files))| {
            let breadth = f64::from(unique_files) / total_files;
            let depth = if unique_files > 0 {
                f64::from(total_commits) / f64::from(unique_files)
            } else {
                0.0
            };

            // Use median as threshold (computed later, use 0.5 as initial)
            DeveloperExpertiseProfile {
                author,
                quadrant: ExpertiseQuadrant::SpecialistShallow, // Will be updated
                breadth,
                depth,
                unique_files,
                total_commits,
            }
        })
        .collect();

    // Compute medians for quadrant classification
    let mut breadths: Vec<f64> = developers.iter().map(|d| d.breadth).collect();
    let mut depths: Vec<f64> = developers.iter().map(|d| d.depth).collect();
    breadths.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    depths.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

    let median_breadth = if breadths.is_empty() {
        0.0
    } else {
        breadths[breadths.len() / 2]
    };
    let median_depth = if depths.is_empty() {
        0.0
    } else {
        depths[depths.len() / 2]
    };

    // Classify quadrants
    for dev in &mut developers {
        dev.quadrant = if dev.breadth >= median_breadth && dev.depth >= median_depth {
            ExpertiseQuadrant::GeneralistDeep
        } else if dev.breadth >= median_breadth && dev.depth < median_depth {
            ExpertiseQuadrant::GeneralistShallow
        } else if dev.breadth < median_breadth && dev.depth >= median_depth {
            ExpertiseQuadrant::SpecialistDeep
        } else {
            ExpertiseQuadrant::SpecialistShallow
        };
    }

    // Sort by total commits descending
    developers.sort_by(|a, b| b.total_commits.cmp(&a.total_commits));
    developers.truncate(50);

    let specialist_deep_count = developers
        .iter()
        .filter(|d| d.quadrant == ExpertiseQuadrant::SpecialistDeep)
        .count();
    let specialist_shallow_count = developers
        .iter()
        .filter(|d| d.quadrant == ExpertiseQuadrant::SpecialistShallow)
        .count();
    let generalist_deep_count = developers
        .iter()
        .filter(|d| d.quadrant == ExpertiseQuadrant::GeneralistDeep)
        .count();
    let generalist_shallow_count = developers
        .iter()
        .filter(|d| d.quadrant == ExpertiseQuadrant::GeneralistShallow)
        .count();

    ExpertiseProfileReport {
        developers,
        specialist_deep_count,
        specialist_shallow_count,
        generalist_deep_count,
        generalist_shallow_count,
        median_breadth,
        median_depth,
    }
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
    fn test_empty() {
        let report = compute_expertise_profiles(&FxHashMap::default());
        assert!(report.developers.is_empty());
    }

    #[test]
    fn test_single_developer() {
        let data = make_file_authors(&[("a.rs", &[("Alice", 10)]), ("b.rs", &[("Alice", 5)])]);
        let report = compute_expertise_profiles(&data);
        assert_eq!(report.developers.len(), 1);
        assert!((report.developers[0].breadth - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_specialist_vs_generalist() {
        let data = make_file_authors(&[
            ("a.rs", &[("Alice", 50)]), // Alice: deep specialist
            ("b.rs", &[("Bob", 1)]),    // Bob touches many files
            ("c.rs", &[("Bob", 1)]),
            ("d.rs", &[("Bob", 1)]),
            ("e.rs", &[("Bob", 1)]),
        ]);
        let report = compute_expertise_profiles(&data);
        let alice = report
            .developers
            .iter()
            .find(|d| d.author == "Alice")
            .unwrap();
        let bob = report
            .developers
            .iter()
            .find(|d| d.author == "Bob")
            .unwrap();
        // Alice has low breadth (1/5) but high depth (50)
        // Bob has high breadth (4/5) but low depth (1)
        assert!(alice.depth > bob.depth);
        assert!(bob.breadth > alice.breadth);
    }

    #[test]
    fn test_quadrant_labels() {
        assert_eq!(
            ExpertiseQuadrant::SpecialistDeep.label(),
            "Specialist (Deep)"
        );
        assert_eq!(
            ExpertiseQuadrant::GeneralistShallow.label(),
            "Generalist (Shallow)"
        );
    }
}
