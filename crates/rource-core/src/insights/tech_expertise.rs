// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Developer Technology Expertise — infers developer skills from the file
//! types they modify in the repository.
//!
//! Maps each developer to the technologies they work with, based on file
//! extensions in their commit history. This provides a skills matrix
//! analogous to what `LinkedIn` or `GitHub` profiles show, but derived from
//! actual commit evidence.
//!
//! # Research Basis
//!
//! - Mockus & Herbsleb (2002) "Expertise Browser: A Quantitative Approach
//!   to Identifying Expertise" (ICSE) — identifying expertise from
//!   change history
//! - Fritz et al. (2010) "A Degree-of-Knowledge Model to Capture Source
//!   Code Familiarity" (ICSE) — expertise derived from interaction history
//!
//! # Algorithm
//!
//! 1. For each developer, collect file extensions from their commits
//! 2. Map extensions to technology categories (same mapping as
//!    `tech_distribution`)
//! 3. Count commits per technology per developer
//! 4. Rank technologies by commit count to produce expertise profile
//!
//! # Complexity
//!
//! - O(C × `F_avg`) where C = commits, `F_avg` = avg files per commit

use rustc_hash::FxHashMap;

/// Developer technology expertise report.
#[derive(Debug, Clone)]
pub struct TechExpertiseReport {
    /// Per-developer expertise profiles, sorted by total commits descending.
    pub developers: Vec<DeveloperExpertise>,
    /// Total developers with expertise data.
    pub developer_count: usize,
    /// Most common technology across all developers.
    pub dominant_tech: String,
}

/// Expertise profile for a single developer.
#[derive(Debug, Clone)]
pub struct DeveloperExpertise {
    /// Developer name.
    pub name: String,
    /// Technologies this developer works with, sorted by commit count.
    pub technologies: Vec<TechCommitCount>,
    /// Total commits by this developer.
    pub total_commits: u32,
    /// Number of distinct technologies used.
    pub tech_count: u32,
    /// Primary technology (highest commit count).
    pub primary_tech: String,
}

/// Commit count for a specific technology.
#[derive(Debug, Clone)]
pub struct TechCommitCount {
    /// Technology/language name.
    pub tech: String,
    /// Number of commits touching files of this technology.
    pub commits: u32,
    /// Percentage of this developer's commits.
    pub percentage: f64,
}

/// Accumulates per-developer technology data.
pub struct TechExpertiseAccumulator {
    /// Developer → (technology → commit count).
    dev_tech: FxHashMap<String, FxHashMap<String, u32>>,
    /// Developer → total commits.
    dev_commits: FxHashMap<String, u32>,
}

impl Default for TechExpertiseAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl TechExpertiseAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            dev_tech: FxHashMap::default(),
            dev_commits: FxHashMap::default(),
        }
    }

    /// Records a commit for tech expertise analysis.
    /// `techs` should be the set of unique technologies in this commit.
    pub fn record_commit(&mut self, author: &str, techs: &[&str]) {
        *self.dev_commits.entry(author.to_string()).or_default() += 1;

        let dev_entry = self.dev_tech.entry(author.to_string()).or_default();
        for &tech in techs {
            *dev_entry.entry(tech.to_string()).or_default() += 1;
        }
    }

    /// Finalizes the expertise report.
    #[must_use]
    pub fn finalize(self) -> TechExpertiseReport {
        if self.dev_tech.is_empty() {
            return TechExpertiseReport {
                developers: Vec::new(),
                developer_count: 0,
                dominant_tech: String::new(),
            };
        }

        let mut global_tech_counts: FxHashMap<String, u32> = FxHashMap::default();
        let mut developers: Vec<DeveloperExpertise> = Vec::new();

        for (dev, techs) in &self.dev_tech {
            let total_commits = self.dev_commits.get(dev).copied().unwrap_or(0);
            let total_f64 = f64::from(total_commits.max(1));

            let mut tech_list: Vec<TechCommitCount> = techs
                .iter()
                .map(|(tech, &count)| {
                    *global_tech_counts.entry(tech.clone()).or_default() += count;
                    TechCommitCount {
                        tech: tech.clone(),
                        commits: count,
                        percentage: f64::from(count) / total_f64 * 100.0,
                    }
                })
                .collect();

            tech_list.sort_by(|a, b| b.commits.cmp(&a.commits));

            let primary_tech = tech_list.first().map_or(String::new(), |t| t.tech.clone());

            developers.push(DeveloperExpertise {
                name: dev.clone(),
                technologies: tech_list,
                total_commits,
                tech_count: techs.len() as u32,
                primary_tech,
            });
        }

        developers.sort_by(|a, b| b.total_commits.cmp(&a.total_commits));

        let dominant_tech = global_tech_counts
            .iter()
            .max_by_key(|(_, &count)| count)
            .map_or(String::new(), |(tech, _)| tech.clone());

        TechExpertiseReport {
            developer_count: developers.len(),
            dominant_tech,
            developers,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let acc = TechExpertiseAccumulator::new();
        let report = acc.finalize();
        assert!(report.developers.is_empty());
        assert_eq!(report.developer_count, 0);
    }

    #[test]
    fn test_default_impl() {
        let acc = TechExpertiseAccumulator::default();
        let report = acc.finalize();
        assert!(report.developers.is_empty());
    }

    #[test]
    fn test_single_developer() {
        let mut acc = TechExpertiseAccumulator::new();
        acc.record_commit("Alice", &["Rust", "TOML"]);
        acc.record_commit("Alice", &["Rust"]);
        acc.record_commit("Alice", &["JavaScript"]);
        let report = acc.finalize();
        assert_eq!(report.developer_count, 1);
        let alice = &report.developers[0];
        assert_eq!(alice.name, "Alice");
        assert_eq!(alice.total_commits, 3);
        assert_eq!(alice.primary_tech, "Rust");
    }

    #[test]
    fn test_multiple_developers() {
        let mut acc = TechExpertiseAccumulator::new();
        acc.record_commit("Alice", &["Rust"]);
        acc.record_commit("Alice", &["Rust"]);
        acc.record_commit("Bob", &["JavaScript"]);
        let report = acc.finalize();
        assert_eq!(report.developer_count, 2);
        // Alice has more commits, so should be first
        assert_eq!(report.developers[0].name, "Alice");
    }

    #[test]
    fn test_dominant_tech() {
        let mut acc = TechExpertiseAccumulator::new();
        acc.record_commit("Alice", &["Rust"]);
        acc.record_commit("Alice", &["Rust"]);
        acc.record_commit("Bob", &["Rust"]);
        acc.record_commit("Bob", &["JavaScript"]);
        let report = acc.finalize();
        assert_eq!(report.dominant_tech, "Rust");
    }

    #[test]
    fn test_tech_percentages() {
        let mut acc = TechExpertiseAccumulator::new();
        acc.record_commit("Alice", &["Rust"]);
        acc.record_commit("Alice", &["Rust"]);
        acc.record_commit("Alice", &["JavaScript"]);
        acc.record_commit("Alice", &["JavaScript"]);
        let report = acc.finalize();
        let alice = &report.developers[0];
        for tech in &alice.technologies {
            assert!(
                (tech.percentage - 50.0).abs() < 0.01,
                "each tech should be ~50%: {}",
                tech.percentage
            );
        }
    }

    #[test]
    fn test_sorted_by_commits() {
        let mut acc = TechExpertiseAccumulator::new();
        for _ in 0..10 {
            acc.record_commit("Alice", &["Rust"]);
        }
        for _ in 0..5 {
            acc.record_commit("Bob", &["JavaScript"]);
        }
        for _ in 0..1 {
            acc.record_commit("Charlie", &["Python"]);
        }
        let report = acc.finalize();
        for w in report.developers.windows(2) {
            assert!(
                w[0].total_commits >= w[1].total_commits,
                "not sorted: {} < {}",
                w[0].total_commits,
                w[1].total_commits
            );
        }
    }
}
