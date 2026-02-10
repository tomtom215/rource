// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Developer activity profiles.
//!
//! Builds per-developer activity summaries including total commits, files
//! touched, preferred directories, and contributor classification (core,
//! peripheral, drive-by).
//!
//! # Research Basis
//!
//! Mockus et al. (2002) "Two Case Studies of Open Source Software Development"
//! (TOSEM) established that OSS projects typically have a small core of
//! contributors responsible for most changes. Robles et al. (2005) showed
//! that contributor distribution follows a power law.
//!
//! # Algorithm
//!
//! For each author, accumulate: commit count, unique files touched, active
//! days, and per-directory commit counts. Classification:
//! - **Core**: > 10% of total commits AND active in the last 20% of time span
//! - **Peripheral**: regular contributor but below core threshold
//! - **Drive-by**: 1-2 commits total
//!
//! # Complexity
//!
//! - Accumulation: O(1) per commit per file
//! - Finalization: O(A log A) where A = number of authors

use rustc_hash::{FxHashMap, FxHashSet};

/// Minimum commits for core contributor classification.
const CORE_COMMIT_THRESHOLD_PCT: f64 = 0.10;

/// Maximum commits for drive-by classification.
const DRIVE_BY_MAX_COMMITS: usize = 2;

/// Fraction of time span considered "recent" for core classification.
const RECENCY_FRACTION: f64 = 0.20;

/// Contributor classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContributorType {
    /// Major contributor: high commit share and recently active.
    Core,
    /// Regular but lower-volume contributor.
    Peripheral,
    /// One-time or two-time contributor.
    DriveBy,
}

/// Activity profile for a single developer.
#[derive(Debug, Clone)]
pub struct DeveloperProfile {
    /// Author name.
    pub author: String,
    /// Total number of commits.
    pub commit_count: usize,
    /// Number of unique files touched.
    pub unique_files: usize,
    /// Average files per commit.
    pub avg_files_per_commit: f64,
    /// First commit timestamp (Unix seconds).
    pub first_commit: i64,
    /// Last commit timestamp (Unix seconds).
    pub last_commit: i64,
    /// Active span in days (last - first commit).
    pub active_span_days: f64,
    /// Contributor classification.
    pub classification: ContributorType,
    /// Top directories by commit count (max 3).
    pub preferred_directories: Vec<(String, usize)>,
}

/// Aggregate developer profiles report.
#[derive(Debug, Clone)]
pub struct ProfilesReport {
    /// Per-developer profiles, sorted by commit count descending.
    pub developers: Vec<DeveloperProfile>,
    /// Number of core contributors.
    pub core_count: usize,
    /// Number of peripheral contributors.
    pub peripheral_count: usize,
    /// Number of drive-by contributors.
    pub drive_by_count: usize,
    /// Total active contributors (all types).
    pub total_contributors: usize,
}

/// Per-author accumulator data.
struct AuthorData {
    commit_count: usize,
    file_count_sum: usize,
    unique_files: FxHashSet<String>,
    first_commit: i64,
    last_commit: i64,
    dir_commits: FxHashMap<String, usize>,
}

/// Accumulates developer activity during commit processing.
pub struct ProfilesAccumulator {
    /// Author → accumulated data.
    authors: FxHashMap<String, AuthorData>,
}

impl Default for ProfilesAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl ProfilesAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            authors: FxHashMap::default(),
        }
    }

    /// Records a commit for developer profiling.
    ///
    /// # Arguments
    ///
    /// * `author` - Author name
    /// * `timestamp` - Unix epoch seconds
    /// * `file_paths` - Paths of files changed in this commit
    pub fn record_commit(&mut self, author: &str, timestamp: i64, file_paths: &[&str]) {
        let data = self
            .authors
            .entry(author.to_string())
            .or_insert(AuthorData {
                commit_count: 0,
                file_count_sum: 0,
                unique_files: FxHashSet::default(),
                first_commit: timestamp,
                last_commit: timestamp,
                dir_commits: FxHashMap::default(),
            });

        data.commit_count += 1;
        data.file_count_sum += file_paths.len();

        if timestamp < data.first_commit {
            data.first_commit = timestamp;
        }
        if timestamp > data.last_commit {
            data.last_commit = timestamp;
        }

        for &path in file_paths {
            data.unique_files.insert(path.to_string());
            let dir = extract_directory(path);
            *data.dir_commits.entry(dir).or_insert(0) += 1;
        }
    }

    /// Finalizes the accumulator into a [`ProfilesReport`].
    ///
    /// # Arguments
    ///
    /// * `total_commits` - Total commits across all authors
    /// * `t_min` - Earliest commit timestamp
    /// * `t_max` - Latest commit timestamp
    #[must_use]
    pub fn finalize(self, total_commits: usize, t_min: i64, t_max: i64) -> ProfilesReport {
        let time_span = (t_max - t_min) as f64;
        let recency_threshold = t_max as f64 - time_span * RECENCY_FRACTION;

        let mut developers: Vec<DeveloperProfile> = self
            .authors
            .into_iter()
            .map(|(author, data)| build_profile(author, data, total_commits, recency_threshold))
            .collect();

        developers.sort_by(|a, b| b.commit_count.cmp(&a.commit_count));

        let core_count = developers
            .iter()
            .filter(|d| d.classification == ContributorType::Core)
            .count();
        let peripheral_count = developers
            .iter()
            .filter(|d| d.classification == ContributorType::Peripheral)
            .count();
        let drive_by_count = developers
            .iter()
            .filter(|d| d.classification == ContributorType::DriveBy)
            .count();

        ProfilesReport {
            total_contributors: developers.len(),
            developers,
            core_count,
            peripheral_count,
            drive_by_count,
        }
    }
}

/// Builds a developer profile from accumulated data.
fn build_profile(
    author: String,
    data: AuthorData,
    total_commits: usize,
    recency_threshold: f64,
) -> DeveloperProfile {
    let avg_files = if data.commit_count > 0 {
        data.file_count_sum as f64 / data.commit_count as f64
    } else {
        0.0
    };

    let active_span_days = (data.last_commit - data.first_commit) as f64 / 86400.0;

    // Top 3 directories by commit count
    let mut dir_vec: Vec<(String, usize)> = data.dir_commits.into_iter().collect();
    dir_vec.sort_by(|a, b| b.1.cmp(&a.1));
    dir_vec.truncate(3);

    let classification = classify_contributor(
        data.commit_count,
        total_commits,
        data.last_commit as f64,
        recency_threshold,
    );

    DeveloperProfile {
        author,
        commit_count: data.commit_count,
        unique_files: data.unique_files.len(),
        avg_files_per_commit: avg_files,
        first_commit: data.first_commit,
        last_commit: data.last_commit,
        active_span_days,
        classification,
        preferred_directories: dir_vec,
    }
}

/// Classifies a contributor based on commit share and recency.
fn classify_contributor(
    commit_count: usize,
    total_commits: usize,
    last_commit: f64,
    recency_threshold: f64,
) -> ContributorType {
    if commit_count <= DRIVE_BY_MAX_COMMITS {
        return ContributorType::DriveBy;
    }

    let share = if total_commits > 0 {
        commit_count as f64 / total_commits as f64
    } else {
        0.0
    };

    if share >= CORE_COMMIT_THRESHOLD_PCT && last_commit >= recency_threshold {
        ContributorType::Core
    } else {
        ContributorType::Peripheral
    }
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

    #[test]
    fn test_empty_accumulator() {
        let acc = ProfilesAccumulator::new();
        let report = acc.finalize(0, 0, 0);
        assert!(report.developers.is_empty());
        assert_eq!(report.total_contributors, 0);
    }

    #[test]
    fn test_single_developer() {
        let mut acc = ProfilesAccumulator::new();
        acc.record_commit("Alice", 1000, &["src/main.rs", "src/lib.rs"]);
        acc.record_commit("Alice", 2000, &["src/main.rs"]);

        let report = acc.finalize(2, 1000, 2000);
        assert_eq!(report.developers.len(), 1);
        let alice = &report.developers[0];
        assert_eq!(alice.author, "Alice");
        assert_eq!(alice.commit_count, 2);
        assert_eq!(alice.unique_files, 2);
        assert!((alice.avg_files_per_commit - 1.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_drive_by_classification() {
        let mut acc = ProfilesAccumulator::new();
        // Only 1 commit → drive-by
        acc.record_commit("Guest", 5000, &["README.md"]);

        let report = acc.finalize(100, 0, 10000);
        assert_eq!(
            report.developers[0].classification,
            ContributorType::DriveBy
        );
        assert_eq!(report.drive_by_count, 1);
    }

    #[test]
    fn test_core_classification() {
        let mut acc = ProfilesAccumulator::new();
        // 20 commits out of 100 (20%) and recent → core
        for i in 0..20 {
            acc.record_commit("Alice", 8000 + i * 100, &["src/main.rs"]);
        }

        let report = acc.finalize(100, 0, 10000);
        assert_eq!(report.developers[0].classification, ContributorType::Core);
        assert_eq!(report.core_count, 1);
    }

    #[test]
    fn test_peripheral_classification() {
        let mut acc = ProfilesAccumulator::new();
        // 5 commits out of 100 (5%) → peripheral (below 10% threshold)
        for i in 0..5 {
            acc.record_commit("Bob", 8000 + i * 100, &["src/lib.rs"]);
        }

        let report = acc.finalize(100, 0, 10000);
        assert_eq!(
            report.developers[0].classification,
            ContributorType::Peripheral
        );
        assert_eq!(report.peripheral_count, 1);
    }

    #[test]
    fn test_not_recent_is_peripheral() {
        let mut acc = ProfilesAccumulator::new();
        // 50 commits (50% share) but all early → peripheral despite high share
        for i in 0..50 {
            acc.record_commit("Alice", i * 100, &["src/main.rs"]);
        }

        let report = acc.finalize(100, 0, 100_000);
        // last_commit = 4900, recency_threshold = 100000 - 20000 = 80000
        assert_eq!(
            report.developers[0].classification,
            ContributorType::Peripheral
        );
    }

    #[test]
    fn test_sorted_by_commit_count() {
        let mut acc = ProfilesAccumulator::new();
        for i in 0..3 {
            acc.record_commit("Alice", i * 1000, &["a.rs"]);
        }
        for i in 0..5 {
            acc.record_commit("Bob", i * 1000, &["b.rs"]);
        }

        let report = acc.finalize(8, 0, 5000);
        assert_eq!(report.developers[0].author, "Bob");
        assert_eq!(report.developers[1].author, "Alice");
    }

    #[test]
    fn test_preferred_directories() {
        let mut acc = ProfilesAccumulator::new();
        acc.record_commit("Alice", 1000, &["src/a.rs", "src/b.rs"]);
        acc.record_commit("Alice", 2000, &["src/c.rs"]);
        acc.record_commit("Alice", 3000, &["tests/t.rs"]);
        acc.record_commit("Alice", 4000, &["docs/d.md"]);

        let report = acc.finalize(4, 1000, 4000);
        let alice = &report.developers[0];
        // src: 3 file touches, tests: 1, docs: 1
        assert_eq!(alice.preferred_directories[0].0, "src");
        assert_eq!(alice.preferred_directories[0].1, 3);
        assert!(alice.preferred_directories.len() <= 3);
    }

    #[test]
    fn test_active_span_days() {
        let mut acc = ProfilesAccumulator::new();
        // 10 days apart
        acc.record_commit("Alice", 0, &["a.rs"]);
        acc.record_commit("Alice", 10 * 86400, &["b.rs"]);

        let report = acc.finalize(2, 0, 10 * 86400);
        assert!(
            (report.developers[0].active_span_days - 10.0).abs() < f64::EPSILON,
            "active_span_days={}, expected=10.0",
            report.developers[0].active_span_days
        );
    }

    #[test]
    fn test_first_last_commit() {
        let mut acc = ProfilesAccumulator::new();
        acc.record_commit("Alice", 5000, &["a.rs"]);
        acc.record_commit("Alice", 1000, &["b.rs"]); // Earlier!
        acc.record_commit("Alice", 9000, &["c.rs"]);

        let report = acc.finalize(3, 1000, 9000);
        let alice = &report.developers[0];
        assert_eq!(alice.first_commit, 1000);
        assert_eq!(alice.last_commit, 9000);
    }

    #[test]
    fn test_default() {
        let acc = ProfilesAccumulator::default();
        let report = acc.finalize(0, 0, 0);
        assert!(report.developers.is_empty());
    }

    #[test]
    fn test_root_directory_tracking() {
        let mut acc = ProfilesAccumulator::new();
        acc.record_commit("Alice", 1000, &["README.md", "LICENSE"]);

        let report = acc.finalize(1, 1000, 1000);
        let alice = &report.developers[0];
        assert!(alice.preferred_directories.iter().any(|(d, _)| d == "."));
    }
}
