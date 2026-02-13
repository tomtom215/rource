// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Code reviewer recommendation engine (M9).
//!
//! Recommends the most qualified reviewers for each file based on ownership,
//! recency, and review history (approximated from subsequent edits by different
//! authors).
//!
//! # Research Basis
//!
//! Thongtanunam et al. (2015) "Who Should Review My Code?" (SANER,
//! DOI: 10.1109/SANER.2015.7081824) — file-path-based reviewer recommendation.
//!
//! Balachandran (2013) "Reducing Human Effort and Improving Quality in Peer
//! Code Reviews" (ICSE) — line-level review authority.
//!
//! Xia et al. (2015) "Who Should Review This Change?" (FSE) — hybrid approach
//! combining file path similarity and review activity.
//!
//! # Algorithm
//!
//! `ReviewScore(d, f) = w₁·Ownership(d,f) + w₂·Recency(d,f) + w₃·ReviewFreq(d,f)`
//!
//! where:
//! - `Ownership(d,f)` = commits by d to f / total commits to f
//! - `Recency(d,f) = 1 / (1 + days_since_last_touch)`
//! - `ReviewFreq(d,f)` = number of times d edited f after someone else / total such events
//!
//! # Complexity
//!
//! - Accumulation: O(N) per commit
//! - Finalization: O(F × A²) where F = files, A = authors per file

use rustc_hash::FxHashMap;

// Weights for the composite reviewer score
const W_OWNERSHIP: f64 = 0.4;
const W_RECENCY: f64 = 0.35;
const W_REVIEW_FREQ: f64 = 0.25;

/// A recommended reviewer for a specific file.
#[derive(Debug, Clone)]
pub struct ReviewerRecommendation {
    /// File path.
    pub path: String,
    /// Recommended reviewers ranked by composite score.
    pub reviewers: Vec<ReviewerCandidate>,
}

/// A single reviewer candidate with scoring breakdown.
#[derive(Debug, Clone)]
pub struct ReviewerCandidate {
    /// Developer name.
    pub author: String,
    /// Composite review score ∈ [0, 1].
    pub score: f64,
    /// Ownership component: fraction of commits to this file.
    pub ownership: f64,
    /// Recency component: how recently they touched this file.
    pub recency: f64,
    /// Review frequency: how often they edit after others.
    pub review_freq: f64,
}

/// Complete reviewer recommendation report.
#[derive(Debug, Clone)]
pub struct ReviewerRecommendationReport {
    /// Per-file reviewer recommendations (top files by activity).
    pub files: Vec<ReviewerRecommendation>,
    /// Average number of qualified reviewers per file.
    pub avg_reviewers_per_file: f64,
    /// Files with only one qualified reviewer (single-point-of-failure).
    pub single_reviewer_count: usize,
    /// Total files analyzed.
    pub total_analyzed: usize,
}

/// Per-file accumulation state.
struct FileState {
    /// Author → commit count to this file.
    author_commits: FxHashMap<String, u32>,
    /// Author → last commit timestamp.
    author_last_touch: FxHashMap<String, i64>,
    /// Author → count of edits that followed a different author.
    author_review_count: FxHashMap<String, u32>,
    /// Last author to touch this file (for review detection).
    last_author: Option<String>,
    /// Total "review-like" events (author change on file).
    total_review_events: u32,
}

/// Accumulates reviewer recommendation data from commit stream.
pub struct ReviewerRecommendationAccumulator {
    files: FxHashMap<String, FileState>,
}

impl Default for ReviewerRecommendationAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl ReviewerRecommendationAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            files: FxHashMap::default(),
        }
    }

    /// Records a file change within a commit.
    pub fn record_file(&mut self, path: &str, author: &str, timestamp: i64) {
        let state = self
            .files
            .entry(path.to_string())
            .or_insert_with(|| FileState {
                author_commits: FxHashMap::default(),
                author_last_touch: FxHashMap::default(),
                author_review_count: FxHashMap::default(),
                last_author: None,
                total_review_events: 0,
            });

        *state.author_commits.entry(author.to_string()).or_insert(0) += 1;
        state
            .author_last_touch
            .insert(author.to_string(), timestamp);

        // If this author is different from the last one, count as a review-like event
        if let Some(ref last) = state.last_author {
            if last != author {
                *state
                    .author_review_count
                    .entry(author.to_string())
                    .or_insert(0) += 1;
                state.total_review_events += 1;
            }
        }
        state.last_author = Some(author.to_string());
    }

    /// Finalizes the reviewer recommendation report.
    #[must_use]
    pub fn finalize(self, t_max: i64) -> ReviewerRecommendationReport {
        let total_analyzed = self.files.len();
        let mut files: Vec<ReviewerRecommendation> = self
            .files
            .into_iter()
            .filter_map(|(path, state)| {
                let total_commits: u32 = state.author_commits.values().sum();
                if total_commits < 2 {
                    return None;
                }

                let mut reviewers: Vec<ReviewerCandidate> = state
                    .author_commits
                    .iter()
                    .map(|(author, &commits)| {
                        let ownership = f64::from(commits) / f64::from(total_commits);

                        let last_touch = state.author_last_touch.get(author).copied().unwrap_or(0);
                        let days_since = ((t_max - last_touch) as f64 / 86400.0).max(0.0);
                        let recency = 1.0 / (1.0 + days_since);

                        let review_count =
                            state.author_review_count.get(author).copied().unwrap_or(0);
                        let review_freq = if state.total_review_events > 0 {
                            f64::from(review_count) / f64::from(state.total_review_events)
                        } else {
                            0.0
                        };

                        let score = W_OWNERSHIP * ownership
                            + W_RECENCY * recency
                            + W_REVIEW_FREQ * review_freq;

                        ReviewerCandidate {
                            author: author.clone(),
                            score,
                            ownership,
                            recency,
                            review_freq,
                        }
                    })
                    .collect();

                reviewers.sort_by(|a, b| {
                    b.score
                        .partial_cmp(&a.score)
                        .unwrap_or(std::cmp::Ordering::Equal)
                });
                reviewers.truncate(5);

                Some(ReviewerRecommendation { path, reviewers })
            })
            .collect();

        files.sort_by(|a, b| {
            let a_top = a.reviewers.first().map_or(0.0, |r| r.score);
            let b_top = b.reviewers.first().map_or(0.0, |r| r.score);
            b_top
                .partial_cmp(&a_top)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        files.truncate(50);

        let single_reviewer_count = files
            .iter()
            .filter(|f| f.reviewers.iter().filter(|r| r.score > 0.1).count() <= 1)
            .count();

        let avg_reviewers_per_file = if files.is_empty() {
            0.0
        } else {
            files
                .iter()
                .map(|f| f.reviewers.iter().filter(|r| r.score > 0.1).count() as f64)
                .sum::<f64>()
                / files.len() as f64
        };

        ReviewerRecommendationReport {
            files,
            avg_reviewers_per_file,
            single_reviewer_count,
            total_analyzed,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let acc = ReviewerRecommendationAccumulator::new();
        let report = acc.finalize(1000);
        assert!(report.files.is_empty());
        assert_eq!(report.total_analyzed, 0);
    }

    #[test]
    fn test_single_file_two_authors() {
        let mut acc = ReviewerRecommendationAccumulator::new();
        acc.record_file("src/main.rs", "Alice", 100);
        acc.record_file("src/main.rs", "Bob", 200);
        acc.record_file("src/main.rs", "Alice", 300);
        let report = acc.finalize(300);
        assert_eq!(report.files.len(), 1);
        assert_eq!(report.files[0].reviewers.len(), 2);
        // Alice has more commits (2/3) and more recency
        assert_eq!(report.files[0].reviewers[0].author, "Alice");
    }

    #[test]
    fn test_review_detection() {
        let mut acc = ReviewerRecommendationAccumulator::new();
        // Alice → Bob → Alice pattern = Bob reviewed, Alice reviewed
        acc.record_file("a.rs", "Alice", 100);
        acc.record_file("a.rs", "Bob", 200);
        acc.record_file("a.rs", "Alice", 300);
        let report = acc.finalize(300);
        let reviewers = &report.files[0].reviewers;
        // Both should have review_freq > 0
        let alice = reviewers.iter().find(|r| r.author == "Alice").unwrap();
        let bob = reviewers.iter().find(|r| r.author == "Bob").unwrap();
        assert!(alice.review_freq > 0.0);
        assert!(bob.review_freq > 0.0);
    }

    #[test]
    fn test_ownership_fraction() {
        let mut acc = ReviewerRecommendationAccumulator::new();
        for _ in 0..8 {
            acc.record_file("a.rs", "Alice", 100);
        }
        for _ in 0..2 {
            acc.record_file("a.rs", "Bob", 200);
        }
        let report = acc.finalize(200);
        let alice = report.files[0]
            .reviewers
            .iter()
            .find(|r| r.author == "Alice")
            .unwrap();
        assert!((alice.ownership - 0.8).abs() < 1e-10);
    }

    #[test]
    fn test_default_impl() {
        let acc = ReviewerRecommendationAccumulator::default();
        let report = acc.finalize(0);
        assert!(report.files.is_empty());
    }
}
