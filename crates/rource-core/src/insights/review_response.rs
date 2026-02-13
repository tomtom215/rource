// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Review response time distribution analysis (M19).
//!
//! Measures how quickly changes get reviewed by computing commit-to-next-
//! different-author-commit intervals on the same file. This approximates
//! review response time from pure git history without requiring code review
//! platform data.
//!
//! # Research Basis
//!
//! Rigby & Storey (2011) "Understanding Broadcast Based Peer Review on an
//! Open Source Software Project" (ICSE) — peer review response time analysis.
//!
//! Baysal et al. (2016) "Investigating Technical and Non-Technical Factors
//! Influencing Modern Code Review" (ESE, DOI: 10.1007/s10664-015-9404-9).
//!
//! # Algorithm
//!
//! For each file, track author sequence. When author changes, measure time
//! delta. Report P50, P90, P99 of review response times.
//!
//! # Complexity
//!
//! - Accumulation: O(1) per file change
//! - Finalization: O(F × log F) for sorting

use rustc_hash::FxHashMap;

/// Per-file review response statistics.
#[derive(Debug, Clone)]
pub struct FileReviewResponse {
    /// File path.
    pub path: String,
    /// Median response time in hours.
    pub p50_hours: f64,
    /// 90th percentile response time in hours.
    pub p90_hours: f64,
    /// Number of review events detected.
    pub review_count: u32,
    /// Number of unique reviewers (distinct subsequent authors).
    pub reviewer_count: u32,
}

/// Complete review response time report.
#[derive(Debug, Clone)]
pub struct ReviewResponseReport {
    /// Per-file response times (sorted by P50 descending = slowest first).
    pub files: Vec<FileReviewResponse>,
    /// Team-wide median response time in hours.
    pub team_p50_hours: f64,
    /// Team-wide P90 response time in hours.
    pub team_p90_hours: f64,
    /// Files with consistently slow reviews (P50 > 72 hours).
    pub slow_review_count: usize,
    /// Total review events analyzed.
    pub total_reviews: usize,
}

/// Per-file tracking state during accumulation.
struct FileTracker {
    /// Last author and timestamp for this file.
    last_author: String,
    last_timestamp: i64,
    /// Response time deltas in seconds.
    response_times: Vec<i64>,
    /// Unique reviewers (different-from-previous authors).
    reviewers: rustc_hash::FxHashSet<String>,
}

/// Accumulates review response time data from commit stream.
pub struct ReviewResponseAccumulator {
    files: FxHashMap<String, FileTracker>,
}

impl Default for ReviewResponseAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl ReviewResponseAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            files: FxHashMap::default(),
        }
    }

    /// Records a file change within a commit.
    pub fn record_file(&mut self, path: &str, author: &str, timestamp: i64) {
        let tracker = self
            .files
            .entry(path.to_string())
            .or_insert_with(|| FileTracker {
                last_author: author.to_string(),
                last_timestamp: timestamp,
                response_times: Vec::new(),
                reviewers: rustc_hash::FxHashSet::default(),
            });

        if tracker.last_author != author {
            let delta = (timestamp - tracker.last_timestamp).max(0);
            tracker.response_times.push(delta);
            tracker.reviewers.insert(author.to_string());
        }

        tracker.last_author = author.to_string();
        tracker.last_timestamp = timestamp;
    }

    /// Finalizes the review response time report.
    #[must_use]
    pub fn finalize(self) -> ReviewResponseReport {
        let mut all_times: Vec<f64> = Vec::new();
        let mut files: Vec<FileReviewResponse> = self
            .files
            .into_iter()
            .filter_map(|(path, tracker)| {
                if tracker.response_times.is_empty() {
                    return None;
                }

                let mut times: Vec<f64> = tracker
                    .response_times
                    .iter()
                    .map(|&t| t as f64 / 3600.0) // Convert to hours
                    .collect();
                times.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

                let p50 = percentile(&times, 50.0);
                let p90 = percentile(&times, 90.0);

                all_times.extend_from_slice(&times);

                Some(FileReviewResponse {
                    path,
                    p50_hours: p50,
                    p90_hours: p90,
                    review_count: times.len() as u32,
                    reviewer_count: tracker.reviewers.len() as u32,
                })
            })
            .collect();

        files.sort_by(|a, b| {
            b.p50_hours
                .partial_cmp(&a.p50_hours)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        files.truncate(50);

        all_times.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

        let team_p50 = percentile(&all_times, 50.0);
        let team_p90 = percentile(&all_times, 90.0);
        let slow_count = files.iter().filter(|f| f.p50_hours > 72.0).count();

        ReviewResponseReport {
            total_reviews: all_times.len(),
            files,
            team_p50_hours: team_p50,
            team_p90_hours: team_p90,
            slow_review_count: slow_count,
        }
    }
}

/// Computes the p-th percentile of a sorted slice.
fn percentile(sorted: &[f64], p: f64) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let idx = (p / 100.0 * (sorted.len() as f64 - 1.0)).round() as usize;
    sorted[idx.min(sorted.len() - 1)]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let acc = ReviewResponseAccumulator::new();
        let report = acc.finalize();
        assert!(report.files.is_empty());
        assert_eq!(report.total_reviews, 0);
    }

    #[test]
    fn test_single_author_no_reviews() {
        let mut acc = ReviewResponseAccumulator::new();
        acc.record_file("a.rs", "Alice", 100);
        acc.record_file("a.rs", "Alice", 200);
        let report = acc.finalize();
        assert!(report.files.is_empty());
    }

    #[test]
    fn test_two_authors_one_review() {
        let mut acc = ReviewResponseAccumulator::new();
        acc.record_file("a.rs", "Alice", 0);
        acc.record_file("a.rs", "Bob", 7200); // 2 hours later
        let report = acc.finalize();
        assert_eq!(report.files.len(), 1);
        assert!((report.files[0].p50_hours - 2.0).abs() < 1e-10);
        assert_eq!(report.files[0].review_count, 1);
    }

    #[test]
    fn test_percentile_calculation() {
        let sorted = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        assert!((percentile(&sorted, 50.0) - 3.0).abs() < 1e-10);
        assert!((percentile(&sorted, 0.0) - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_default_impl() {
        let acc = ReviewResponseAccumulator::default();
        let report = acc.finalize();
        assert!(report.files.is_empty());
    }
}
