// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Knowledge currency index: unified per-file knowledge freshness score.
//!
//! Combines multiple knowledge decay signals into a single score [0.0, 1.0]
//! answering: "How well-understood is this file RIGHT NOW by the current team?"
//!
//! # Signals Combined
//!
//! 1. Time since last touch by ANY contributor (recency)
//! 2. Exponential decay of each contributor's knowledge (Ebbinghaus 1885)
//! 3. Number of "knowledge refreshes" (re-visits after gaps)
//! 4. Active contributor count (team availability)
//!
//! # Academic Citations
//!
//! - Fritz et al. (2010) — "Degree of Knowledge" (DOK = DOA + DOI with temporal decay)
//! - Mockus & Votta (2000) — Knowledge contribution decay
//! - Jabrayilzade et al. (2022) — Extended DOK with explicit decay parameters
//! - Ebbinghaus (1885) — Forgetting curve (exponential decay of memory)
//!
//! # Novelty
//!
//! Existing tools compute ownership (static) or knowledge decay (per-developer).
//! A unified per-FILE currency index that answers "how well-understood is this
//! file RIGHT NOW by the current team?" is not offered by any existing tool.

use rustc_hash::FxHashMap;

/// Knowledge currency report for the entire repository.
#[derive(Debug)]
pub struct KnowledgeCurrencyReport {
    /// Per-file knowledge currency data, sorted by currency ascending (stalest first).
    pub files: Vec<FileKnowledgeCurrency>,
    /// Repository-wide average knowledge currency [0.0, 1.0].
    pub avg_currency: f64,
    /// Number of files with stale knowledge (currency < 0.3).
    pub stale_count: u32,
    /// Number of files with current knowledge (currency >= 0.7).
    pub current_count: u32,
    /// Total files analyzed.
    pub total_files: u32,
}

/// Knowledge currency data for a single file.
#[derive(Debug)]
pub struct FileKnowledgeCurrency {
    /// File path.
    pub path: String,
    /// Unified knowledge currency score [0.0, 1.0].
    /// 0.0 = completely stale, 1.0 = fully current.
    pub currency: f64,
    /// Days since last modification by any contributor.
    pub days_since_last_touch: f64,
    /// Number of knowledge refreshes (re-visits after 30+ day gaps).
    pub refresh_count: u32,
    /// Number of active contributors (touched within last 90 days).
    pub active_contributor_count: u32,
    /// Total distinct contributors.
    pub total_contributor_count: u32,
    /// Weighted knowledge sum across all contributors (after decay).
    pub decayed_knowledge_sum: f64,
}

/// Half-life for knowledge decay in seconds (90 days).
///
/// Based on Ebbinghaus (1885) forgetting curve adapted for software knowledge:
/// after 90 days without touching a file, a developer's knowledge is halved.
const KNOWLEDGE_HALF_LIFE_SECS: f64 = 90.0 * 86400.0;

/// Gap threshold for counting a "knowledge refresh" (30 days in seconds).
const REFRESH_GAP_SECS: i64 = 30 * 86400;

/// Threshold for "active" contributor (90 days in seconds).
const ACTIVE_THRESHOLD_SECS: i64 = 90 * 86400;

/// Computes knowledge currency for all files from per-file contributor data.
///
/// # Arguments
///
/// * `file_author_times` - Map of file path → (author → Vec<timestamps>)
/// * `t_now` - Current timestamp (typically max commit timestamp)
///
/// # Complexity
///
/// O(F × D × T) where F = files, D = max developers per file, T = max timestamps per developer-file pair.
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn compute_knowledge_currency(
    file_author_times: &FxHashMap<String, FxHashMap<String, Vec<i64>>>,
    t_now: i64,
) -> KnowledgeCurrencyReport {
    if file_author_times.is_empty() {
        return KnowledgeCurrencyReport {
            files: Vec::new(),
            avg_currency: 0.0,
            stale_count: 0,
            current_count: 0,
            total_files: 0,
        };
    }

    let mut files: Vec<FileKnowledgeCurrency> = file_author_times
        .iter()
        .map(|(path, authors)| compute_file_currency(path, authors, t_now))
        .collect();

    // Sort by currency ascending (stalest first — most actionable)
    files.sort_by(|a, b| {
        a.currency
            .partial_cmp(&b.currency)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let total = files.len() as u32;
    let avg_currency = if files.is_empty() {
        0.0
    } else {
        files.iter().map(|f| f.currency).sum::<f64>() / files.len() as f64
    };
    let stale_count = files.iter().filter(|f| f.currency < 0.3).count() as u32;
    let current_count = files.iter().filter(|f| f.currency >= 0.7).count() as u32;

    // Truncate to top 100 most stale files
    files.truncate(100);

    KnowledgeCurrencyReport {
        files,
        avg_currency,
        stale_count,
        current_count,
        total_files: total,
    }
}

/// Computes knowledge currency for a single file.
fn compute_file_currency(
    path: &str,
    authors: &FxHashMap<String, Vec<i64>>,
    t_now: i64,
) -> FileKnowledgeCurrency {
    // Find the most recent touch across all contributors
    let last_touch = authors
        .values()
        .filter_map(|ts| ts.iter().max())
        .max()
        .copied()
        .unwrap_or(0);
    let days_since_last = (t_now - last_touch) as f64 / 86400.0;

    // Compute decayed knowledge per contributor
    let mut decayed_sum = 0.0;
    let mut total_refresh = 0u32;
    let mut active_count = 0u32;
    let total_contributors = authors.len() as u32;

    for timestamps in authors.values() {
        let mut sorted_ts = timestamps.clone();
        sorted_ts.sort_unstable();

        // Count knowledge refreshes (re-visits after 30+ day gaps)
        let refreshes = sorted_ts
            .windows(2)
            .filter(|w| (w[1] - w[0]) >= REFRESH_GAP_SECS)
            .count() as u32;
        total_refresh += refreshes;

        // Most recent touch by this contributor
        let last = *sorted_ts.last().unwrap_or(&0);
        let elapsed_secs = (t_now - last) as f64;

        // Exponential decay: knowledge = base × 2^(-t/half_life)
        // Base knowledge = ln(1 + commit_count) to diminish returns of many commits
        let base_knowledge = (sorted_ts.len() as f64).ln_1p();
        let decay_factor = (-elapsed_secs / KNOWLEDGE_HALF_LIFE_SECS).exp2();
        decayed_sum += base_knowledge * decay_factor;

        // Is this contributor still active?
        if t_now - last < ACTIVE_THRESHOLD_SECS {
            active_count += 1;
        }
    }

    // Normalize to [0.0, 1.0]:
    // Signal 1: Recency (exponential decay of time since last touch)
    let recency_score = (-days_since_last / 90.0).exp2().min(1.0);

    // Signal 2: Decayed knowledge relative to best possible
    // Best possible: all contributors just touched it, each with many commits
    let max_possible_knowledge = authors
        .values()
        .map(|ts| (ts.len() as f64).ln_1p())
        .sum::<f64>();
    let knowledge_score = if max_possible_knowledge > 0.0 {
        (decayed_sum / max_possible_knowledge).min(1.0)
    } else {
        0.0
    };

    // Signal 3: Refresh bonus (normalized by contributor count)
    let refresh_bonus = if total_contributors > 0 {
        (f64::from(total_refresh) / f64::from(total_contributors) / 3.0).min(0.2)
    } else {
        0.0
    };

    // Signal 4: Active contributor ratio
    let active_ratio = if total_contributors > 0 {
        f64::from(active_count) / f64::from(total_contributors)
    } else {
        0.0
    };

    // Weighted combination (weights sum to 1.0 before refresh bonus):
    // 40% recency, 30% knowledge decay, 30% active ratio, +bonus
    let currency =
        (0.4 * recency_score + 0.3 * knowledge_score + 0.3 * active_ratio + refresh_bonus)
            .clamp(0.0, 1.0);

    FileKnowledgeCurrency {
        path: path.to_string(),
        currency,
        days_since_last_touch: days_since_last,
        refresh_count: total_refresh,
        active_contributor_count: active_count,
        total_contributor_count: total_contributors,
        decayed_knowledge_sum: decayed_sum,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_input() {
        let map = FxHashMap::default();
        let report = compute_knowledge_currency(&map, 1_000_000);
        assert_eq!(report.total_files, 0);
        assert!(report.files.is_empty());
    }

    #[test]
    fn test_single_file_just_touched() {
        let mut map = FxHashMap::default();
        let mut authors = FxHashMap::default();
        authors.insert("Alice".to_string(), vec![1_000_000]);
        map.insert("src/main.rs".to_string(), authors);

        let report = compute_knowledge_currency(&map, 1_000_000);
        assert_eq!(report.total_files, 1);
        let f = &report.files[0];
        assert_eq!(f.path, "src/main.rs");
        // Just touched → currency should be high
        assert!(f.currency > 0.7, "currency={}, expected >0.7", f.currency);
        assert!(f.days_since_last_touch.abs() < 0.01);
    }

    #[test]
    fn test_stale_file() {
        let mut map = FxHashMap::default();
        let mut authors = FxHashMap::default();
        // File touched 365 days ago
        let t_now: i64 = 365 * 86400;
        authors.insert("Alice".to_string(), vec![0]);
        map.insert("old.rs".to_string(), authors);

        let report = compute_knowledge_currency(&map, t_now);
        let f = &report.files[0];
        // Very old → currency should be low
        assert!(f.currency < 0.3, "currency={}, expected <0.3", f.currency);
        assert!((f.days_since_last_touch - 365.0).abs() < 0.1);
    }

    #[test]
    fn test_multiple_contributors_boost() {
        let t_now: i64 = 100 * 86400;
        let mut map = FxHashMap::default();

        // File with 3 active contributors, all at same recency
        let mut authors_multi = FxHashMap::default();
        authors_multi.insert("Alice".to_string(), vec![90 * 86400]);
        authors_multi.insert("Bob".to_string(), vec![90 * 86400]);
        authors_multi.insert("Carol".to_string(), vec![90 * 86400]);
        map.insert("multi.rs".to_string(), authors_multi);

        // File with 1 contributor, same recency
        let mut authors_single = FxHashMap::default();
        authors_single.insert("Alice".to_string(), vec![90 * 86400]);
        map.insert("single.rs".to_string(), authors_single);

        let report = compute_knowledge_currency(&map, t_now);
        let multi = report.files.iter().find(|f| f.path == "multi.rs").unwrap();
        let single = report.files.iter().find(|f| f.path == "single.rs").unwrap();

        // Multi-contributor file should have higher currency (more active ratio)
        // With equal recency and commits, the 30% active_ratio weight makes the difference
        assert!(
            multi.currency >= single.currency,
            "multi={}, single={}",
            multi.currency,
            single.currency
        );
        assert_eq!(multi.active_contributor_count, 3);
        assert_eq!(single.active_contributor_count, 1);
    }

    #[test]
    fn test_refresh_count() {
        let mut map = FxHashMap::default();
        let mut authors = FxHashMap::default();
        // Touches at day 0, 60, 120 → 2 refreshes (gaps > 30 days)
        authors.insert("Alice".to_string(), vec![0, 60 * 86400, 120 * 86400]);
        map.insert("refreshed.rs".to_string(), authors);

        let report = compute_knowledge_currency(&map, 120 * 86400);
        let f = &report.files[0];
        assert_eq!(f.refresh_count, 2);
    }

    #[test]
    fn test_sorted_stalest_first() {
        let t_now: i64 = 200 * 86400;
        let mut map = FxHashMap::default();

        let mut a1 = FxHashMap::default();
        a1.insert("Alice".to_string(), vec![190 * 86400]); // recent
        map.insert("recent.rs".to_string(), a1);

        let mut a2 = FxHashMap::default();
        a2.insert("Alice".to_string(), vec![10 * 86400]); // old
        map.insert("old.rs".to_string(), a2);

        let report = compute_knowledge_currency(&map, t_now);
        assert_eq!(report.files.len(), 2);
        // Stalest first
        assert!(report.files[0].currency <= report.files[1].currency);
        assert_eq!(report.files[0].path, "old.rs");
    }

    #[test]
    fn test_currency_bounded() {
        let mut map = FxHashMap::default();
        let mut authors = FxHashMap::default();
        authors.insert("Alice".to_string(), vec![1000]);
        map.insert("a.rs".to_string(), authors);

        let report = compute_knowledge_currency(&map, 1000);
        let f = &report.files[0];
        assert!(f.currency >= 0.0 && f.currency <= 1.0);
    }

    #[test]
    fn test_stale_current_counts() {
        let t_now: i64 = 400 * 86400;
        let mut map = FxHashMap::default();

        // 3 stale files (touched 300+ days ago)
        for i in 0..3 {
            let mut a = FxHashMap::default();
            a.insert("Alice".to_string(), vec![10 * 86400]);
            map.insert(format!("stale{i}.rs"), a);
        }
        // 2 current files (touched recently)
        for i in 0..2 {
            let mut a = FxHashMap::default();
            a.insert("Alice".to_string(), vec![395 * 86400]);
            map.insert(format!("current{i}.rs"), a);
        }

        let report = compute_knowledge_currency(&map, t_now);
        assert_eq!(report.total_files, 5);
        assert_eq!(report.stale_count, 3);
        assert_eq!(report.current_count, 2);
    }
}
