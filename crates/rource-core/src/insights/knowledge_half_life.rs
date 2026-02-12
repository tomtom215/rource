// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Knowledge Half-Life analysis.
//!
//! Models how quickly a developer's knowledge of a file becomes stale, with
//! decay rate calibrated to each file's change velocity.
//!
//! # Research Basis
//!
//! - Mockus & Votta (ICSM 2000, DOI: 10.1109/ICSM.2000.883028) — experience model
//! - Fritz et al. (ICSE 2010, DOI: 10.1145/1806799.1806856) — degree-of-knowledge
//! - Robillard et al. (IEEE Software 2014, DOI: 10.1109/MS.2014.96) — developer memory of code
//! - Ebbinghaus (1885) — forgetting curve applied to code knowledge
//!
//! # Novelty
//!
//! Per-file adaptive decay rate calibrated to change velocity is genuinely new.
//! Existing knowledge models use fixed decay or no decay at all. This model
//! captures the intuition that expertise in fast-changing code decays faster
//! than expertise in stable code, with the decay rate empirically derived from
//! the file's own history.
//!
//! # Algorithm
//!
//! Knowledge of developer d for file f at time t:
//!   K(d, f, t) = Σᵢ e^(-λ_f × (t - tᵢ))
//!
//! where:
//!   `tᵢ` = timestamp of d's i-th commit to f
//!   `λ_f = ln(2) / h_f` (decay constant)
//!   `h_f = median_interval(f) × α` (half-life, α = 2.0 default)
//!
//! # Complexity
//!
//! - Accumulation: O(C) where C = total (developer, file) commit events
//! - Finalization: O(D × F) where D = developers, F = files per developer

use rustc_hash::FxHashMap;

/// Tuning parameter: knowledge halves every `α` median-change-intervals.
const ALPHA: f64 = 2.0;

/// Below this threshold, a file is on the "knowledge cliff."
const CLIFF_THRESHOLD: f64 = 0.1;

/// Fallback half-life in seconds when a file has only one change.
/// Set to 90 days — a reasonable default for stable code.
const FALLBACK_HALF_LIFE_SECS: f64 = 90.0 * 86400.0;

/// Per-file knowledge metrics.
#[derive(Debug, Clone)]
pub struct FileKnowledgeHealth {
    /// File path.
    pub path: String,
    /// Maximum current knowledge K across all developers (freshness).
    pub knowledge_freshness: f64,
    /// Developer with the highest current K.
    pub top_expert: String,
    /// Half-life in days for this file.
    pub half_life_days: f64,
    /// Whether this file is on the "knowledge cliff" (no live expert).
    pub is_knowledge_cliff: bool,
    /// Top-K developers with their current knowledge scores.
    pub experts: Vec<(String, f64)>,
}

/// Per-developer knowledge portfolio.
#[derive(Debug, Clone)]
pub struct DeveloperKnowledgePortfolio {
    /// Developer name.
    pub author: String,
    /// Total current knowledge mass: `Σ_f K(d, f, now)`.
    pub knowledge_mass: f64,
    /// Number of files where this developer is on the knowledge cliff.
    pub cliff_file_count: u32,
    /// Number of files where this developer is the top expert.
    pub top_expert_count: u32,
}

/// Aggregate knowledge half-life report.
#[derive(Debug, Clone)]
pub struct KnowledgeHalfLifeReport {
    /// Per-file knowledge health, sorted by freshness ascending (most stale first).
    pub files: Vec<FileKnowledgeHealth>,
    /// Team Knowledge Freshness: fraction of files with a live expert.
    pub team_knowledge_freshness: f64,
    /// Files on the knowledge cliff (no developer with K > threshold).
    pub cliff_count: u32,
    /// Per-developer knowledge portfolio.
    pub developers: Vec<DeveloperKnowledgePortfolio>,
    /// Distribution stats for half-lives (in days).
    pub median_half_life_days: f64,
    /// Shortest half-life observed (fastest-changing code).
    pub min_half_life_days: f64,
    /// Longest half-life observed (most stable code).
    pub max_half_life_days: f64,
}

/// Accumulates per-(developer, file) commit timestamps.
pub struct KnowledgeHalfLifeAccumulator {
    /// (developer, file) → list of commit timestamps.
    commit_times: FxHashMap<(String, String), Vec<i64>>,
    /// file → list of all change timestamps (for median interval computation).
    file_change_times: FxHashMap<String, Vec<i64>>,
}

impl Default for KnowledgeHalfLifeAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl KnowledgeHalfLifeAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            commit_times: FxHashMap::default(),
            file_change_times: FxHashMap::default(),
        }
    }

    /// Records a developer's contribution to a file.
    pub fn record_file(&mut self, author: &str, path: &str, timestamp: i64) {
        self.commit_times
            .entry((author.to_string(), path.to_string()))
            .or_default()
            .push(timestamp);
        self.file_change_times
            .entry(path.to_string())
            .or_default()
            .push(timestamp);
    }

    /// Finalizes the accumulator into a report.
    ///
    /// # Arguments
    ///
    /// * `t_now` - The "current" timestamp (typically `t_max` of the commit range)
    #[must_use]
    pub fn finalize(self, t_now: i64) -> KnowledgeHalfLifeReport {
        if self.file_change_times.is_empty() {
            return KnowledgeHalfLifeReport {
                files: Vec::new(),
                team_knowledge_freshness: 0.0,
                cliff_count: 0,
                developers: Vec::new(),
                median_half_life_days: 0.0,
                min_half_life_days: 0.0,
                max_half_life_days: 0.0,
            };
        }

        // Step 1: Compute per-file median interval and half-life.
        let project_median = compute_project_median_interval(&self.file_change_times);
        let mut file_half_lives: FxHashMap<&str, f64> = FxHashMap::default();
        for (path, times) in &self.file_change_times {
            let half_life = compute_half_life(times, project_median);
            file_half_lives.insert(path.as_str(), half_life);
        }

        // Step 2: Compute K(d, f, t_now) for each (developer, file) pair.
        let (file_experts, dev_mass) =
            compute_knowledge_scores(&self.commit_times, &file_half_lives, t_now);

        // Steps 3-4: Build per-file and per-developer reports.
        build_knowledge_report(
            &self.file_change_times,
            &file_half_lives,
            &file_experts,
            dev_mass,
        )
    }
}

/// Result of knowledge score computation: (file experts, developer mass totals).
type KnowledgeScores<'a> = (
    FxHashMap<&'a str, Vec<(&'a str, f64)>>,
    FxHashMap<&'a str, f64>,
);

/// Computes `K(d, f, t_now)` for each (developer, file) pair using exponential decay.
///
/// Returns per-file expert lists and per-developer knowledge mass totals.
fn compute_knowledge_scores<'a>(
    commit_times: &'a FxHashMap<(String, String), Vec<i64>>,
    file_half_lives: &FxHashMap<&str, f64>,
    t_now: i64,
) -> KnowledgeScores<'a> {
    let now = t_now as f64;
    let mut file_experts: FxHashMap<&str, Vec<(&str, f64)>> = FxHashMap::default();
    let mut dev_mass: FxHashMap<&str, f64> = FxHashMap::default();

    for ((author, path), timestamps) in commit_times {
        let half_life = file_half_lives
            .get(path.as_str())
            .copied()
            .unwrap_or(FALLBACK_HALF_LIFE_SECS);
        let lambda = (2.0_f64).ln() / half_life;

        let k: f64 = timestamps
            .iter()
            .map(|&t| {
                let dt = (now - t as f64).max(0.0);
                (-lambda * dt).exp()
            })
            .sum();

        file_experts
            .entry(path.as_str())
            .or_default()
            .push((author.as_str(), k));
        *dev_mass.entry(author.as_str()).or_insert(0.0) += k;
    }

    (file_experts, dev_mass)
}

/// Builds the final report from pre-computed knowledge scores.
fn build_knowledge_report(
    file_change_times: &FxHashMap<String, Vec<i64>>,
    file_half_lives: &FxHashMap<&str, f64>,
    file_experts: &FxHashMap<&str, Vec<(&str, f64)>>,
    dev_mass: FxHashMap<&str, f64>,
) -> KnowledgeHalfLifeReport {
    let mut files: Vec<FileKnowledgeHealth> = file_change_times
        .keys()
        .map(|path| {
            let half_life_secs = file_half_lives
                .get(path.as_str())
                .copied()
                .unwrap_or(FALLBACK_HALF_LIFE_SECS);
            let half_life_days = half_life_secs / 86400.0;

            let mut experts = file_experts.get(path.as_str()).cloned().unwrap_or_default();
            experts.sort_unstable_by(|a, b| {
                b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal)
            });

            let (top_expert, knowledge_freshness) = match experts.first() {
                Some((name, k)) => (name.to_string(), *k),
                None => (String::new(), 0.0),
            };

            let is_knowledge_cliff = knowledge_freshness < CLIFF_THRESHOLD;
            let expert_list: Vec<(String, f64)> = experts
                .iter()
                .take(5)
                .map(|(name, k)| (name.to_string(), *k))
                .collect();

            FileKnowledgeHealth {
                path: path.clone(),
                knowledge_freshness,
                top_expert,
                half_life_days,
                is_knowledge_cliff,
                experts: expert_list,
            }
        })
        .collect();

    files.sort_unstable_by(|a, b| {
        a.knowledge_freshness
            .partial_cmp(&b.knowledge_freshness)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let cliff_count = files.iter().filter(|f| f.is_knowledge_cliff).count() as u32;
    let team_knowledge_freshness = if files.is_empty() {
        0.0
    } else {
        let live_expert_count = files.iter().filter(|f| !f.is_knowledge_cliff).count();
        live_expert_count as f64 / files.len() as f64
    };

    let mut hl_days: Vec<f64> = files.iter().map(|f| f.half_life_days).collect();
    hl_days.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let median_half_life_days = median_sorted(&hl_days);
    let min_half_life_days = hl_days.first().copied().unwrap_or(0.0);
    let max_half_life_days = hl_days.last().copied().unwrap_or(0.0);

    let mut developers: Vec<DeveloperKnowledgePortfolio> = dev_mass
        .into_iter()
        .map(|(author, mass)| {
            let cliff_file_count = file_experts
                .values()
                .filter(|experts| {
                    experts
                        .iter()
                        .any(|(a, k)| *a == author && *k < CLIFF_THRESHOLD)
                })
                .count() as u32;
            let top_expert_count = files.iter().filter(|f| f.top_expert == author).count() as u32;
            DeveloperKnowledgePortfolio {
                author: author.to_string(),
                knowledge_mass: mass,
                cliff_file_count,
                top_expert_count,
            }
        })
        .collect();
    developers.sort_unstable_by(|a, b| {
        b.knowledge_mass
            .partial_cmp(&a.knowledge_mass)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    KnowledgeHalfLifeReport {
        files,
        team_knowledge_freshness,
        cliff_count,
        developers,
        median_half_life_days,
        min_half_life_days,
        max_half_life_days,
    }
}

/// Computes the half-life for a file based on its change timestamps.
fn compute_half_life(timestamps: &[i64], project_median: f64) -> f64 {
    if timestamps.len() < 2 {
        return project_median * ALPHA;
    }

    let mut sorted = timestamps.to_vec();
    sorted.sort_unstable();

    let intervals: Vec<f64> = sorted
        .windows(2)
        .map(|w| (w[1] - w[0]) as f64)
        .filter(|&d| d > 0.0)
        .collect();

    if intervals.is_empty() {
        return project_median * ALPHA;
    }

    let mut sorted_intervals = intervals;
    sorted_intervals.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let median = median_sorted(&sorted_intervals);

    if median <= 0.0 {
        project_median * ALPHA
    } else {
        median * ALPHA
    }
}

/// Computes the project-wide median inter-change interval.
fn compute_project_median_interval(file_change_times: &FxHashMap<String, Vec<i64>>) -> f64 {
    let mut all_intervals: Vec<f64> = Vec::new();

    for times in file_change_times.values() {
        if times.len() < 2 {
            continue;
        }
        let mut sorted = times.clone();
        sorted.sort_unstable();
        for w in sorted.windows(2) {
            let d = (w[1] - w[0]) as f64;
            if d > 0.0 {
                all_intervals.push(d);
            }
        }
    }

    if all_intervals.is_empty() {
        return FALLBACK_HALF_LIFE_SECS / ALPHA;
    }

    all_intervals.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    median_sorted(&all_intervals)
}

/// Computes the median of a pre-sorted slice.
fn median_sorted(sorted: &[f64]) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let mid = sorted.len() / 2;
    if sorted.len() % 2 == 0 {
        (sorted[mid - 1] + sorted[mid]) / 2.0
    } else {
        sorted[mid]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = KnowledgeHalfLifeAccumulator::new();
        let report = acc.finalize(10000);
        assert!(report.files.is_empty());
        assert_eq!(report.team_knowledge_freshness, 0.0);
    }

    #[test]
    fn test_single_developer_single_file() {
        let mut acc = KnowledgeHalfLifeAccumulator::new();
        acc.record_file("Alice", "a.rs", 1000);
        let report = acc.finalize(1000);

        assert_eq!(report.files.len(), 1);
        // At t=t_commit, K should be ~1.0 (no decay)
        assert!(report.files[0].knowledge_freshness > 0.9);
        assert_eq!(report.files[0].top_expert, "Alice");
    }

    #[test]
    fn test_knowledge_decays_over_time() {
        let mut acc = KnowledgeHalfLifeAccumulator::new();
        acc.record_file("Alice", "a.rs", 0);
        acc.record_file("Alice", "a.rs", 1000);

        // Evaluate at a much later time
        let report = acc.finalize(1_000_000);

        // Knowledge should have decayed significantly
        assert!(report.files[0].knowledge_freshness < 1.0);
    }

    #[test]
    fn test_recent_contributor_higher_knowledge() {
        let mut acc = KnowledgeHalfLifeAccumulator::new();
        // Alice contributed long ago (early in project history)
        acc.record_file("Alice", "a.rs", 0);
        acc.record_file("Alice", "a.rs", 100);
        // Bob contributed much more recently with a strong contribution
        acc.record_file("Bob", "a.rs", 990_000);
        acc.record_file("Bob", "a.rs", 999_000);

        // Evaluate well after Alice's contributions but near Bob's
        let report = acc.finalize(1_000_000);

        let file = &report.files[0];
        assert_eq!(
            file.top_expert, "Bob",
            "Recent contributor should be top expert"
        );
    }

    #[test]
    fn test_fast_changing_file_faster_decay() {
        let mut acc = KnowledgeHalfLifeAccumulator::new();

        // Fast-changing file: changes every 100 seconds
        for i in 0..10 {
            acc.record_file("Alice", "fast.rs", i * 100);
        }
        // Slow-changing file: changes every 10000 seconds
        for i in 0..10 {
            acc.record_file("Alice", "slow.rs", i * 10000);
        }

        let report = acc.finalize(100_000);

        let fast = report.files.iter().find(|f| f.path == "fast.rs").unwrap();
        let slow = report.files.iter().find(|f| f.path == "slow.rs").unwrap();

        // Fast-changing file should have shorter half-life
        assert!(
            fast.half_life_days < slow.half_life_days,
            "fast.half_life_days ({}) should be < slow.half_life_days ({})",
            fast.half_life_days,
            slow.half_life_days
        );
    }

    #[test]
    fn test_knowledge_cliff_detection() {
        let mut acc = KnowledgeHalfLifeAccumulator::new();
        // File changed very long ago
        acc.record_file("Alice", "old.rs", 0);
        acc.record_file("Alice", "old.rs", 100);

        // Evaluate way in the future
        let report = acc.finalize(100_000_000);

        let file = report.files.iter().find(|f| f.path == "old.rs").unwrap();
        assert!(
            file.is_knowledge_cliff,
            "Old file should be on knowledge cliff"
        );
        assert!(report.cliff_count > 0);
    }

    #[test]
    fn test_team_knowledge_freshness_bounds() {
        let mut acc = KnowledgeHalfLifeAccumulator::new();
        acc.record_file("Alice", "a.rs", 1000);
        let report = acc.finalize(1000);

        assert!(report.team_knowledge_freshness >= 0.0);
        assert!(report.team_knowledge_freshness <= 1.0);
    }

    #[test]
    fn test_developer_portfolio() {
        let mut acc = KnowledgeHalfLifeAccumulator::new();
        acc.record_file("Alice", "a.rs", 1000);
        acc.record_file("Alice", "b.rs", 1000);
        acc.record_file("Bob", "c.rs", 1000);

        let report = acc.finalize(1000);

        assert_eq!(report.developers.len(), 2);
        let alice = report
            .developers
            .iter()
            .find(|d| d.author == "Alice")
            .unwrap();
        assert!(alice.knowledge_mass > 0.0);
        assert_eq!(alice.top_expert_count, 2);
    }

    #[test]
    fn test_half_life_distribution() {
        let mut acc = KnowledgeHalfLifeAccumulator::new();
        for i in 0..5 {
            acc.record_file("Alice", "a.rs", i * 1000);
            acc.record_file("Bob", "b.rs", i * 5000);
        }

        let report = acc.finalize(50000);

        assert!(report.min_half_life_days > 0.0);
        assert!(report.max_half_life_days >= report.min_half_life_days);
        assert!(report.median_half_life_days >= report.min_half_life_days);
        assert!(report.median_half_life_days <= report.max_half_life_days);
    }

    #[test]
    fn test_compute_half_life_single_timestamp() {
        // Single timestamp falls back to project median × α
        let hl = compute_half_life(&[1000], 86400.0);
        assert!((hl - 86400.0 * ALPHA).abs() < 0.01);
    }

    #[test]
    fn test_median_sorted() {
        assert_eq!(median_sorted(&[]), 0.0);
        assert_eq!(median_sorted(&[5.0]), 5.0);
        assert_eq!(median_sorted(&[1.0, 3.0]), 2.0);
        assert_eq!(median_sorted(&[1.0, 2.0, 3.0]), 2.0);
    }
}
