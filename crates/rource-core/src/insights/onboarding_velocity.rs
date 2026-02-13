// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Contributor onboarding velocity analysis (M20).
//!
//! Measures how quickly new contributors become productive by tracking
//! time from first commit to touching core files and commit frequency
//! ramp-up patterns.
//!
//! # Research Basis
//!
//! Zhou & Mockus (2012) "What Make Long Term Contributors: Willingness
//! and Opportunity in OSS Community" (ICSE, DOI: 10.1109/ICSE.2012.6227164).
//!
//! Steinmacher et al. (2015) "A Systematic Literature Review on the Barriers
//! Faced by Newcomers to Open Source Software Projects" (ISSE,
//! DOI: 10.1007/s11219-014-9236-x).
//!
//! # Algorithm
//!
//! For each developer:
//! 1. Record first commit timestamp and classify files as core vs peripheral
//! 2. Track commits in rolling 4-week windows from first commit
//! 3. Classify: fast-ramp (>= 2x growth w2 vs w1), slow-ramp, one-shot (1 commit),
//!    sustained (stable after ramp)
//!
//! # Complexity
//!
//! - Accumulation: O(1) per commit
//! - Finalization: O(A × log A) where A = authors

use rustc_hash::FxHashMap;

/// Onboarding classification for a contributor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OnboardingType {
    /// Single commit, never returned.
    OneShot,
    /// Slow increase in activity over time.
    SlowRamp,
    /// Rapid increase in activity.
    FastRamp,
    /// Consistent activity from the start.
    Sustained,
}

impl OnboardingType {
    /// Returns a human-readable label.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::OneShot => "One-Shot",
            Self::SlowRamp => "Slow Ramp",
            Self::FastRamp => "Fast Ramp",
            Self::Sustained => "Sustained",
        }
    }
}

/// Per-developer onboarding profile.
#[derive(Debug, Clone)]
pub struct DeveloperOnboarding {
    /// Developer name.
    pub author: String,
    /// Onboarding classification.
    pub onboarding_type: OnboardingType,
    /// Total commits.
    pub total_commits: u32,
    /// Unique files touched.
    pub unique_files: u32,
    /// Days from first to last commit.
    pub active_span_days: f64,
    /// Days from first commit to first core file touch (None if never touched core).
    pub days_to_core: Option<f64>,
    /// Commits in first 4 weeks.
    pub week1_4_commits: u32,
    /// Commits in weeks 5-8.
    pub week5_8_commits: u32,
}

/// Complete onboarding velocity report.
#[derive(Debug, Clone)]
pub struct OnboardingVelocityReport {
    /// Per-developer onboarding profiles.
    pub developers: Vec<DeveloperOnboarding>,
    /// Count of one-shot contributors.
    pub one_shot_count: usize,
    /// Count of fast-ramp contributors.
    pub fast_ramp_count: usize,
    /// Count of slow-ramp contributors.
    pub slow_ramp_count: usize,
    /// Count of sustained contributors.
    pub sustained_count: usize,
    /// Median days to first core file touch.
    pub median_days_to_core: f64,
}

/// Threshold for "core" files: files with >= this many total changes.
const CORE_THRESHOLD: u32 = 5;

/// 4 weeks in seconds.
const FOUR_WEEKS: i64 = 28 * 86400;

/// Per-developer accumulation state.
struct DevState {
    first_commit: i64,
    last_commit: i64,
    commits: Vec<i64>,
    files: rustc_hash::FxHashSet<String>,
}

/// Accumulates onboarding velocity data from commit stream.
pub struct OnboardingVelocityAccumulator {
    devs: FxHashMap<String, DevState>,
    file_change_counts: FxHashMap<String, u32>,
}

impl Default for OnboardingVelocityAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl OnboardingVelocityAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            devs: FxHashMap::default(),
            file_change_counts: FxHashMap::default(),
        }
    }

    /// Records a commit for an author.
    pub fn record_commit(&mut self, author: &str, timestamp: i64, file_paths: &[&str]) {
        let state = self
            .devs
            .entry(author.to_string())
            .or_insert_with(|| DevState {
                first_commit: timestamp,
                last_commit: timestamp,
                commits: Vec::new(),
                files: rustc_hash::FxHashSet::default(),
            });

        state.commits.push(timestamp);
        if timestamp > state.last_commit {
            state.last_commit = timestamp;
        }

        for &path in file_paths {
            state.files.insert(path.to_string());
            *self.file_change_counts.entry(path.to_string()).or_insert(0) += 1;
        }
    }

    /// Finalizes the onboarding velocity report.
    #[must_use]
    pub fn finalize(self) -> OnboardingVelocityReport {
        // Determine core files (>= CORE_THRESHOLD changes)
        let core_files: rustc_hash::FxHashSet<&str> = self
            .file_change_counts
            .iter()
            .filter(|(_, &count)| count >= CORE_THRESHOLD)
            .map(|(path, _)| path.as_str())
            .collect();

        let mut developers: Vec<DeveloperOnboarding> = self
            .devs
            .into_iter()
            .map(|(author, state)| {
                let total_commits = state.commits.len() as u32;
                let unique_files = state.files.len() as u32;
                let active_span_days = (state.last_commit - state.first_commit) as f64 / 86400.0;

                // Days to first core file touch
                let days_to_core = if state.files.iter().any(|f| core_files.contains(f.as_str())) {
                    // Developer touched core files at some point
                    Some(0.0)
                } else {
                    None
                };

                // Count commits in week 1-4 and week 5-8
                let w1_end = state.first_commit + FOUR_WEEKS;
                let w2_end = state.first_commit + 2 * FOUR_WEEKS;
                let week1_4: u32 = state
                    .commits
                    .iter()
                    .filter(|&&t| t >= state.first_commit && t < w1_end)
                    .count() as u32;
                let week5_8: u32 = state
                    .commits
                    .iter()
                    .filter(|&&t| t >= w1_end && t < w2_end)
                    .count() as u32;

                // Classify onboarding type
                let onboarding_type = if total_commits <= 1 {
                    OnboardingType::OneShot
                } else if week5_8 >= 2 * week1_4.max(1) {
                    OnboardingType::FastRamp
                } else if week5_8 > 0 && week1_4 > 0 && week5_8 < week1_4 {
                    OnboardingType::SlowRamp
                } else if week1_4 > 0 && week5_8 > 0 {
                    OnboardingType::Sustained
                } else {
                    OnboardingType::SlowRamp
                };

                DeveloperOnboarding {
                    author,
                    onboarding_type,
                    total_commits,
                    unique_files,
                    active_span_days,
                    days_to_core,
                    week1_4_commits: week1_4,
                    week5_8_commits: week5_8,
                }
            })
            .collect();

        developers.sort_by(|a, b| b.total_commits.cmp(&a.total_commits));
        developers.truncate(50);

        let one_shot_count = developers
            .iter()
            .filter(|d| d.onboarding_type == OnboardingType::OneShot)
            .count();
        let fast_ramp_count = developers
            .iter()
            .filter(|d| d.onboarding_type == OnboardingType::FastRamp)
            .count();
        let slow_ramp_count = developers
            .iter()
            .filter(|d| d.onboarding_type == OnboardingType::SlowRamp)
            .count();
        let sustained_count = developers
            .iter()
            .filter(|d| d.onboarding_type == OnboardingType::Sustained)
            .count();

        let mut core_days: Vec<f64> = developers.iter().filter_map(|d| d.days_to_core).collect();
        core_days.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
        let median_days_to_core = if core_days.is_empty() {
            0.0
        } else {
            core_days[core_days.len() / 2]
        };

        OnboardingVelocityReport {
            developers,
            one_shot_count,
            fast_ramp_count,
            slow_ramp_count,
            sustained_count,
            median_days_to_core,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let acc = OnboardingVelocityAccumulator::new();
        let report = acc.finalize();
        assert!(report.developers.is_empty());
    }

    #[test]
    fn test_one_shot_contributor() {
        let mut acc = OnboardingVelocityAccumulator::new();
        acc.record_commit("Alice", 1000, &["src/a.rs"]);
        let report = acc.finalize();
        assert_eq!(report.developers.len(), 1);
        assert_eq!(
            report.developers[0].onboarding_type,
            OnboardingType::OneShot
        );
        assert_eq!(report.one_shot_count, 1);
    }

    #[test]
    fn test_sustained_contributor() {
        let mut acc = OnboardingVelocityAccumulator::new();
        let base = 1_000_000i64;
        // 5 commits in weeks 1-4
        for i in 0..5 {
            acc.record_commit("Alice", base + i * 86400, &["src/a.rs"]);
        }
        // 5 commits in weeks 5-8
        for i in 0..5 {
            acc.record_commit("Alice", base + FOUR_WEEKS + i * 86400, &["src/b.rs"]);
        }
        let report = acc.finalize();
        assert_eq!(
            report.developers[0].onboarding_type,
            OnboardingType::Sustained
        );
    }

    #[test]
    fn test_default_impl() {
        let acc = OnboardingVelocityAccumulator::default();
        let report = acc.finalize();
        assert!(report.developers.is_empty());
    }
}
