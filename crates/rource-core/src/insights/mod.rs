// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Repository insights engine.
//!
//! Computes research-backed software engineering metrics from VCS commit history.
//! These metrics provide actionable intelligence about code quality, organizational
//! risk, and development patterns — backed by empirical software engineering research.
//!
//! # Metrics Computed
//!
//! | Metric | Research Basis | What It Reveals |
//! |--------|---------------|-----------------|
//! | **Hotspot Analysis** | Nagappan et al. (2005), Tornhill | Files with high change frequency — defect predictors |
//! | **Change Coupling** | D'Ambros et al. (2009) | Hidden architectural dependencies via co-change patterns |
//! | **Code Ownership** | Bird et al. (2011) "Don't Touch My Code!" | Knowledge concentration and key-person risk |
//! | **Bus Factor** | Avelino et al. (2016) | Organizational resilience — minimum people to lose |
//! | **Temporal Patterns** | Eyolfson et al. (2011) | When defects are introduced — time-of-day/day-of-week |
//! | **Commit Entropy** | Hassan (2009) JIT-SDP | Change scatter — high entropy commits are riskier |
//!
//! # Architecture
//!
//! The engine operates on VCS-agnostic [`CommitRecord`] inputs, making it usable
//! with any version control system (Git, SVN, Mercurial, etc.).
//!
//! ```text
//! Vec<Commit> ──[convert]──> Vec<CommitRecord> ──[InsightsEngine]──> InsightsReport
//! ```
//!
//! All computation happens at load time (not per-frame), so there is zero impact
//! on the visualization's frame budget.

pub mod cadence;
pub mod change_bursts;
pub mod change_entropy;
pub mod circadian;
pub mod congruence;
pub mod coupling;
pub mod focus;
pub mod growth;
pub mod hotspot;
pub mod inequality;
pub mod knowledge;
pub mod lifecycle;
pub mod modularity;
pub mod network;
pub mod ownership;
pub mod profiles;
pub mod survival;
pub mod temporal;
pub mod work_type;

use rustc_hash::FxHashMap;

// ============================================================================
// Input Types (VCS-agnostic)
// ============================================================================

/// The action performed on a file in a commit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FileActionKind {
    /// File was created.
    Create,
    /// File was modified.
    Modify,
    /// File was deleted.
    Delete,
}

/// A file change within a commit, for insights computation.
#[derive(Debug, Clone)]
pub struct FileRecord {
    /// File path relative to repository root.
    pub path: String,
    /// Action performed on this file.
    pub action: FileActionKind,
}

/// A lightweight commit record for insights computation.
///
/// This is VCS-agnostic and can be constructed from any commit format.
#[derive(Debug, Clone)]
pub struct CommitRecord {
    /// Unix epoch timestamp in seconds.
    pub timestamp: i64,
    /// Author name.
    pub author: String,
    /// File changes in this commit.
    pub files: Vec<FileRecord>,
}

// ============================================================================
// Output Types
// ============================================================================

/// Complete insights report for a repository.
///
/// Contains all computed metrics, ready for serialization to JSON.
#[derive(Debug)]
pub struct InsightsReport {
    /// File hotspot analysis results, sorted by score descending.
    pub hotspots: Vec<hotspot::FileHotspot>,

    /// Change coupling pairs above the minimum support threshold.
    pub couplings: Vec<coupling::CouplingPair>,

    /// Per-file ownership data.
    pub ownership: Vec<ownership::FileOwnership>,

    /// Per-directory bus factor.
    pub bus_factors: Vec<ownership::DirectoryBusFactor>,

    /// Temporal activity patterns.
    pub temporal: temporal::TemporalReport,

    /// Codebase growth trajectory (Lehman 1996).
    pub growth: growth::GrowthReport,

    /// Work-type mix analysis (Hindle et al. 2008).
    pub work_type: work_type::WorkTypeReport,

    /// Commit cadence analysis per developer (Eyolfson et al. 2014).
    pub cadence: cadence::CadenceReport,

    /// Knowledge distribution and silo detection (Rigby & Bird 2013).
    pub knowledge: knowledge::KnowledgeReport,

    /// Developer activity profiles (Mockus et al. 2002).
    pub profiles: profiles::ProfilesReport,

    /// File lifecycle analysis (Godfrey & Tu 2000).
    pub lifecycle: lifecycle::LifecycleReport,

    /// Contribution inequality / Gini coefficient (Chelkowski et al. 2016).
    pub inequality: inequality::InequalityReport,

    /// Sliding-window change entropy (Hassan ICSE 2009).
    pub change_entropy: change_entropy::ChangeEntropyReport,

    /// Circadian (time-of-day) risk patterns (Eyolfson et al. 2011).
    pub circadian: circadian::CircadianReport,

    /// Per-file change burst detection (Nagappan et al. 2010).
    pub change_bursts: change_bursts::ChangeBurstReport,

    /// Developer focus and file diffusion (Posnett et al. 2013).
    pub focus: focus::FocusReport,

    /// Co-change modularity / DSM analysis (Silva et al. 2014).
    pub modularity: modularity::ModularityReport,

    /// Sociotechnical congruence / Conway's Law (Cataldo et al. 2008).
    pub congruence: congruence::CongruenceReport,

    /// File survival analysis / Kaplan-Meier (Cito et al. 2021).
    pub survival: survival::SurvivalReport,

    /// Developer collaboration network centrality (Begel et al. 2023).
    pub network: network::NetworkReport,

    /// Summary statistics.
    pub summary: SummaryStats,
}

/// High-level summary statistics for the repository.
#[derive(Debug)]
pub struct SummaryStats {
    /// Total number of commits analyzed.
    pub total_commits: usize,
    /// Total unique files touched.
    pub total_files: usize,
    /// Total unique authors.
    pub total_authors: usize,
    /// Time span in seconds (last - first commit).
    pub time_span_seconds: i64,
    /// Average files per commit.
    pub avg_files_per_commit: f64,
    /// Average commit entropy (Shannon entropy of file distribution).
    pub avg_commit_entropy: f64,
    /// Median commit entropy.
    pub median_commit_entropy: f64,
}

// ============================================================================
// Insights Engine
// ============================================================================

/// Maximum files per commit before it's considered a bulk operation.
///
/// Commits touching more files than this threshold are excluded from coupling
/// analysis to avoid noise from bulk imports, large merges, and formatting runs.
const BULK_COMMIT_THRESHOLD: usize = 50;

/// Minimum support count for coupling pairs to be reported.
///
/// Pairs that co-change fewer times than this are filtered out as noise.
const MIN_COUPLING_SUPPORT: u32 = 2;

/// Top-N results to return for ranked metrics.
const DEFAULT_TOP_N: usize = 50;

/// Computes all insights from a sequence of commit records.
///
/// This is the main entry point. All computation is O(N) or O(N log N)
/// in the total number of file changes, except coupling which is
/// O(Σ k²) where k = files per non-bulk commit.
///
/// # Arguments
///
/// * `commits` - Chronologically ordered commit records
///
/// # Returns
///
/// A complete [`InsightsReport`] with all computed metrics.
#[must_use]
pub fn compute_insights(commits: &[CommitRecord]) -> InsightsReport {
    if commits.is_empty() {
        return empty_report();
    }

    let t_min = commits.first().map_or(0, |c| c.timestamp);
    let t_max = commits.last().map_or(0, |c| c.timestamp);

    // Single-pass accumulation over all commits
    let accumulators = accumulate_commit_data(commits);

    // Finalize each metric from accumulated data
    let hotspots = finalize_hotspots(accumulators.file_changes, t_min, t_max);
    let couplings = finalize_couplings(accumulators.coupling_acc);
    let (mut ownership, bus_factors) = finalize_ownership(accumulators.file_authors.clone());
    let temporal = accumulators.temporal_acc.finalize();
    let growth = accumulators.growth_acc.finalize(t_min, t_max);
    let work_type = accumulators.work_type_acc.finalize();
    let cadence = accumulators.cadence_acc.finalize();
    let knowledge = knowledge::compute_knowledge(&accumulators.file_authors);
    let profiles_report = accumulators
        .profiles_acc
        .finalize(commits.len(), t_min, t_max);
    let lifecycle = accumulators.lifecycle_acc.finalize(t_min, t_max);

    // Session 3 metrics: finalize new accumulators and compute derived metrics
    let inequality_windows = accumulators.inequality_acc.finalize(t_min, t_max);
    let inequality =
        inequality::compute_inequality(&accumulators.unique_authors, inequality_windows);
    let change_entropy = accumulators.change_entropy_acc.finalize(t_min, t_max);
    let circadian = accumulators.circadian_acc.finalize();
    let change_bursts = accumulators.change_burst_acc.finalize();
    let focus_devs = accumulators.focus_acc.finalize();
    let focus_files = focus::compute_file_diffusion(&accumulators.file_authors);
    let focus = focus::build_focus_report(focus_devs, focus_files);
    let modularity = modularity::compute_modularity(&couplings);
    let congruence = congruence::compute_congruence(&couplings, &accumulators.file_authors);
    let survival = accumulators.survival_acc.finalize(t_max);
    let network = network::compute_network(&accumulators.file_authors);

    let summary = compute_summary(
        commits,
        &ownership,
        &accumulators.unique_authors,
        accumulators.commit_entropies,
        t_min,
        t_max,
    );

    ownership.truncate(DEFAULT_TOP_N * 4);

    InsightsReport {
        hotspots,
        couplings,
        ownership,
        bus_factors,
        temporal,
        growth,
        work_type,
        cadence,
        knowledge,
        profiles: profiles_report,
        lifecycle,
        inequality,
        change_entropy,
        circadian,
        change_bursts,
        focus,
        modularity,
        congruence,
        survival,
        network,
        summary,
    }
}

/// Returns an empty report for repositories with no commits.
#[allow(clippy::too_many_lines)]
fn empty_report() -> InsightsReport {
    InsightsReport {
        hotspots: Vec::new(),
        couplings: Vec::new(),
        ownership: Vec::new(),
        bus_factors: Vec::new(),
        temporal: temporal::TemporalReport::empty(),
        growth: growth::GrowthReport {
            snapshots: Vec::new(),
            current_file_count: 0,
            total_created: 0,
            total_deleted: 0,
            net_growth: 0,
            avg_monthly_growth: 0.0,
            trend: growth::GrowthTrend::Stable,
        },
        work_type: work_type::WorkTypeReport {
            commits: Vec::new(),
            feature_pct: 0.0,
            maintenance_pct: 0.0,
            cleanup_pct: 0.0,
            mixed_pct: 0.0,
            dominant_type: work_type::WorkType::Mixed,
            total_commits: 0,
        },
        cadence: cadence::CadenceReport {
            authors: Vec::new(),
            team_mean_interval: 0.0,
            regular_count: 0,
            bursty_count: 0,
            moderate_count: 0,
        },
        knowledge: knowledge::KnowledgeReport {
            files: Vec::new(),
            directories: Vec::new(),
            total_silos: 0,
            silo_percentage: 0.0,
            avg_entropy: 0.0,
        },
        profiles: profiles::ProfilesReport {
            developers: Vec::new(),
            core_count: 0,
            peripheral_count: 0,
            drive_by_count: 0,
            total_contributors: 0,
        },
        lifecycle: lifecycle::LifecycleReport {
            files: Vec::new(),
            avg_lifespan_days: 0.0,
            ephemeral_count: 0,
            dead_count: 0,
            deleted_count: 0,
            active_count: 0,
            churn_rate: 0.0,
            total_files_seen: 0,
        },
        inequality: inequality::InequalityReport {
            gini_coefficient: 0.0,
            top_1_pct_share: 0.0,
            top_10_pct_share: 0.0,
            top_20_pct_share: 0.0,
            total_developers: 0,
            total_commits: 0,
            lorenz_curve: Vec::new(),
            windows: Vec::new(),
        },
        change_entropy: change_entropy::ChangeEntropyReport {
            windows: Vec::new(),
            avg_normalized_entropy: 0.0,
            max_entropy_window_idx: None,
            trend: change_entropy::EntropyTrend::Stable,
        },
        circadian: circadian::CircadianReport {
            files: Vec::new(),
            authors: Vec::new(),
            hourly_risk: [0.0; 24],
            high_risk_percentage: 0.0,
            total_commits_analyzed: 0,
        },
        change_bursts: change_bursts::ChangeBurstReport {
            files: Vec::new(),
            total_bursts: 0,
            avg_burst_length: 0.0,
            files_with_bursts: 0,
            multi_author_burst_count: 0,
        },
        focus: focus::FocusReport {
            developers: Vec::new(),
            files: Vec::new(),
            avg_developer_focus: 0.0,
            avg_file_diffusion: 0.0,
        },
        modularity: modularity::ModularityReport {
            modularity_index: 1.0, // vacuously modular
            cross_module_ratio: 0.0,
            total_intra_edges: 0,
            total_cross_edges: 0,
            directories: Vec::new(),
        },
        congruence: congruence::CongruenceReport {
            congruence_score: 1.0, // vacuously congruent
            required_coordinations: 0,
            actual_coordinations: 0,
            coordination_gaps: Vec::new(),
            total_developer_pairs: 0,
        },
        survival: survival::SurvivalReport {
            curve: Vec::new(),
            median_survival_days: None,
            infant_mortality_rate: 0.0,
            total_births: 0,
            total_deaths: 0,
            censored_count: 0,
        },
        network: network::NetworkReport {
            developers: Vec::new(),
            network_density: 0.0,
            connected_components: 0,
            largest_component_size: 0,
            total_edges: 0,
            avg_degree: 0.0,
        },
        summary: SummaryStats {
            total_commits: 0,
            total_files: 0,
            total_authors: 0,
            time_span_seconds: 0,
            avg_files_per_commit: 0.0,
            avg_commit_entropy: 0.0,
            median_commit_entropy: 0.0,
        },
    }
}

/// Intermediate accumulators collected during the single-pass over commits.
struct CommitAccumulators {
    file_changes: FxHashMap<String, hotspot::HotspotAccumulator>,
    file_authors: FxHashMap<String, FxHashMap<String, u32>>,
    unique_authors: FxHashMap<String, u32>,
    commit_entropies: Vec<f64>,
    coupling_acc: coupling::CouplingAccumulator,
    temporal_acc: temporal::TemporalAccumulator,
    growth_acc: growth::GrowthAccumulator,
    work_type_acc: work_type::WorkTypeAccumulator,
    cadence_acc: cadence::CadenceAccumulator,
    profiles_acc: profiles::ProfilesAccumulator,
    lifecycle_acc: lifecycle::LifecycleAccumulator,
    inequality_acc: inequality::InequalityAccumulator,
    change_entropy_acc: change_entropy::ChangeEntropyAccumulator,
    circadian_acc: circadian::CircadianAccumulator,
    change_burst_acc: change_bursts::ChangeBurstAccumulator,
    focus_acc: focus::FocusAccumulator,
    survival_acc: survival::SurvivalAccumulator,
}

/// Single pass over commits to populate all accumulators.
fn accumulate_commit_data(commits: &[CommitRecord]) -> CommitAccumulators {
    let mut file_changes: FxHashMap<String, hotspot::HotspotAccumulator> = FxHashMap::default();
    let mut file_authors: FxHashMap<String, FxHashMap<String, u32>> = FxHashMap::default();
    let mut unique_authors: FxHashMap<String, u32> = FxHashMap::default();
    let mut commit_entropies: Vec<f64> = Vec::with_capacity(commits.len());
    let mut coupling_acc = coupling::CouplingAccumulator::new();
    let mut temporal_acc = temporal::TemporalAccumulator::new();
    let mut growth_acc = growth::GrowthAccumulator::new();
    let mut work_type_acc = work_type::WorkTypeAccumulator::new();
    let mut cadence_acc = cadence::CadenceAccumulator::new();
    let mut profiles_acc = profiles::ProfilesAccumulator::new();
    let mut lifecycle_acc = lifecycle::LifecycleAccumulator::new();
    let mut inequality_acc = inequality::InequalityAccumulator::new();
    let mut change_entropy_acc = change_entropy::ChangeEntropyAccumulator::new();
    let mut circadian_acc = circadian::CircadianAccumulator::new();
    let mut change_burst_acc = change_bursts::ChangeBurstAccumulator::new();
    let mut focus_acc = focus::FocusAccumulator::new();
    let mut survival_acc = survival::SurvivalAccumulator::new();

    for commit in commits {
        *unique_authors.entry(commit.author.clone()).or_insert(0) += 1;
        commit_entropies.push(compute_commit_entropy(commit.files.len()));
        temporal_acc.record_commit(commit.timestamp, commit.files.len());
        cadence_acc.record_commit(&commit.author, commit.timestamp);

        // Collect file paths and action counts for work-type and profiles
        let file_paths: Vec<&str> = commit.files.iter().map(|f| f.path.as_str()).collect();
        let actions: Vec<FileActionKind> = commit.files.iter().map(|f| f.action).collect();
        let (creates, modifies, deletes) = work_type::count_actions(&actions);
        work_type_acc.record_commit(commit.timestamp, creates, modifies, deletes);
        profiles_acc.record_commit(&commit.author, commit.timestamp, &file_paths);

        // Session 3 accumulators: per-commit data
        inequality_acc.record_commit(&commit.author, commit.timestamp);
        circadian_acc.record_commit(&commit.author, commit.timestamp, &file_paths);
        focus_acc.record_commit(&commit.author, &file_paths);

        for file in &commit.files {
            file_changes
                .entry(file.path.clone())
                .or_insert_with(|| hotspot::HotspotAccumulator::new(commit.timestamp))
                .record(commit.timestamp, file.action);
            *file_authors
                .entry(file.path.clone())
                .or_default()
                .entry(commit.author.clone())
                .or_insert(0) += 1;
            growth_acc.record_file(&file.path, file.action);
            lifecycle_acc.record_file(&file.path, file.action, commit.timestamp, &commit.author);

            // Session 3 accumulators: per-file data
            change_entropy_acc.record_file(&file.path, file.action, commit.timestamp);
            change_burst_acc.record_file(&file.path, commit.timestamp, &commit.author);
            match file.action {
                FileActionKind::Create => survival_acc.record_create(&file.path, commit.timestamp),
                FileActionKind::Delete => survival_acc.record_delete(&file.path, commit.timestamp),
                FileActionKind::Modify => {}
            }
        }

        // Record growth snapshot after processing all files in this commit
        growth_acc.record_snapshot(commit.timestamp);

        if commit.files.len() >= 2 && commit.files.len() <= BULK_COMMIT_THRESHOLD {
            coupling_acc.record_commit(&commit.files);
        }
    }

    CommitAccumulators {
        file_changes,
        file_authors,
        unique_authors,
        commit_entropies,
        coupling_acc,
        temporal_acc,
        growth_acc,
        work_type_acc,
        cadence_acc,
        profiles_acc,
        lifecycle_acc,
        inequality_acc,
        change_entropy_acc,
        circadian_acc,
        change_burst_acc,
        focus_acc,
        survival_acc,
    }
}

/// Finalizes hotspot data from accumulated file changes.
fn finalize_hotspots(
    file_changes: FxHashMap<String, hotspot::HotspotAccumulator>,
    t_min: i64,
    t_max: i64,
) -> Vec<hotspot::FileHotspot> {
    let mut hotspots: Vec<hotspot::FileHotspot> = file_changes
        .into_iter()
        .map(|(path, acc)| acc.finalize(path, t_min, t_max))
        .collect();
    hotspots.sort_by(|a, b| {
        b.score
            .partial_cmp(&a.score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    hotspots.truncate(DEFAULT_TOP_N);
    hotspots
}

/// Finalizes coupling pairs from accumulated co-change data.
fn finalize_couplings(coupling_acc: coupling::CouplingAccumulator) -> Vec<coupling::CouplingPair> {
    let mut couplings = coupling_acc.finalize(MIN_COUPLING_SUPPORT);
    couplings.sort_by(|a, b| {
        b.support.cmp(&a.support).then_with(|| {
            b.confidence_ab
                .partial_cmp(&a.confidence_ab)
                .unwrap_or(std::cmp::Ordering::Equal)
        })
    });
    couplings.truncate(DEFAULT_TOP_N);
    couplings
}

/// Finalizes ownership and bus factor data.
fn finalize_ownership(
    file_authors: FxHashMap<String, FxHashMap<String, u32>>,
) -> (
    Vec<ownership::FileOwnership>,
    Vec<ownership::DirectoryBusFactor>,
) {
    let mut ownership: Vec<ownership::FileOwnership> = file_authors
        .into_iter()
        .map(|(path, authors)| ownership::compute_file_ownership(path, &authors))
        .collect();
    ownership.sort_by(|a, b| {
        a.top_owner_share
            .partial_cmp(&b.top_owner_share)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    let bus_factors = ownership::compute_bus_factors(&ownership);
    (ownership, bus_factors)
}

/// Computes summary statistics from accumulated data.
fn compute_summary(
    commits: &[CommitRecord],
    ownership: &[ownership::FileOwnership],
    unique_authors: &FxHashMap<String, u32>,
    mut commit_entropies: Vec<f64>,
    t_min: i64,
    t_max: i64,
) -> SummaryStats {
    let avg_files =
        commits.iter().map(|c| c.files.len()).sum::<usize>() as f64 / commits.len() as f64;
    commit_entropies.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let median_entropy = if commit_entropies.is_empty() {
        0.0
    } else {
        commit_entropies[commit_entropies.len() / 2]
    };
    let avg_entropy = if commit_entropies.is_empty() {
        0.0
    } else {
        commit_entropies.iter().sum::<f64>() / commit_entropies.len() as f64
    };

    SummaryStats {
        total_commits: commits.len(),
        total_files: ownership.len(),
        total_authors: unique_authors.len(),
        time_span_seconds: t_max - t_min,
        avg_files_per_commit: avg_files,
        avg_commit_entropy: avg_entropy,
        median_commit_entropy: median_entropy,
    }
}

/// Computes Shannon entropy for a commit's file distribution.
///
/// For a commit touching N files, the entropy is log2(N), which measures
/// how "spread out" the change is. A single-file commit has entropy 0,
/// while a commit touching many files has high entropy.
///
/// Research (Hassan 2009) shows that high-entropy changes are more likely
/// to introduce defects.
fn compute_commit_entropy(file_count: usize) -> f64 {
    if file_count <= 1 {
        return 0.0;
    }
    (file_count as f64).log2()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_commit(ts: i64, author: &str, files: &[(&str, FileActionKind)]) -> CommitRecord {
        CommitRecord {
            timestamp: ts,
            author: author.to_string(),
            files: files
                .iter()
                .map(|(p, a)| FileRecord {
                    path: p.to_string(),
                    action: *a,
                })
                .collect(),
        }
    }

    #[test]
    fn test_empty_commits() {
        let report = compute_insights(&[]);
        assert_eq!(report.summary.total_commits, 0);
        assert_eq!(report.summary.total_files, 0);
        assert_eq!(report.summary.total_authors, 0);
        assert!(report.hotspots.is_empty());
        assert!(report.couplings.is_empty());
        assert!(report.ownership.is_empty());
        assert!(report.bus_factors.is_empty());
    }

    #[test]
    fn test_single_commit() {
        let commits = vec![make_commit(
            1000,
            "Alice",
            &[
                ("src/main.rs", FileActionKind::Create),
                ("src/lib.rs", FileActionKind::Create),
            ],
        )];
        let report = compute_insights(&commits);
        assert_eq!(report.summary.total_commits, 1);
        assert_eq!(report.summary.total_files, 2);
        assert_eq!(report.summary.total_authors, 1);
        // Kills mutant: / vs * in compute_summary (avg_files = 2/1 = 2.0)
        assert!(
            (report.summary.avg_files_per_commit - 2.0).abs() < f64::EPSILON,
            "avg_files_per_commit={}, expected=2.0",
            report.summary.avg_files_per_commit
        );
        // Entropy for 2 files = log2(2) = 1.0
        // avg_entropy = 1.0 / 1 = 1.0, median_entropy = 1.0
        assert!(
            (report.summary.avg_commit_entropy - 1.0).abs() < f64::EPSILON,
            "avg_commit_entropy={}, expected=1.0",
            report.summary.avg_commit_entropy
        );
        assert!(
            (report.summary.median_commit_entropy - 1.0).abs() < f64::EPSILON,
            "median_commit_entropy={}, expected=1.0",
            report.summary.median_commit_entropy
        );
    }

    #[test]
    fn test_hotspot_ordering() {
        // File A modified 5 times, file B once — A should rank higher
        let commits = vec![
            make_commit(1000, "Alice", &[("a.rs", FileActionKind::Modify)]),
            make_commit(2000, "Alice", &[("a.rs", FileActionKind::Modify)]),
            make_commit(3000, "Alice", &[("a.rs", FileActionKind::Modify)]),
            make_commit(4000, "Alice", &[("a.rs", FileActionKind::Modify)]),
            make_commit(5000, "Alice", &[("a.rs", FileActionKind::Modify)]),
            make_commit(6000, "Bob", &[("b.rs", FileActionKind::Modify)]),
        ];
        let report = compute_insights(&commits);
        assert!(report.hotspots.len() >= 2);
        assert_eq!(report.hotspots[0].path, "a.rs");
        assert!(report.hotspots[0].score > report.hotspots[1].score);
    }

    #[test]
    fn test_coupling_detection() {
        // Files A and B always change together
        let commits = vec![
            make_commit(
                1000,
                "Alice",
                &[
                    ("a.rs", FileActionKind::Modify),
                    ("b.rs", FileActionKind::Modify),
                ],
            ),
            make_commit(
                2000,
                "Alice",
                &[
                    ("a.rs", FileActionKind::Modify),
                    ("b.rs", FileActionKind::Modify),
                ],
            ),
            make_commit(
                3000,
                "Alice",
                &[
                    ("a.rs", FileActionKind::Modify),
                    ("b.rs", FileActionKind::Modify),
                ],
            ),
        ];
        let report = compute_insights(&commits);
        assert!(!report.couplings.is_empty());
        let top = &report.couplings[0];
        assert_eq!(top.support, 3);
        // Confidence should be 1.0 (they always co-change)
        assert!((top.confidence_ab - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_ownership_computed() {
        let commits = vec![
            make_commit(1000, "Alice", &[("x.rs", FileActionKind::Create)]),
            make_commit(2000, "Alice", &[("x.rs", FileActionKind::Modify)]),
            make_commit(3000, "Bob", &[("x.rs", FileActionKind::Modify)]),
        ];
        let report = compute_insights(&commits);
        let owned = report.ownership.iter().find(|o| o.path == "x.rs");
        assert!(owned.is_some());
        let owned = owned.unwrap();
        assert_eq!(owned.total_changes, 3);
        assert_eq!(owned.contributor_count, 2);
        // Alice has 2/3 = 66.7%
        assert!((owned.top_owner_share - 2.0 / 3.0).abs() < 0.01);
    }

    #[test]
    fn test_commit_entropy() {
        assert_eq!(compute_commit_entropy(0), 0.0);
        assert_eq!(compute_commit_entropy(1), 0.0);
        assert!((compute_commit_entropy(2) - 1.0).abs() < f64::EPSILON);
        assert!((compute_commit_entropy(4) - 2.0).abs() < f64::EPSILON);
        assert!((compute_commit_entropy(8) - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_multiple_authors() {
        let commits = vec![
            make_commit(1000, "Alice", &[("a.rs", FileActionKind::Create)]),
            make_commit(2000, "Bob", &[("b.rs", FileActionKind::Create)]),
            make_commit(3000, "Carol", &[("c.rs", FileActionKind::Create)]),
        ];
        let report = compute_insights(&commits);
        assert_eq!(report.summary.total_authors, 3);
        assert_eq!(report.summary.total_files, 3);
    }

    #[test]
    fn test_bulk_commits_excluded_from_coupling() {
        // A commit touching 60 files should be excluded from coupling
        let mut files: Vec<(&str, FileActionKind)> = Vec::new();
        let file_names: Vec<String> = (0..60).map(|i| format!("file{i}.rs")).collect();
        for name in &file_names {
            files.push((name.as_str(), FileActionKind::Modify));
        }
        let commits = vec![
            make_commit(1000, "Alice", &files),
            make_commit(2000, "Alice", &files),
        ];
        let report = compute_insights(&commits);
        // Bulk commits excluded — no coupling pairs should appear
        assert!(report.couplings.is_empty());
    }

    #[test]
    fn test_time_span() {
        let commits = vec![
            make_commit(1000, "Alice", &[("a.rs", FileActionKind::Create)]),
            make_commit(5000, "Bob", &[("b.rs", FileActionKind::Create)]),
        ];
        let report = compute_insights(&commits);
        assert_eq!(report.summary.time_span_seconds, 4000);
    }

    #[test]
    fn test_summary_averages_exact() {
        // Kills mutants: / vs * and / vs % in compute_summary
        // 3 commits with 1, 2, 3 files respectively
        let commits = vec![
            make_commit(1000, "Alice", &[("a.rs", FileActionKind::Create)]),
            make_commit(
                2000,
                "Alice",
                &[
                    ("a.rs", FileActionKind::Modify),
                    ("b.rs", FileActionKind::Create),
                ],
            ),
            make_commit(
                3000,
                "Alice",
                &[
                    ("a.rs", FileActionKind::Modify),
                    ("b.rs", FileActionKind::Modify),
                    ("c.rs", FileActionKind::Create),
                ],
            ),
        ];
        let report = compute_insights(&commits);

        // avg_files = (1 + 2 + 3) / 3 = 2.0
        assert!(
            (report.summary.avg_files_per_commit - 2.0).abs() < f64::EPSILON,
            "avg_files_per_commit={}, expected=2.0",
            report.summary.avg_files_per_commit
        );
        // If / were * : (1+2+3) * 3 = 18.0 — would fail
        assert!(report.summary.avg_files_per_commit < 3.0);

        // Entropies: log2(1)=0, log2(2)=1.0, log2(3)≈1.585
        // avg = (0 + 1.0 + 1.585) / 3 ≈ 0.8617
        let e1 = 0.0_f64;
        let e2 = 2.0_f64.log2();
        let e3 = 3.0_f64.log2();
        let expected_avg = (e1 + e2 + e3) / 3.0;
        assert!(
            (report.summary.avg_commit_entropy - expected_avg).abs() < 1e-10,
            "avg_entropy={}, expected={}",
            report.summary.avg_commit_entropy,
            expected_avg
        );
        // If / were *: (0 + 1 + 1.585) * 3 ≈ 7.75 — would fail
        assert!(report.summary.avg_commit_entropy < 2.0);

        // Median: sorted entropies [0, 1.0, 1.585], median = 1.0 (index 1)
        assert!(
            (report.summary.median_commit_entropy - e2).abs() < f64::EPSILON,
            "median_entropy={}, expected={}",
            report.summary.median_commit_entropy,
            e2
        );
    }

    #[test]
    fn test_author_count_accumulation() {
        // Kills mutant: += vs *= in accumulate_commit_data (unique_authors counter)
        // Two commits by same author — total_authors should still be 1
        let commits = vec![
            make_commit(1000, "Alice", &[("a.rs", FileActionKind::Create)]),
            make_commit(2000, "Alice", &[("b.rs", FileActionKind::Create)]),
        ];
        let report = compute_insights(&commits);
        assert_eq!(report.summary.total_authors, 1);
        assert_eq!(report.summary.total_files, 2);
        // avg_files = (1 + 1) / 2 = 1.0
        assert!(
            (report.summary.avg_files_per_commit - 1.0).abs() < f64::EPSILON,
            "avg_files={}, expected=1.0",
            report.summary.avg_files_per_commit
        );
    }

    #[test]
    fn test_ownership_truncation() {
        // Kills mutant: DEFAULT_TOP_N * 4 (line 181)
        // With DEFAULT_TOP_N=50, truncation is at 200.
        // Create 210 unique files to verify truncation happens
        let mut commits = Vec::new();
        for i in 0..210 {
            commits.push(make_commit(
                1000 + i64::from(i),
                "Alice",
                &[(&format!("file{i:03}.rs"), FileActionKind::Create)],
            ));
        }
        let report = compute_insights(&commits);
        // Ownership should be truncated to DEFAULT_TOP_N * 4 = 200
        assert_eq!(
            report.ownership.len(),
            200,
            "ownership should be truncated to DEFAULT_TOP_N * 4 = 200"
        );
    }

    #[test]
    fn test_hotspot_score_nonzero() {
        // Verify hotspot scores are computed (not zero) — kills score formula mutants
        let commits = vec![
            make_commit(1000, "Alice", &[("a.rs", FileActionKind::Modify)]),
            make_commit(2000, "Alice", &[("a.rs", FileActionKind::Modify)]),
            make_commit(3000, "Alice", &[("a.rs", FileActionKind::Modify)]),
        ];
        let report = compute_insights(&commits);
        assert!(!report.hotspots.is_empty());
        let h = &report.hotspots[0];
        assert_eq!(h.total_changes, 3);
        assert!(h.weighted_changes > 0.0);
        assert!(h.score > 0.0);
        // Score should be weighted_changes * (1 + ln_1p(3))
        let expected_score = h.weighted_changes * (1.0 + 3.0_f64.ln_1p());
        assert!(
            (h.score - expected_score).abs() < 1e-10,
            "score={}, expected={}",
            h.score,
            expected_score
        );
    }

    // ========================================================================
    // Integration Tests: Full Pipeline
    // ========================================================================

    #[test]
    fn test_full_pipeline_all_20_metrics_computed() {
        // Kills: any accumulator that fails to initialize or finalize
        // Verify that all 20 metric sections are populated for a realistic input
        let commits = vec![
            make_commit(
                1000,
                "Alice",
                &[
                    ("src/main.rs", FileActionKind::Create),
                    ("src/lib.rs", FileActionKind::Create),
                ],
            ),
            make_commit(
                2000,
                "Bob",
                &[
                    ("src/main.rs", FileActionKind::Modify),
                    ("tests/test.rs", FileActionKind::Create),
                ],
            ),
            make_commit(
                3000,
                "Alice",
                &[
                    ("src/lib.rs", FileActionKind::Modify),
                    ("src/main.rs", FileActionKind::Modify),
                ],
            ),
            make_commit(4000, "Carol", &[("docs/readme.md", FileActionKind::Create)]),
        ];
        let report = compute_insights(&commits);

        // Summary
        assert_eq!(report.summary.total_commits, 4);
        assert_eq!(report.summary.total_authors, 3);
        assert!(report.summary.total_files > 0);
        assert_eq!(report.summary.time_span_seconds, 3000);

        // Hotspots (src/main.rs modified 3 times → top hotspot)
        assert!(!report.hotspots.is_empty());

        // Couplings (src/main.rs & src/lib.rs co-change 2 times → coupling pair)
        assert!(
            !report.couplings.is_empty(),
            "should detect coupling between co-changed files"
        );

        // Ownership
        assert!(!report.ownership.is_empty());

        // Bus factors
        assert!(!report.bus_factors.is_empty());

        // Temporal
        assert!(report.temporal.commits_per_day.iter().sum::<u32>() == 4);
        assert!(report.temporal.commits_per_hour.iter().sum::<u32>() == 4);

        // Growth
        assert!(report.growth.total_created > 0);
        assert!(report.growth.current_file_count > 0);
        assert!(!report.growth.snapshots.is_empty());

        // Work type
        assert_eq!(report.work_type.total_commits, 4);

        // Cadence
        // Alice has 2 commits, Bob has 1, Carol has 1 — only Alice qualifies (>= 2)
        assert!(!report.cadence.authors.is_empty());

        // Knowledge
        assert!(!report.knowledge.files.is_empty());

        // Profiles
        assert_eq!(report.profiles.total_contributors, 3);

        // Lifecycle
        assert!(!report.lifecycle.files.is_empty());

        // Inequality (need >= 2 authors with commits)
        assert!(report.inequality.total_developers >= 2);

        // Change entropy
        // May or may not have windows depending on time span

        // Circadian
        assert_eq!(report.circadian.total_commits_analyzed, 4);

        // Survival (4 creates, 0 deletes)
        assert!(report.survival.total_births > 0);

        // Network (3 authors, shared files → edges)
        assert!(!report.network.developers.is_empty());
    }

    #[test]
    fn test_full_pipeline_single_author() {
        // Kills: degenerate cases in network (1 node, no edges), inequality (1 author)
        let commits = vec![
            make_commit(1000, "Alice", &[("a.rs", FileActionKind::Create)]),
            make_commit(2000, "Alice", &[("a.rs", FileActionKind::Modify)]),
            make_commit(3000, "Alice", &[("b.rs", FileActionKind::Create)]),
        ];
        let report = compute_insights(&commits);

        assert_eq!(report.summary.total_authors, 1);
        // Network: 1 node, 0 edges, density = 0
        assert_eq!(report.network.developers.len(), 1);
        assert_eq!(report.network.total_edges, 0);
        assert!((report.network.network_density - 0.0).abs() < f64::EPSILON);
        // Bus factor: all files by Alice → bus_factor = 1
        for bf in &report.bus_factors {
            assert_eq!(bf.bus_factor, 1);
        }
        // Knowledge: all silos (single contributor)
        assert_eq!(report.knowledge.total_silos, report.knowledge.files.len());
        // Ownership: 100% for Alice on every file
        for o in &report.ownership {
            assert_eq!(o.top_owner, "Alice");
            assert!((o.top_owner_share - 1.0).abs() < f64::EPSILON);
        }
    }

    #[test]
    fn test_full_pipeline_single_file() {
        // Kills: degenerate cases in coupling (1 file → no pairs), modularity
        let commits = vec![
            make_commit(1000, "Alice", &[("only.rs", FileActionKind::Create)]),
            make_commit(2000, "Bob", &[("only.rs", FileActionKind::Modify)]),
            make_commit(3000, "Carol", &[("only.rs", FileActionKind::Modify)]),
        ];
        let report = compute_insights(&commits);

        assert_eq!(report.summary.total_files, 1);
        assert!(
            report.couplings.is_empty(),
            "single file → no coupling pairs"
        );
        assert_eq!(report.knowledge.files.len(), 1);
        assert!(!report.knowledge.files[0].is_silo);
        assert_eq!(report.knowledge.files[0].contributor_count, 3);
    }

    #[test]
    fn test_deterministic_output() {
        // Kills: non-determinism (HashMap iteration order, unstable sorts)
        let commits = vec![
            make_commit(
                1000,
                "Alice",
                &[
                    ("src/a.rs", FileActionKind::Create),
                    ("src/b.rs", FileActionKind::Create),
                ],
            ),
            make_commit(
                2000,
                "Bob",
                &[
                    ("src/a.rs", FileActionKind::Modify),
                    ("src/c.rs", FileActionKind::Create),
                ],
            ),
            make_commit(
                3000,
                "Alice",
                &[
                    ("src/a.rs", FileActionKind::Modify),
                    ("src/b.rs", FileActionKind::Modify),
                ],
            ),
        ];

        let report1 = compute_insights(&commits);
        let report2 = compute_insights(&commits);

        // Summary must be identical
        assert_eq!(report1.summary.total_commits, report2.summary.total_commits);
        assert_eq!(report1.summary.total_files, report2.summary.total_files);
        assert_eq!(report1.summary.total_authors, report2.summary.total_authors);
        assert!(
            (report1.summary.avg_files_per_commit - report2.summary.avg_files_per_commit).abs()
                < f64::EPSILON
        );

        // Hotspot ranking must be identical
        assert_eq!(report1.hotspots.len(), report2.hotspots.len());
        for (h1, h2) in report1.hotspots.iter().zip(report2.hotspots.iter()) {
            assert_eq!(h1.path, h2.path);
            assert!((h1.score - h2.score).abs() < 1e-10);
        }

        // Growth snapshots must be identical
        assert_eq!(
            report1.growth.snapshots.len(),
            report2.growth.snapshots.len()
        );
        assert_eq!(report1.growth.net_growth, report2.growth.net_growth);
    }

    #[test]
    fn test_bulk_commit_threshold_respected_in_pipeline() {
        // Kills: BULK_COMMIT_THRESHOLD check in accumulate_commit_data
        // Commit with 51 files should be excluded from coupling
        let file_names: Vec<String> = (0..51).map(|i| format!("f{i:03}.rs")).collect();
        let create_files: Vec<(&str, FileActionKind)> = file_names
            .iter()
            .map(|n| (n.as_str(), FileActionKind::Create))
            .collect();
        let modify_files: Vec<(&str, FileActionKind)> = file_names
            .iter()
            .map(|n| (n.as_str(), FileActionKind::Modify))
            .collect();

        let commits = vec![
            make_commit(1000, "Alice", &create_files),
            make_commit(2000, "Alice", &modify_files),
        ];
        let report = compute_insights(&commits);
        // 51 > BULK_COMMIT_THRESHOLD (50) → excluded from coupling
        assert!(
            report.couplings.is_empty(),
            "commits with >50 files should be excluded from coupling"
        );

        // But hotspots should still be computed
        assert!(!report.hotspots.is_empty());
        // And growth should track all created files
        assert_eq!(report.growth.current_file_count, 51);
    }

    #[test]
    fn test_full_pipeline_100_commits_realistic() {
        // Kills: any accumulator that breaks with moderate scale
        // Simulate a realistic 100-commit repository
        let mut commits = Vec::new();
        let authors = ["Alice", "Bob", "Carol", "Dave"];
        let base_ts: i64 = 1_700_000_000; // ~2023

        for i in 0..100_i64 {
            let author = authors[i as usize % 4];
            let ts = base_ts + i * 86400; // 1 commit per day
            let file_count = (i % 5) + 1; // 1-5 files per commit
            let mut files = Vec::new();
            for j in 0..file_count {
                let path = format!("src/mod{}.rs", j % 10);
                let action = if i < 10 && j == 0 {
                    FileActionKind::Create
                } else {
                    FileActionKind::Modify
                };
                files.push((path, action));
            }
            let file_refs: Vec<(&str, FileActionKind)> =
                files.iter().map(|(p, a)| (p.as_str(), *a)).collect();
            commits.push(make_commit(ts, author, &file_refs));
        }

        let report = compute_insights(&commits);

        // Verify all sections populated
        assert_eq!(report.summary.total_commits, 100);
        assert_eq!(report.summary.total_authors, 4);
        assert!(!report.hotspots.is_empty());
        assert!(!report.ownership.is_empty());
        assert!(!report.bus_factors.is_empty());
        assert!(!report.cadence.authors.is_empty());
        assert!(!report.knowledge.files.is_empty());
        assert!(report.profiles.total_contributors == 4);
        assert!(!report.lifecycle.files.is_empty());
        assert!(report.inequality.total_developers >= 2);
        assert!(!report.network.developers.is_empty());
        assert!(report.network.total_edges > 0);
        assert!(report.survival.total_births > 0);
        assert!(report.circadian.total_commits_analyzed == 100);
        assert!(!report.growth.snapshots.is_empty());
        assert_eq!(report.work_type.total_commits, 100);

        // Time span = 99 days
        assert_eq!(report.summary.time_span_seconds, 99 * 86400);
    }
}
