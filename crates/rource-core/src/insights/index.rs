// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Insights index: O(1) per-entity lookup tables for academic metrics.
//!
//! The [`InsightsIndex`] aggregates data from all 20+ insight metrics into
//! flat, render-friendly structs keyed by file path or author name. This
//! enables the visualization layer to query per-entity academic metrics
//! in O(1) time via `FxHashMap` lookup — zero computation in the render loop.
//!
//! # Architecture
//!
//! ```text
//! InsightsReport (20+ metrics, each with Vec<PerFileData>)
//!   ├── hotspots:    Vec<FileHotspot>
//!   ├── ownership:   Vec<FileOwnership>
//!   ├── lifecycle:   Vec<FileLifecycle>
//!   ├── ...
//!   └── network:     NetworkReport
//!         │
//!         ▼  InsightsIndex::from_report()
//! InsightsIndex
//!   ├── files:  FxHashMap<String, FileMetrics>      ← O(1) per file
//!   ├── users:  FxHashMap<String, UserMetrics>      ← O(1) per user
//!   └── summary: IndexSummary                       ← aggregate stats
//! ```
//!
//! # Academic Citations
//!
//! Per-file metrics aggregate findings from:
//! - **Hotspot score**: Nagappan & Ball (ICSE 2005) — relative code churn
//! - **Ownership**: Bird et al. (ICSE 2011) — "Don't Touch My Code!"
//! - **Bus factor**: Avelino et al. (MSR 2016) — truck factor
//! - **Lifecycle**: Godfrey & Tu (ICSM 2000) — software evolution
//! - **Change bursts**: Nagappan et al. (ICSE 2010) — change burst risk
//! - **Circadian risk**: Eyolfson et al. (MSR 2011) — time-of-day defects
//! - **Knowledge entropy**: Rigby & Bird (FSE 2013) — knowledge silos
//! - **File diffusion**: Posnett et al. (ICSE 2013) — developer focus
//! - **Change coupling**: D'Ambros et al. (TSE 2009) — co-change patterns
//!
//! Per-user metrics aggregate findings from:
//! - **Developer profiles**: Mockus et al. (TSE 2002) — core/peripheral
//! - **Commit cadence**: Eyolfson et al. (MSR 2014) — rhythm patterns
//! - **Network centrality**: Meneely & Williams (FSE 2009) — collaboration
//! - **Focus score**: Posnett et al. (ICSE 2013) — developer diffusion
//! - **Circadian risk**: Eyolfson et al. (MSR 2011) — per-author risk
//!
//! # Performance
//!
//! - **Build time**: O(F + U + C) where F = files, U = users, C = couplings
//! - **Lookup time**: O(1) amortized (`FxHashMap`)
//! - **Memory**: ~120 bytes per file + ~80 bytes per user (flat structs)
//! - **Render impact**: Zero — index is built once at load time

use rustc_hash::FxHashMap;

use super::InsightsReport;

// ============================================================================
// Per-File Academic Metrics
// ============================================================================

/// Aggregated academic metrics for a single file.
///
/// All fields are pre-computed from the [`InsightsReport`] at load time.
/// Access during rendering is O(1) via `InsightsIndex::file_metrics()`.
#[derive(Debug, Clone)]
pub struct FileMetrics {
    /// Hotspot score (Nagappan & Ball 2005): composite recency-weighted
    /// change frequency. Higher values indicate defect-prone files.
    /// Range: 0.0+ (unbounded, monotonically increasing with churn).
    pub hotspot_score: f64,

    /// Rank in the hotspot list (0 = top hotspot, None = not in top-N).
    pub hotspot_rank: Option<u32>,

    /// Total number of changes to this file across all commits.
    pub total_changes: u32,

    /// Number of distinct contributors who modified this file.
    /// Bird et al. (2011): contributor count correlates with defect density.
    pub contributor_count: u32,

    /// Share of changes by the top contributor (0.0–1.0).
    /// 1.0 = single owner, 0.5 = two equal owners.
    pub top_owner_share: f64,

    /// Name of the top contributor.
    pub top_owner: String,

    /// Lifecycle stage (Godfrey & Tu 2000): Active, Stable, Ephemeral, Dead, Deleted.
    pub lifecycle_stage: LifecycleStageCompact,

    /// File age in days since first creation.
    pub age_days: f64,

    /// Number of change bursts detected (Nagappan et al. 2010).
    /// High burst count indicates volatile, potentially risky code.
    pub burst_count: u32,

    /// Change burst risk score (0.0–1.0 normalized).
    pub burst_risk_score: f64,

    /// Circadian risk fraction (Eyolfson et al. 2011): proportion of
    /// commits to this file made during high-risk hours (midnight–4 AM).
    /// Range: 0.0–1.0.
    pub circadian_risk: f64,

    /// Knowledge entropy (Rigby & Bird 2013): Shannon entropy of the
    /// contributor distribution. Low entropy = knowledge silo.
    /// Range: 0.0+ (0 = single contributor, higher = more distributed).
    pub knowledge_entropy: f64,

    /// Whether this file is a knowledge silo (single/dominant contributor).
    pub is_knowledge_silo: bool,

    /// File diffusion score (Posnett et al. 2013): how many different
    /// developers touch this file, weighted by their contribution diversity.
    /// Range: 0.0–1.0 (higher = more diffuse ownership).
    pub diffusion_score: f64,

    /// Number of files this file co-changes with (coupling degree).
    /// D'Ambros et al. (2009): high coupling indicates hidden dependencies.
    pub coupling_degree: u32,

    /// Number of minor contributors (Bird et al. 2011): contributors with
    /// < 5% of total changes. High minor count correlates with post-release defects.
    pub minor_contributors: u32,

    /// Number of major contributors (Bird et al. 2011): contributors with
    /// ≥ 5% of total changes. Major contributors have enough context to produce
    /// fewer defects per change.
    pub major_contributors: u32,

    /// Per-file Gini coefficient of contributor commit distribution
    /// (Bird et al. 2011, Greiler et al. 2015). Range: 0.0–1.0.
    /// 0 = equal ownership, 1 = single owner. Mid-range = fragmented (risky).
    pub ownership_gini: f64,

    /// Composite defect prediction score (D'Ambros et al. 2010).
    /// Range: 0.0–1.0 (higher = more defect-prone).
    pub defect_score: f64,

    /// Code churn volatility CV (Nagappan & Ball 2005).
    /// Coefficient of variation of change frequency across time windows.
    /// Higher = more erratic churn pattern = more defect-prone.
    pub churn_cv: f64,

    /// Defect-introducing change pattern score (Kim et al. 2008).
    /// Proportion of large-commit appearances followed by fix-up bursts.
    /// Range: 0.0–1.0 (higher = more defect-introducing pattern).
    pub defect_pattern_score: f64,

    // ---- Strategic tab metrics (next-generation git mining insights) ----
    /// Knowledge currency index (Fritz et al. 2010, Ebbinghaus 1885):
    /// unified per-file knowledge freshness score.
    /// Range: 0.0–1.0 (0 = completely stale, 1 = fully current).
    pub knowledge_currency: f64,
}

/// Compact lifecycle stage enum for the index.
///
/// Mirrors `lifecycle::LifecycleStage` but is owned by this module to
/// avoid tight coupling and to allow future extension.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LifecycleStageCompact {
    /// Recently modified (within last 20% of time span).
    Active,
    /// Exists but rarely changes.
    Stable,
    /// Created and deleted within a short period.
    Ephemeral,
    /// No changes in a long time (dormant).
    Dead,
    /// File has been removed from the repository.
    Deleted,
}

impl Default for FileMetrics {
    fn default() -> Self {
        Self {
            hotspot_score: 0.0,
            hotspot_rank: None,
            total_changes: 0,
            contributor_count: 0,
            top_owner_share: 0.0,
            top_owner: String::new(),
            lifecycle_stage: LifecycleStageCompact::Active,
            age_days: 0.0,
            burst_count: 0,
            burst_risk_score: 0.0,
            circadian_risk: 0.0,
            knowledge_entropy: 0.0,
            is_knowledge_silo: false,
            diffusion_score: 0.0,
            coupling_degree: 0,
            minor_contributors: 0,
            major_contributors: 0,
            ownership_gini: 0.0,
            defect_score: 0.0,
            churn_cv: 0.0,
            defect_pattern_score: 0.0,
            knowledge_currency: 0.0,
        }
    }
}

// ============================================================================
// Per-User Academic Metrics
// ============================================================================

/// Aggregated academic metrics for a single developer/author.
///
/// All fields are pre-computed from the [`InsightsReport`] at load time.
/// Access during rendering is O(1) via `InsightsIndex::user_metrics()`.
#[derive(Debug, Clone)]
pub struct UserMetrics {
    /// Total number of commits by this author.
    pub commit_count: u32,

    /// Contributor classification (Mockus et al. 2002).
    pub profile_type: ProfileTypeCompact,

    /// Number of unique files this author has modified.
    pub unique_files: u32,

    /// Average files per commit (measure of commit granularity).
    pub avg_files_per_commit: f64,

    /// Active span in days (last commit - first commit).
    pub active_span_days: f64,

    /// Commit cadence type (Eyolfson et al. 2014).
    pub cadence_type: CadenceTypeCompact,

    /// Mean interval between commits (seconds).
    pub mean_commit_interval: f64,

    /// Focus score (Posnett et al. 2013): how concentrated this
    /// developer's work is across directories. Range: 0.0–1.0
    /// (1.0 = works in single directory, 0.0 = maximally spread).
    pub focus_score: f64,

    /// Network degree centrality (Meneely & Williams 2009):
    /// number of other developers this person collaborates with
    /// (shares file edits).
    pub network_degree: u32,

    /// Network betweenness centrality: how often this developer
    /// lies on shortest paths between other developers.
    /// Range: 0.0–1.0 (higher = more central).
    pub network_betweenness: f64,

    /// Circadian risk (Eyolfson et al. 2011): average risk score
    /// of this developer's commits based on time-of-day patterns.
    pub circadian_avg_risk: f64,

    /// Number of directories this developer works in.
    pub directories_touched: u32,

    /// Developer experience score (Mockus & Votta 2000):
    /// `tenure_days` × ln(1 + `total_commits`). Higher = more experienced.
    pub experience_score: f64,

    /// Tenure in days (last commit - first commit).
    pub tenure_days: f64,

    /// Total DOA (Degree of Authorship) from truck factor model (Avelino et al. 2016).
    /// Sum of DOA scores across all files where this developer is an expert.
    pub truck_factor_doa: f64,

    /// Number of files where this developer is the sole expert.
    pub sole_expert_count: u32,

    /// Whether this developer has departed (no commits in last 90 days).
    pub is_departed: bool,

    // ---- Strategic tab metrics (next-generation git mining insights) ----
    /// Team rhythm type (Fisher 1993, Eyolfson et al. 2011):
    /// commit hour regularity classification.
    pub rhythm_type: RhythmTypeCompact,

    /// Mean commit coherence score for this developer (Herzig & Zeller 2013).
    /// Range: 0.0–1.0 (higher = more atomic, focused commits).
    pub mean_coherence: f64,
}

/// Compact contributor classification.
///
/// Mirrors `profiles::ContributorType` with owned enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProfileTypeCompact {
    /// Core contributor: high commit count, broad file coverage.
    Core,
    /// Peripheral contributor: moderate activity.
    Peripheral,
    /// Drive-by contributor: very few commits.
    DriveBy,
}

/// Compact cadence classification.
///
/// Mirrors `cadence::CadenceType` with owned enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CadenceTypeCompact {
    /// Regular commit intervals (low coefficient of variation).
    Regular,
    /// Moderate variability in commit intervals.
    Moderate,
    /// Highly irregular (bursty) commit patterns.
    Bursty,
}

/// Compact rhythm type classification.
///
/// Mirrors `team_rhythm::RhythmType` with owned enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RhythmTypeCompact {
    /// Regular: concentrated commit hours (R̄ > 0.7).
    Regular,
    /// Moderate: some regularity (0.3 < R̄ ≤ 0.7).
    Moderate,
    /// Irregular: spread across many hours (R̄ ≤ 0.3).
    Irregular,
}

impl Default for UserMetrics {
    fn default() -> Self {
        Self {
            commit_count: 0,
            profile_type: ProfileTypeCompact::DriveBy,
            unique_files: 0,
            avg_files_per_commit: 0.0,
            active_span_days: 0.0,
            cadence_type: CadenceTypeCompact::Moderate,
            mean_commit_interval: 0.0,
            focus_score: 0.0,
            network_degree: 0,
            network_betweenness: 0.0,
            circadian_avg_risk: 0.0,
            directories_touched: 0,
            experience_score: 0.0,
            tenure_days: 0.0,
            truck_factor_doa: 0.0,
            sole_expert_count: 0,
            is_departed: false,
            rhythm_type: RhythmTypeCompact::Moderate,
            mean_coherence: 1.0,
        }
    }
}

// ============================================================================
// Index Summary
// ============================================================================

/// Aggregate statistics about the indexed metrics.
#[derive(Debug, Clone)]
pub struct IndexSummary {
    /// Total files in the index.
    pub total_files: usize,
    /// Total users in the index.
    pub total_users: usize,
    /// Number of files classified as knowledge silos.
    pub knowledge_silo_count: usize,
    /// Number of files with burst activity.
    pub files_with_bursts: usize,
    /// Number of core contributors.
    pub core_contributor_count: usize,
    /// Number of peripheral contributors.
    pub peripheral_contributor_count: usize,
    /// Number of drive-by contributors.
    pub drive_by_contributor_count: usize,
    /// Maximum hotspot score across all files.
    pub max_hotspot_score: f64,
    /// Average contributor count per file.
    pub avg_contributors_per_file: f64,
}

// ============================================================================
// InsightsIndex
// ============================================================================

/// O(1) lookup index for per-entity academic metrics.
///
/// Built once from [`InsightsReport`] at load time. All lookups are
/// `FxHashMap::get()` — O(1) amortized with fast hashing.
///
/// # Usage
///
/// ```ignore
/// let report = compute_insights(&commits);
/// let index = InsightsIndex::from_report(&report);
///
/// // O(1) lookup during rendering
/// if let Some(fm) = index.file_metrics("src/main.rs") {
///     let radius_scale = 1.0 + fm.hotspot_score.min(5.0) * 0.4;
///     let glow = fm.burst_risk_score;
/// }
///
/// if let Some(um) = index.user_metrics("Alice") {
///     let size_scale = 1.0 + (um.commit_count as f64).log2() * 0.2;
/// }
/// ```
#[derive(Debug)]
pub struct InsightsIndex {
    /// Per-file metrics keyed by file path.
    files: FxHashMap<String, FileMetrics>,

    /// Per-user metrics keyed by author name.
    users: FxHashMap<String, UserMetrics>,

    /// Aggregate summary statistics.
    summary: IndexSummary,
}

impl InsightsIndex {
    /// Builds the index from a complete insights report.
    ///
    /// # Complexity
    ///
    /// O(F + U + C) where F = total files across all metrics,
    /// U = total users across all metrics, C = coupling pairs.
    ///
    /// # Arguments
    ///
    /// * `report` - A complete [`InsightsReport`] from `compute_insights()`
    #[must_use]
    #[allow(clippy::too_many_lines)]
    pub fn from_report(report: &InsightsReport) -> Self {
        let mut files: FxHashMap<String, FileMetrics> = FxHashMap::default();
        let mut users: FxHashMap<String, UserMetrics> = FxHashMap::default();

        // ---- Phase 1: Populate file metrics from each insight section ----

        // Hotspots (Nagappan & Ball 2005)
        for (rank, h) in report.hotspots.iter().enumerate() {
            let fm = files.entry(h.path.clone()).or_default();
            fm.hotspot_score = h.score;
            fm.hotspot_rank = Some(rank as u32);
            fm.total_changes = h.total_changes;
        }

        // Ownership (Bird et al. 2011)
        for o in &report.ownership {
            let fm = files.entry(o.path.clone()).or_default();
            fm.contributor_count = o.contributor_count as u32;
            fm.top_owner_share = o.top_owner_share;
            o.top_owner.clone_into(&mut fm.top_owner);
            // total_changes: prefer ownership data if hotspot didn't set it
            if fm.total_changes == 0 {
                fm.total_changes = o.total_changes;
            }
            // Bird et al. (2011) minor/major classification: 5% threshold
            let mut minor = 0u32;
            let mut major = 0u32;
            for c in &o.contributors {
                if c.share < 0.05 {
                    minor += 1;
                } else {
                    major += 1;
                }
            }
            fm.minor_contributors = minor;
            fm.major_contributors = major;
        }

        // Lifecycle (Godfrey & Tu 2000)
        for l in &report.lifecycle.files {
            let fm = files.entry(l.path.clone()).or_default();
            fm.lifecycle_stage = convert_lifecycle_stage(l.stage);
            fm.age_days = l.age_days;
        }

        // Change bursts (Nagappan et al. 2010)
        for b in &report.change_bursts.files {
            let fm = files.entry(b.path.clone()).or_default();
            fm.burst_count = b.burst_count;
            fm.burst_risk_score = b.risk_score;
        }

        // Circadian risk (Eyolfson et al. 2011)
        for c in &report.circadian.files {
            let fm = files.entry(c.path.clone()).or_default();
            fm.circadian_risk = c.high_risk_fraction;
        }

        // Knowledge entropy (Rigby & Bird 2013)
        for k in &report.knowledge.files {
            let fm = files.entry(k.path.clone()).or_default();
            fm.knowledge_entropy = k.knowledge_entropy;
            fm.is_knowledge_silo = k.is_silo;
        }

        // File diffusion (Posnett et al. 2013)
        for f in &report.focus.files {
            let fm = files.entry(f.path.clone()).or_default();
            fm.diffusion_score = f.diffusion_score;
        }

        // Coupling degree (D'Ambros et al. 2009)
        // Count how many coupling pairs each file participates in
        for cp in &report.couplings {
            files.entry(cp.file_a.clone()).or_default().coupling_degree += 1;
            files.entry(cp.file_b.clone()).or_default().coupling_degree += 1;
        }

        // Ownership fragmentation / Gini (Bird et al. 2011)
        for of in &report.ownership_fragmentation.files {
            let fm = files.entry(of.path.clone()).or_default();
            fm.ownership_gini = of.gini_coefficient;
        }

        // Churn volatility (Nagappan & Ball 2005)
        for cv in &report.churn_volatility.files {
            let fm = files.entry(cv.path.clone()).or_default();
            fm.churn_cv = cv.cv;
        }

        // Defect-introducing change patterns (Kim et al. 2008)
        for dp in &report.defect_patterns.files {
            let fm = files.entry(dp.path.clone()).or_default();
            fm.defect_pattern_score = dp.score;
        }

        // Knowledge currency (Fritz et al. 2010, Ebbinghaus 1885)
        for kc in &report.knowledge_currency.files {
            let fm = files.entry(kc.path.clone()).or_default();
            fm.knowledge_currency = kc.currency;
        }

        // Defect prediction scores (D'Ambros et al. 2010)
        // Compute from the file metrics we've accumulated so far
        {
            let raw: Vec<super::defect_prediction::RawPredictors> = files
                .iter()
                .map(|(path, fm)| super::defect_prediction::RawPredictors {
                    path: path.clone(),
                    total_changes: fm.total_changes,
                    age_days: fm.age_days,
                    contributor_count: fm.contributor_count,
                    knowledge_entropy: fm.knowledge_entropy,
                    coupling_degree: fm.coupling_degree,
                    burst_risk: fm.burst_risk_score,
                })
                .collect();
            let dp_report = super::defect_prediction::compute_defect_predictions(&raw);
            for dp in &dp_report.files {
                if let Some(fm) = files.get_mut(&dp.path) {
                    fm.defect_score = dp.defect_score;
                }
            }
        }

        // ---- Phase 2: Populate user metrics from each insight section ----

        // Developer profiles (Mockus et al. 2002)
        for p in &report.profiles.developers {
            let um = users.entry(p.author.clone()).or_default();
            um.commit_count = p.commit_count as u32;
            um.profile_type = convert_profile_type(p.classification);
            um.unique_files = p.unique_files as u32;
            um.avg_files_per_commit = p.avg_files_per_commit;
            um.active_span_days = p.active_span_days;
        }

        // Commit cadence (Eyolfson et al. 2014)
        for c in &report.cadence.authors {
            let um = users.entry(c.author.clone()).or_default();
            um.cadence_type = convert_cadence_type(c.cadence_type);
            um.mean_commit_interval = c.mean_interval;
        }

        // Developer focus (Posnett et al. 2013)
        for f in &report.focus.developers {
            let um = users.entry(f.author.clone()).or_default();
            um.focus_score = f.focus_score;
            um.directories_touched = f.directories_touched;
        }

        // Network centrality (Meneely & Williams 2009)
        for n in &report.network.developers {
            let um = users.entry(n.author.clone()).or_default();
            um.network_degree = n.degree;
            um.network_betweenness = n.betweenness;
        }

        // Circadian risk per author (Eyolfson et al. 2011)
        for a in &report.circadian.authors {
            let um = users.entry(a.author.clone()).or_default();
            um.circadian_avg_risk = a.avg_risk;
        }

        // Developer experience (Mockus & Votta 2000)
        for de in &report.developer_experience.developers {
            let um = users.entry(de.author.clone()).or_default();
            um.experience_score = de.experience_score;
            um.tenure_days = de.tenure_days;
        }

        // Truck factor DOA (Avelino et al. 2016)
        for dev in &report.truck_factor.ranked_developers {
            let um = users.entry(dev.name.clone()).or_default();
            um.truck_factor_doa = dev.total_doa;
            um.sole_expert_count = dev.sole_expert_count;
        }

        // Turnover impact (Mockus 2009)
        for dep in &report.turnover_impact.departed_developers {
            let um = users.entry(dep.name.clone()).or_default();
            um.is_departed = true;
        }

        // Team rhythm (Fisher 1993, Eyolfson et al. 2011)
        for dev in &report.team_rhythm.developers {
            let um = users.entry(dev.author.clone()).or_default();
            um.rhythm_type = convert_rhythm_type(dev.rhythm_type);
        }

        // Commit coherence per developer (Herzig & Zeller 2013)
        for dc in &report.commit_coherence_score.developer_coherence {
            let um = users.entry(dc.author.clone()).or_default();
            um.mean_coherence = dc.mean_coherence;
        }

        // ---- Phase 3: Compute summary statistics ----
        let knowledge_silo_count = files.values().filter(|f| f.is_knowledge_silo).count();
        let files_with_bursts = files.values().filter(|f| f.burst_count > 0).count();
        let core_count = users
            .values()
            .filter(|u| u.profile_type == ProfileTypeCompact::Core)
            .count();
        let peripheral_count = users
            .values()
            .filter(|u| u.profile_type == ProfileTypeCompact::Peripheral)
            .count();
        let drive_by_count = users
            .values()
            .filter(|u| u.profile_type == ProfileTypeCompact::DriveBy)
            .count();
        let max_hotspot = files
            .values()
            .map(|f| f.hotspot_score)
            .fold(0.0_f64, f64::max);
        let total_contributors: u64 = files.values().map(|f| u64::from(f.contributor_count)).sum();
        let avg_contributors = if files.is_empty() {
            0.0
        } else {
            total_contributors as f64 / files.len() as f64
        };

        let summary = IndexSummary {
            total_files: files.len(),
            total_users: users.len(),
            knowledge_silo_count,
            files_with_bursts,
            core_contributor_count: core_count,
            peripheral_contributor_count: peripheral_count,
            drive_by_contributor_count: drive_by_count,
            max_hotspot_score: max_hotspot,
            avg_contributors_per_file: avg_contributors,
        };

        Self {
            files,
            users,
            summary,
        }
    }

    /// Looks up metrics for a file by path.
    ///
    /// Returns `None` if the file was not seen in any commit.
    ///
    /// # Complexity
    ///
    /// O(1) amortized (`FxHashMap` lookup).
    #[inline]
    #[must_use]
    pub fn file_metrics(&self, path: &str) -> Option<&FileMetrics> {
        self.files.get(path)
    }

    /// Looks up metrics for a user by author name.
    ///
    /// Returns `None` if the author was not seen in any commit.
    ///
    /// # Complexity
    ///
    /// O(1) amortized (`FxHashMap` lookup).
    #[inline]
    #[must_use]
    pub fn user_metrics(&self, author: &str) -> Option<&UserMetrics> {
        self.users.get(author)
    }

    /// Returns aggregate summary statistics for the index.
    #[inline]
    #[must_use]
    pub fn summary(&self) -> &IndexSummary {
        &self.summary
    }

    /// Returns the number of files in the index.
    #[inline]
    #[must_use]
    pub fn file_count(&self) -> usize {
        self.files.len()
    }

    /// Returns the number of users in the index.
    #[inline]
    #[must_use]
    pub fn user_count(&self) -> usize {
        self.users.len()
    }

    /// Returns an iterator over all file paths and their metrics.
    pub fn iter_files(&self) -> impl Iterator<Item = (&str, &FileMetrics)> {
        self.files.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Returns an iterator over all user names and their metrics.
    pub fn iter_users(&self) -> impl Iterator<Item = (&str, &UserMetrics)> {
        self.users.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Returns true if the index contains no files and no users.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.files.is_empty() && self.users.is_empty()
    }
}

// ============================================================================
// Conversion helpers
// ============================================================================

/// Converts the lifecycle module's stage enum to our compact representation.
fn convert_lifecycle_stage(stage: super::lifecycle::LifecycleStage) -> LifecycleStageCompact {
    match stage {
        super::lifecycle::LifecycleStage::Active => LifecycleStageCompact::Active,
        super::lifecycle::LifecycleStage::Stable => LifecycleStageCompact::Stable,
        super::lifecycle::LifecycleStage::Ephemeral => LifecycleStageCompact::Ephemeral,
        super::lifecycle::LifecycleStage::Dead => LifecycleStageCompact::Dead,
        super::lifecycle::LifecycleStage::Deleted => LifecycleStageCompact::Deleted,
    }
}

/// Converts the profiles module's contributor type to our compact representation.
fn convert_profile_type(ct: super::profiles::ContributorType) -> ProfileTypeCompact {
    match ct {
        super::profiles::ContributorType::Core => ProfileTypeCompact::Core,
        super::profiles::ContributorType::Peripheral => ProfileTypeCompact::Peripheral,
        super::profiles::ContributorType::DriveBy => ProfileTypeCompact::DriveBy,
    }
}

/// Converts the `team_rhythm` module's rhythm type to our compact representation.
fn convert_rhythm_type(rt: super::team_rhythm::RhythmType) -> RhythmTypeCompact {
    match rt {
        super::team_rhythm::RhythmType::Regular => RhythmTypeCompact::Regular,
        super::team_rhythm::RhythmType::Moderate => RhythmTypeCompact::Moderate,
        super::team_rhythm::RhythmType::Irregular => RhythmTypeCompact::Irregular,
    }
}

/// Converts the cadence module's cadence type to our compact representation.
fn convert_cadence_type(ct: super::cadence::CadenceType) -> CadenceTypeCompact {
    match ct {
        super::cadence::CadenceType::Regular => CadenceTypeCompact::Regular,
        super::cadence::CadenceType::Moderate => CadenceTypeCompact::Moderate,
        super::cadence::CadenceType::Bursty => CadenceTypeCompact::Bursty,
    }
}

// ============================================================================
// Display implementations
// ============================================================================

impl std::fmt::Display for LifecycleStageCompact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Active => write!(f, "active"),
            Self::Stable => write!(f, "stable"),
            Self::Ephemeral => write!(f, "ephemeral"),
            Self::Dead => write!(f, "dead"),
            Self::Deleted => write!(f, "deleted"),
        }
    }
}

impl std::fmt::Display for ProfileTypeCompact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Core => write!(f, "core"),
            Self::Peripheral => write!(f, "peripheral"),
            Self::DriveBy => write!(f, "drive-by"),
        }
    }
}

impl std::fmt::Display for RhythmTypeCompact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Regular => write!(f, "regular"),
            Self::Moderate => write!(f, "moderate"),
            Self::Irregular => write!(f, "irregular"),
        }
    }
}

impl std::fmt::Display for CadenceTypeCompact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Regular => write!(f, "regular"),
            Self::Moderate => write!(f, "moderate"),
            Self::Bursty => write!(f, "bursty"),
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::insights::{compute_insights, CommitRecord, FileActionKind, FileRecord};

    fn make_commit(ts: i64, author: &str, files: &[(&str, FileActionKind)]) -> CommitRecord {
        CommitRecord {
            timestamp: ts,
            author: author.to_string(),
            message: None,
            files: files
                .iter()
                .map(|(p, a)| FileRecord {
                    path: p.to_string(),
                    action: *a,
                })
                .collect(),
        }
    }

    // ---- Empty input ----

    #[test]
    fn test_empty_report_produces_empty_index() {
        let report = compute_insights(&[]);
        let index = InsightsIndex::from_report(&report);
        assert!(index.is_empty());
        assert_eq!(index.file_count(), 0);
        assert_eq!(index.user_count(), 0);
        assert_eq!(index.summary().total_files, 0);
        assert_eq!(index.summary().total_users, 0);
        assert!((index.summary().max_hotspot_score - 0.0).abs() < f64::EPSILON);
        assert!((index.summary().avg_contributors_per_file - 0.0).abs() < f64::EPSILON);
    }

    // ---- Single commit, single file ----

    #[test]
    fn test_single_commit_file_metrics() {
        let commits = vec![make_commit(
            1000,
            "Alice",
            &[("src/main.rs", FileActionKind::Create)],
        )];
        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);

        assert_eq!(index.file_count(), 1);
        assert_eq!(index.user_count(), 1);
        assert!(!index.is_empty());

        let fm = index
            .file_metrics("src/main.rs")
            .expect("file should exist");
        assert_eq!(fm.contributor_count, 1);
        assert!((fm.top_owner_share - 1.0).abs() < f64::EPSILON);
        assert_eq!(fm.top_owner, "Alice");
        assert!(fm.is_knowledge_silo);
    }

    #[test]
    fn test_single_commit_user_metrics() {
        let commits = vec![make_commit(
            1000,
            "Alice",
            &[("src/main.rs", FileActionKind::Create)],
        )];
        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);

        let um = index.user_metrics("Alice").expect("user should exist");
        assert!(um.commit_count >= 1);
        assert!(um.unique_files >= 1);
    }

    // ---- Nonexistent lookups ----

    #[test]
    fn test_nonexistent_file_returns_none() {
        let commits = vec![make_commit(
            1000,
            "Alice",
            &[("src/main.rs", FileActionKind::Create)],
        )];
        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);

        assert!(index.file_metrics("nonexistent.rs").is_none());
        assert!(index.user_metrics("Bob").is_none());
    }

    // ---- Hotspot ranking ----

    #[test]
    fn test_hotspot_ranking_order() {
        // File A modified 5 times, file B once — A should rank 0
        let commits = vec![
            make_commit(1000, "Alice", &[("a.rs", FileActionKind::Modify)]),
            make_commit(2000, "Alice", &[("a.rs", FileActionKind::Modify)]),
            make_commit(3000, "Alice", &[("a.rs", FileActionKind::Modify)]),
            make_commit(4000, "Alice", &[("a.rs", FileActionKind::Modify)]),
            make_commit(5000, "Alice", &[("a.rs", FileActionKind::Modify)]),
            make_commit(6000, "Bob", &[("b.rs", FileActionKind::Modify)]),
        ];
        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);

        let a = index.file_metrics("a.rs").expect("a.rs should exist");
        let b = index.file_metrics("b.rs").expect("b.rs should exist");

        // a.rs should rank higher (lower rank number)
        assert_eq!(a.hotspot_rank, Some(0));
        assert!(a.hotspot_score > b.hotspot_score);
        assert_eq!(a.total_changes, 5);
        assert_eq!(b.total_changes, 1);
    }

    // ---- Ownership metrics ----

    #[test]
    fn test_multi_owner_file() {
        let commits = vec![
            make_commit(1000, "Alice", &[("x.rs", FileActionKind::Create)]),
            make_commit(2000, "Alice", &[("x.rs", FileActionKind::Modify)]),
            make_commit(3000, "Bob", &[("x.rs", FileActionKind::Modify)]),
        ];
        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);

        let fm = index.file_metrics("x.rs").expect("file should exist");
        assert_eq!(fm.contributor_count, 2);
        // Alice has 2/3 ≈ 0.667
        assert!((fm.top_owner_share - 2.0 / 3.0).abs() < 0.01);
        assert_eq!(fm.top_owner, "Alice");
        assert!(!fm.is_knowledge_silo); // 2 contributors → not a silo
    }

    // ---- Coupling degree ----

    #[test]
    fn test_coupling_degree_counts() {
        // A and B always change together → each gets coupling_degree 1
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
        let index = InsightsIndex::from_report(&report);

        let a = index.file_metrics("a.rs").expect("a.rs");
        let b = index.file_metrics("b.rs").expect("b.rs");
        // Both should have coupling_degree >= 1 (they co-change)
        assert!(
            a.coupling_degree >= 1,
            "a.rs coupling_degree={}",
            a.coupling_degree
        );
        assert!(
            b.coupling_degree >= 1,
            "b.rs coupling_degree={}",
            b.coupling_degree
        );
    }

    // ---- User profiles ----

    #[test]
    fn test_user_profile_types() {
        // Create a scenario with core + drive-by contributors
        let mut commits = Vec::new();
        let base_ts: i64 = 1_700_000_000;
        // Alice: 20 commits over 20 days → core
        for i in 0..20 {
            commits.push(make_commit(
                base_ts + i * 86400,
                "Alice",
                &[(&format!("src/mod{}.rs", i % 5), FileActionKind::Modify)],
            ));
        }
        // Bob: 1 commit → drive-by
        commits.push(make_commit(
            base_ts + 21 * 86400,
            "Bob",
            &[("readme.md", FileActionKind::Create)],
        ));

        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);

        let alice = index.user_metrics("Alice").expect("Alice should exist");
        let bob = index.user_metrics("Bob").expect("Bob should exist");

        assert_eq!(alice.commit_count, 20);
        assert_eq!(bob.commit_count, 1);
        // Alice should be Core, Bob should be DriveBy
        assert_eq!(alice.profile_type, ProfileTypeCompact::Core);
        assert_eq!(bob.profile_type, ProfileTypeCompact::DriveBy);
    }

    // ---- Summary statistics ----

    #[test]
    fn test_summary_statistics() {
        let commits = vec![
            make_commit(
                1000,
                "Alice",
                &[
                    ("a.rs", FileActionKind::Create),
                    ("b.rs", FileActionKind::Create),
                ],
            ),
            make_commit(2000, "Bob", &[("a.rs", FileActionKind::Modify)]),
            make_commit(3000, "Carol", &[("c.rs", FileActionKind::Create)]),
        ];
        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);

        let s = index.summary();
        assert!(s.total_files >= 3);
        assert!(s.total_users >= 3);
        assert!(s.max_hotspot_score > 0.0);
        assert!(s.avg_contributors_per_file > 0.0);
    }

    // ---- Mutation-killing: arithmetic operator tests ----

    #[test]
    fn test_coupling_degree_increments_both_files() {
        // Coupling pairs increment BOTH file_a and file_b's coupling_degree.
        // A mutant that only increments file_a (or only file_b) would fail.
        let commits = vec![
            make_commit(
                1000,
                "Alice",
                &[
                    ("x.rs", FileActionKind::Modify),
                    ("y.rs", FileActionKind::Modify),
                    ("z.rs", FileActionKind::Modify),
                ],
            ),
            make_commit(
                2000,
                "Alice",
                &[
                    ("x.rs", FileActionKind::Modify),
                    ("y.rs", FileActionKind::Modify),
                    ("z.rs", FileActionKind::Modify),
                ],
            ),
        ];
        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);

        // All three files co-change → each should have coupling_degree >= 2
        // (x↔y, x↔z, y↔z = 3 pairs, so each file appears in 2 pairs)
        let x = index.file_metrics("x.rs").expect("x.rs");
        let y = index.file_metrics("y.rs").expect("y.rs");
        let z = index.file_metrics("z.rs").expect("z.rs");

        // Each file should participate in at least 2 coupling pairs
        assert!(
            x.coupling_degree >= 2,
            "x coupling_degree={}",
            x.coupling_degree
        );
        assert!(
            y.coupling_degree >= 2,
            "y coupling_degree={}",
            y.coupling_degree
        );
        assert!(
            z.coupling_degree >= 2,
            "z coupling_degree={}",
            z.coupling_degree
        );
    }

    #[test]
    fn test_avg_contributors_division_not_multiplication() {
        // avg_contributors_per_file = sum / count, NOT sum * count
        // With 2 files each having 1 contributor: avg = 2/2 = 1.0
        // If mutated to *: avg = 2*2 = 4.0 → caught
        let commits = vec![
            make_commit(1000, "Alice", &[("a.rs", FileActionKind::Create)]),
            make_commit(2000, "Bob", &[("b.rs", FileActionKind::Create)]),
        ];
        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);

        let avg = index.summary().avg_contributors_per_file;
        assert!(
            (avg - 1.0).abs() < f64::EPSILON,
            "avg_contributors_per_file={avg}, expected 1.0"
        );
        // If / were *: 2 * 2 = 4.0 → fails
        assert!(avg < 2.0);
    }

    // ---- Determinism ----

    #[test]
    fn test_index_deterministic() {
        let commits = vec![
            make_commit(
                1000,
                "Alice",
                &[
                    ("a.rs", FileActionKind::Create),
                    ("b.rs", FileActionKind::Create),
                ],
            ),
            make_commit(
                2000,
                "Bob",
                &[
                    ("a.rs", FileActionKind::Modify),
                    ("c.rs", FileActionKind::Create),
                ],
            ),
        ];
        let report = compute_insights(&commits);
        let idx1 = InsightsIndex::from_report(&report);
        let idx2 = InsightsIndex::from_report(&report);

        assert_eq!(idx1.file_count(), idx2.file_count());
        assert_eq!(idx1.user_count(), idx2.user_count());

        // File metrics must be identical
        for (path, fm1) in idx1.iter_files() {
            let fm2 = idx2.file_metrics(path).expect("should exist in both");
            assert!(
                (fm1.hotspot_score - fm2.hotspot_score).abs() < 1e-10,
                "hotspot_score mismatch for {path}"
            );
            assert_eq!(fm1.contributor_count, fm2.contributor_count);
            assert_eq!(fm1.coupling_degree, fm2.coupling_degree);
        }
    }

    // ---- Iterator tests ----

    #[test]
    fn test_iter_files_covers_all() {
        let commits = vec![
            make_commit(1000, "Alice", &[("a.rs", FileActionKind::Create)]),
            make_commit(2000, "Bob", &[("b.rs", FileActionKind::Create)]),
        ];
        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);

        let paths: Vec<&str> = index.iter_files().map(|(p, _)| p).collect();
        assert!(paths.contains(&"a.rs"));
        assert!(paths.contains(&"b.rs"));
    }

    #[test]
    fn test_iter_users_covers_all() {
        let commits = vec![
            make_commit(1000, "Alice", &[("a.rs", FileActionKind::Create)]),
            make_commit(2000, "Bob", &[("b.rs", FileActionKind::Create)]),
        ];
        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);

        let authors: Vec<&str> = index.iter_users().map(|(a, _)| a).collect();
        assert!(authors.contains(&"Alice"));
        assert!(authors.contains(&"Bob"));
    }

    // ---- Display implementations ----

    #[test]
    fn test_lifecycle_stage_display() {
        assert_eq!(format!("{}", LifecycleStageCompact::Active), "active");
        assert_eq!(format!("{}", LifecycleStageCompact::Stable), "stable");
        assert_eq!(format!("{}", LifecycleStageCompact::Ephemeral), "ephemeral");
        assert_eq!(format!("{}", LifecycleStageCompact::Dead), "dead");
        assert_eq!(format!("{}", LifecycleStageCompact::Deleted), "deleted");
    }

    #[test]
    fn test_profile_type_display() {
        assert_eq!(format!("{}", ProfileTypeCompact::Core), "core");
        assert_eq!(format!("{}", ProfileTypeCompact::Peripheral), "peripheral");
        assert_eq!(format!("{}", ProfileTypeCompact::DriveBy), "drive-by");
    }

    #[test]
    fn test_cadence_type_display() {
        assert_eq!(format!("{}", CadenceTypeCompact::Regular), "regular");
        assert_eq!(format!("{}", CadenceTypeCompact::Moderate), "moderate");
        assert_eq!(format!("{}", CadenceTypeCompact::Bursty), "bursty");
    }

    // ---- Bird et al. (2011) minor/major classification ----

    #[test]
    fn test_minor_major_classification() {
        // 20 commits from Alice (major), 1 commit from each of Bob, Carol, Dave (minor at <5%)
        // Total = 23 commits. Alice = 20/23 ≈ 87% (major), others = 1/23 ≈ 4.3% (minor)
        let mut commits = Vec::new();
        let base_ts: i64 = 1_700_000_000;
        for i in 0..20 {
            commits.push(make_commit(
                base_ts + i * 86400,
                "Alice",
                &[("src/core.rs", FileActionKind::Modify)],
            ));
        }
        for (i, author) in ["Bob", "Carol", "Dave"].iter().enumerate() {
            commits.push(make_commit(
                base_ts + (20 + i64::try_from(i).unwrap()) * 86400,
                author,
                &[("src/core.rs", FileActionKind::Modify)],
            ));
        }

        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);
        let fm = index.file_metrics("src/core.rs").unwrap();

        assert_eq!(fm.contributor_count, 4);
        // Alice ≈ 87% → major, Bob/Carol/Dave ≈ 4.3% each → minor
        assert_eq!(fm.major_contributors, 1, "only Alice is major (≥5%)");
        assert_eq!(fm.minor_contributors, 3, "Bob, Carol, Dave are minor (<5%)");
    }

    #[test]
    fn test_minor_major_boundary() {
        // Test exact 5% boundary: 1/20 = 5% → major (≥ 5%), not minor
        let mut commits = Vec::new();
        let base_ts: i64 = 1_700_000_000;
        for i in 0..19 {
            commits.push(make_commit(
                base_ts + i * 86400,
                "Alice",
                &[("src/lib.rs", FileActionKind::Modify)],
            ));
        }
        commits.push(make_commit(
            base_ts + 19 * 86400,
            "Bob",
            &[("src/lib.rs", FileActionKind::Modify)],
        ));

        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);
        let fm = index.file_metrics("src/lib.rs").unwrap();

        assert_eq!(fm.contributor_count, 2);
        // Alice = 19/20 = 95% → major, Bob = 1/20 = 5% → major (≥ 5%)
        assert_eq!(fm.major_contributors, 2, "both ≥ 5%");
        assert_eq!(fm.minor_contributors, 0, "none < 5%");
    }

    #[test]
    fn test_minor_major_single_owner() {
        // Single owner file: 1 major, 0 minor
        let commits = vec![
            make_commit(
                1_700_000_000,
                "Alice",
                &[("README.md", FileActionKind::Create)],
            ),
            make_commit(
                1_700_086_400,
                "Alice",
                &[("README.md", FileActionKind::Modify)],
            ),
        ];

        let report = compute_insights(&commits);
        let index = InsightsIndex::from_report(&report);
        let fm = index.file_metrics("README.md").unwrap();

        assert_eq!(fm.major_contributors, 1);
        assert_eq!(fm.minor_contributors, 0);
    }

    // ---- Scale test ----

    #[test]
    fn test_100_commit_realistic_scenario() {
        let mut commits = Vec::new();
        let authors = ["Alice", "Bob", "Carol", "Dave"];
        let base_ts: i64 = 1_700_000_000;

        for i in 0..100_i64 {
            let author = authors[i as usize % 4];
            let ts = base_ts + i * 86400;
            let file_count = (i % 5) + 1;
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
        let index = InsightsIndex::from_report(&report);

        // Verify all sections populated
        assert!(index.file_count() > 0);
        assert_eq!(index.user_count(), 4);
        assert!(!index.is_empty());

        // Verify file metrics are populated
        for (path, fm) in index.iter_files() {
            assert!(fm.contributor_count > 0, "{path} has 0 contributors");
        }

        // Verify user metrics are populated
        for (author, um) in index.iter_users() {
            assert!(um.commit_count > 0, "{author} has 0 commits");
        }

        // Summary checks
        let s = index.summary();
        assert_eq!(s.total_users, 4);
        assert!(s.total_files > 0);
        assert!(s.max_hotspot_score > 0.0);
    }
}
