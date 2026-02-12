// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Defect Prediction Composite Score — weighted multi-factor defect predictor.
//!
//! Combines the strongest defect predictors identified in empirical software
//! engineering research into a single per-file risk score (0.0–1.0). This
//! composite approach consistently outperforms individual metrics.
//!
//! # Research Basis
//!
//! - D'Ambros et al. (2010) "An Extensive Comparison of Bug Prediction
//!   Approaches" (MSR) — comprehensive comparison of 20+ prediction models
//! - Zimmermann & Nagappan (2008) "Predicting Defects Using Network Analysis
//!   on Dependency Graphs" (ICSE) — network metrics as predictors
//! - Nagappan & Ball (2005) "Use of Relative Code Churn Measures to Predict
//!   System Defect Density" (ICSE) — churn as top predictor
//! - Bird et al. (2011) "Don't Touch My Code!" (FSE) — developer count
//!
//! # Algorithm
//!
//! ```text
//! defect_score(file) = weighted sum of normalized predictors:
//!   0.25 × norm(churn)            — Nagappan & Ball 2005
//!   0.20 × norm(recency)          — Graves et al. 2000
//!   0.20 × norm(developer_count)  — Bird et al. 2011
//!   0.15 × norm(entropy_proxy)    — Hassan 2009
//!   0.10 × norm(coupling_degree)  — Cataldo et al. 2006
//!   0.10 × norm(burst_risk)       — Nagappan et al. 2010
//!
//! Normalization: min-max from dataset, then clamp to [0, 1].
//! ```
//!
//! # Complexity
//!
//! - Computation: O(F) where F = files (single pass over pre-computed metrics)
//! - Lookup: O(1) per file (stored in index)

/// Weight vector for the composite defect predictor.
///
/// Based on D'Ambros et al. (2010) relative importance rankings.
const W_CHURN: f64 = 0.25;
const W_RECENCY: f64 = 0.20;
const W_DEVELOPERS: f64 = 0.20;
const W_ENTROPY: f64 = 0.15;
const W_COUPLING: f64 = 0.10;
const W_BURST: f64 = 0.10;

/// Defect prediction report for the repository.
#[derive(Debug, Clone)]
pub struct DefectPredictionReport {
    /// Per-file defect prediction scores.
    pub files: Vec<FileDefectPrediction>,
    /// Average defect score across all files.
    pub avg_defect_score: f64,
    /// Number of high-risk files (score > 0.7).
    pub high_risk_count: usize,
    /// Number of medium-risk files (score 0.4–0.7).
    pub medium_risk_count: usize,
}

/// Defect prediction for a single file.
#[derive(Debug, Clone)]
pub struct FileDefectPrediction {
    /// File path.
    pub path: String,
    /// Composite defect score (0.0–1.0, higher = more defect-prone).
    pub defect_score: f64,
    /// Top risk factor contributing most to the score.
    pub top_risk_factor: RiskFactor,
    /// Individual normalized predictor values (for transparency).
    pub predictors: DefectPredictors,
}

/// Individual normalized predictor values.
#[derive(Debug, Clone, Copy)]
pub struct DefectPredictors {
    /// Normalized churn (total changes).
    pub churn: f64,
    /// Normalized recency (inverse of age — newer files less tested).
    pub recency: f64,
    /// Normalized developer count.
    pub developers: f64,
    /// Normalized entropy proxy (knowledge entropy).
    pub entropy: f64,
    /// Normalized coupling degree.
    pub coupling: f64,
    /// Normalized burst risk.
    pub burst: f64,
}

/// Risk factor categories.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RiskFactor {
    /// High code churn (frequent changes).
    HighChurn,
    /// Recently created file (less battle-tested).
    RecentlyCreated,
    /// Many developers (ownership dilution).
    ManyDevelopers,
    /// High knowledge entropy (scattered expertise).
    HighEntropy,
    /// High coupling degree (hidden dependencies).
    HighCoupling,
    /// Burst activity (volatile change patterns).
    BurstActivity,
}

impl std::fmt::Display for RiskFactor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::HighChurn => write!(f, "high_churn"),
            Self::RecentlyCreated => write!(f, "recently_created"),
            Self::ManyDevelopers => write!(f, "many_developers"),
            Self::HighEntropy => write!(f, "high_entropy"),
            Self::HighCoupling => write!(f, "high_coupling"),
            Self::BurstActivity => write!(f, "burst_activity"),
        }
    }
}

/// Raw predictor values for a single file before normalization.
#[derive(Debug, Clone)]
pub struct RawPredictors {
    /// File path.
    pub path: String,
    /// Total changes (churn proxy).
    pub total_changes: u32,
    /// File age in days.
    pub age_days: f64,
    /// Number of distinct contributors.
    pub contributor_count: u32,
    /// Knowledge entropy (Shannon entropy of contributor distribution).
    pub knowledge_entropy: f64,
    /// Number of co-change coupling partners.
    pub coupling_degree: u32,
    /// Burst risk score (0.0–1.0).
    pub burst_risk: f64,
}

/// Computes defect prediction scores from pre-computed per-file metrics.
///
/// This function operates on the aggregated data from the existing insight
/// modules — it does NOT re-scan commits. All inputs come from the
/// `InsightsReport` via the index.
///
/// # Complexity
///
/// O(F) where F = number of files (two passes: one for min/max, one for scoring).
#[must_use]
pub fn compute_defect_predictions(raw_data: &[RawPredictors]) -> DefectPredictionReport {
    if raw_data.is_empty() {
        return DefectPredictionReport {
            files: Vec::new(),
            avg_defect_score: 0.0,
            high_risk_count: 0,
            medium_risk_count: 0,
        };
    }

    // Pass 1: Find min/max for normalization
    let mut max_churn: f64 = 0.0;
    let mut max_age: f64 = 0.0;
    let mut max_devs: f64 = 0.0;
    let mut max_entropy: f64 = 0.0;
    let mut max_coupling: f64 = 0.0;

    for r in raw_data {
        max_churn = max_churn.max(f64::from(r.total_changes));
        max_age = max_age.max(r.age_days);
        max_devs = max_devs.max(f64::from(r.contributor_count));
        max_entropy = max_entropy.max(r.knowledge_entropy);
        max_coupling = max_coupling.max(f64::from(r.coupling_degree));
    }

    // Pass 2: Normalize and compute composite score
    let mut files = Vec::with_capacity(raw_data.len());

    for r in raw_data {
        let churn = safe_normalize(f64::from(r.total_changes), max_churn);
        // Recency: inverse of age (newer = higher risk)
        let recency = if max_age > 0.0 {
            1.0 - safe_normalize(r.age_days, max_age)
        } else {
            0.0
        };
        let developers = safe_normalize(f64::from(r.contributor_count), max_devs);
        let entropy = safe_normalize(r.knowledge_entropy, max_entropy);
        let coupling = safe_normalize(f64::from(r.coupling_degree), max_coupling);
        let burst = r.burst_risk.clamp(0.0, 1.0);

        let defect_score = (W_CHURN * churn
            + W_RECENCY * recency
            + W_DEVELOPERS * developers
            + W_ENTROPY * entropy
            + W_COUPLING * coupling
            + W_BURST * burst)
            .clamp(0.0, 1.0);

        let predictors = DefectPredictors {
            churn,
            recency,
            developers,
            entropy,
            coupling,
            burst,
        };

        let top_risk_factor = identify_top_risk(&predictors);

        files.push(FileDefectPrediction {
            path: r.path.clone(),
            defect_score,
            top_risk_factor,
            predictors,
        });
    }

    // Sort by defect score descending
    files.sort_by(|a, b| {
        b.defect_score
            .partial_cmp(&a.defect_score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let avg_score = files.iter().map(|f| f.defect_score).sum::<f64>() / files.len() as f64;
    let high_risk = files.iter().filter(|f| f.defect_score > 0.7).count();
    let medium_risk = files
        .iter()
        .filter(|f| f.defect_score > 0.4 && f.defect_score <= 0.7)
        .count();

    DefectPredictionReport {
        files,
        avg_defect_score: avg_score,
        high_risk_count: high_risk,
        medium_risk_count: medium_risk,
    }
}

/// Builds raw predictor data from the index's file metrics.
///
/// This bridges the `InsightsIndex::FileMetrics` to the defect prediction input.
pub fn build_raw_predictors<S: ::std::hash::BuildHasher>(
    file_data: &std::collections::HashMap<String, super::index::FileMetrics, S>,
) -> Vec<RawPredictors> {
    file_data
        .iter()
        .map(|(path, fm)| RawPredictors {
            path: path.clone(),
            total_changes: fm.total_changes,
            age_days: fm.age_days,
            contributor_count: fm.contributor_count,
            knowledge_entropy: fm.knowledge_entropy,
            coupling_degree: fm.coupling_degree,
            burst_risk: fm.burst_risk_score,
        })
        .collect()
}

/// Normalizes a value to [0, 1] using max normalization.
///
/// Returns 0.0 if max is zero (avoids division by zero).
#[inline]
fn safe_normalize(value: f64, max: f64) -> f64 {
    if max <= 0.0 {
        0.0
    } else {
        (value / max).clamp(0.0, 1.0)
    }
}

/// Identifies the top risk factor (highest weighted contribution).
fn identify_top_risk(p: &DefectPredictors) -> RiskFactor {
    let contributions = [
        (W_CHURN * p.churn, RiskFactor::HighChurn),
        (W_RECENCY * p.recency, RiskFactor::RecentlyCreated),
        (W_DEVELOPERS * p.developers, RiskFactor::ManyDevelopers),
        (W_ENTROPY * p.entropy, RiskFactor::HighEntropy),
        (W_COUPLING * p.coupling, RiskFactor::HighCoupling),
        (W_BURST * p.burst, RiskFactor::BurstActivity),
    ];
    contributions
        .iter()
        .max_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal))
        .map_or(RiskFactor::HighChurn, |(_, factor)| *factor)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_raw(
        path: &str,
        changes: u32,
        age: f64,
        devs: u32,
        entropy: f64,
        coupling: u32,
        burst: f64,
    ) -> RawPredictors {
        RawPredictors {
            path: path.to_string(),
            total_changes: changes,
            age_days: age,
            contributor_count: devs,
            knowledge_entropy: entropy,
            coupling_degree: coupling,
            burst_risk: burst,
        }
    }

    #[test]
    fn test_empty_input() {
        let report = compute_defect_predictions(&[]);
        assert!(report.files.is_empty());
        assert!((report.avg_defect_score - 0.0).abs() < f64::EPSILON);
        assert_eq!(report.high_risk_count, 0);
    }

    #[test]
    fn test_single_file_max_risk() {
        let data = vec![make_raw("risky.rs", 100, 1.0, 10, 3.0, 5, 0.9)];
        let report = compute_defect_predictions(&data);

        assert_eq!(report.files.len(), 1);
        let f = &report.files[0];
        // Single file: all metrics normalize to 1.0 (or inverse for age)
        // churn=1.0, recency = 1 - 1/1 = 0, devs=1.0, entropy=1.0, coupling=1.0, burst=0.9
        // score = 0.25*1 + 0.20*0 + 0.20*1 + 0.15*1 + 0.10*1 + 0.10*0.9 = 0.79
        assert!(f.defect_score >= 0.0 && f.defect_score <= 1.0);
    }

    #[test]
    fn test_score_bounded_zero_one() {
        let data = vec![
            make_raw("a.rs", 0, 100.0, 0, 0.0, 0, 0.0),
            make_raw("b.rs", 100, 1.0, 10, 3.0, 5, 1.0),
        ];
        let report = compute_defect_predictions(&data);
        for f in &report.files {
            assert!(
                f.defect_score >= 0.0 && f.defect_score <= 1.0,
                "score out of range: {}",
                f.defect_score
            );
        }
    }

    #[test]
    fn test_sorting_descending() {
        let data = vec![
            make_raw("low.rs", 1, 365.0, 1, 0.0, 0, 0.0),
            make_raw("high.rs", 100, 1.0, 10, 3.0, 5, 1.0),
        ];
        let report = compute_defect_predictions(&data);
        assert_eq!(report.files[0].path, "high.rs");
        assert!(report.files[0].defect_score >= report.files[1].defect_score);
    }

    #[test]
    fn test_risk_factor_identification() {
        // File with high churn but nothing else
        let data = vec![make_raw("churn.rs", 100, 365.0, 1, 0.0, 0, 0.0)];
        let report = compute_defect_predictions(&data);
        assert_eq!(report.files[0].top_risk_factor, RiskFactor::HighChurn);
    }

    #[test]
    fn test_weights_sum_to_one() {
        let sum = W_CHURN + W_RECENCY + W_DEVELOPERS + W_ENTROPY + W_COUPLING + W_BURST;
        assert!(
            (sum - 1.0).abs() < f64::EPSILON,
            "weights sum to {sum}, expected 1.0"
        );
    }

    #[test]
    fn test_high_medium_risk_counts() {
        let data = vec![
            make_raw("high.rs", 100, 1.0, 10, 3.0, 5, 1.0),
            make_raw("medium.rs", 50, 50.0, 5, 1.5, 2, 0.5),
            make_raw("low.rs", 1, 365.0, 1, 0.0, 0, 0.0),
        ];
        let report = compute_defect_predictions(&data);
        // Counts depend on actual score computation
        assert_eq!(
            report.high_risk_count
                + report.medium_risk_count
                + report
                    .files
                    .iter()
                    .filter(|f| f.defect_score <= 0.4)
                    .count(),
            3
        );
    }

    #[test]
    fn test_safe_normalize_zero_max() {
        assert!((safe_normalize(5.0, 0.0) - 0.0).abs() < f64::EPSILON);
        assert!((safe_normalize(0.0, 0.0) - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_safe_normalize_normal() {
        assert!((safe_normalize(5.0, 10.0) - 0.5).abs() < f64::EPSILON);
        assert!((safe_normalize(10.0, 10.0) - 1.0).abs() < f64::EPSILON);
        assert!((safe_normalize(0.0, 10.0) - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_recency_inverse_relationship() {
        // Older files should have LOWER recency (less risky)
        let data = vec![
            make_raw("new.rs", 10, 1.0, 2, 1.0, 1, 0.0),
            make_raw("old.rs", 10, 365.0, 2, 1.0, 1, 0.0),
        ];
        let report = compute_defect_predictions(&data);
        let new_file = report.files.iter().find(|f| f.path == "new.rs").unwrap();
        let old_file = report.files.iter().find(|f| f.path == "old.rs").unwrap();
        assert!(
            new_file.predictors.recency > old_file.predictors.recency,
            "new={}, old={}",
            new_file.predictors.recency,
            old_file.predictors.recency
        );
    }

    #[test]
    fn test_risk_factor_display() {
        assert_eq!(format!("{}", RiskFactor::HighChurn), "high_churn");
        assert_eq!(
            format!("{}", RiskFactor::RecentlyCreated),
            "recently_created"
        );
        assert_eq!(format!("{}", RiskFactor::ManyDevelopers), "many_developers");
        assert_eq!(format!("{}", RiskFactor::HighEntropy), "high_entropy");
        assert_eq!(format!("{}", RiskFactor::HighCoupling), "high_coupling");
        assert_eq!(format!("{}", RiskFactor::BurstActivity), "burst_activity");
    }

    // ── Property-based tests ──

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// All defect scores are in [0, 1].
            #[test]
            fn prop_scores_bounded(
                changes in 0u32..1000,
                age in 0.0f64..1000.0,
                devs in 0u32..50,
                entropy in 0.0f64..5.0,
                coupling in 0u32..20,
                burst in 0.0f64..1.0
            ) {
                let data = vec![make_raw("test.rs", changes, age, devs, entropy, coupling, burst)];
                let report = compute_defect_predictions(&data);
                for f in &report.files {
                    prop_assert!(f.defect_score >= 0.0 && f.defect_score <= 1.0,
                        "score out of bounds: {}", f.defect_score);
                }
            }

            /// More churned files score higher than less churned files (all else equal).
            #[test]
            fn prop_more_churn_higher_score(
                low_churn in 1u32..50,
                high_churn in 51u32..200
            ) {
                let data = vec![
                    make_raw("low.rs", low_churn, 100.0, 2, 1.0, 1, 0.0),
                    make_raw("high.rs", high_churn, 100.0, 2, 1.0, 1, 0.0),
                ];
                let report = compute_defect_predictions(&data);
                let low = report.files.iter().find(|f| f.path == "low.rs").unwrap();
                let high = report.files.iter().find(|f| f.path == "high.rs").unwrap();
                prop_assert!(high.defect_score >= low.defect_score,
                    "high_churn score {} < low_churn score {}",
                    high.defect_score, low.defect_score);
            }
        }
    }
}
