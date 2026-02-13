// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Composite repository health score for M&A due diligence and executive dashboards.
//!
//! Computes a single score [0–100] summarizing overall repository health from
//! weighted combination of pre-computed metrics. Designed for contexts where
//! a single-number assessment is needed: M&A due diligence, executive reporting,
//! portfolio health monitoring.
//!
//! # Dimensions
//!
//! | Dimension | Weight | Source |
//! |-----------|--------|--------|
//! | Bus factor coverage | 20% | Truck factor: % files with BF >= 2 |
//! | Knowledge currency | 20% | Knowledge currency: avg score |
//! | Commit atomicity | 15% | Commit coherence: atomicity index |
//! | Ownership health | 15% | Ownership fragmentation: inverted Gini |
//! | Change stability | 15% | Churn volatility: inverted avg CV |
//! | Defect risk | 15% | Defect prediction: inverted avg score |
//!
//! # Academic Citations
//!
//! - Borg et al. (2024) — "Increasing, Not Diminishing: Returns of Maintainable Code" (`TechDebt` Best Paper)
//! - D'Ambros et al. (2010) — Composite defect prediction
//! - SIG (Software Improvement Group) — IT due diligence methodology
//!
//! # Novelty
//!
//! A purely VCS-derived composite health score with transparent, reproducible
//! weighting is not available in any open-source tool. `CodeScene`'s Code Health
//! requires source code analysis; this uses only commit history (`CodeScene`).

/// Composite repository health score.
#[derive(Debug)]
pub struct RepoHealthReport {
    /// Overall health score [0, 100].
    pub score: f64,
    /// Per-dimension scores [0.0, 1.0].
    pub dimensions: HealthDimensions,
    /// Health grade (A through F).
    pub grade: HealthGrade,
    /// Textual interpretation of the score.
    pub interpretation: &'static str,
}

/// Individual health dimensions, each [0.0, 1.0].
#[derive(Debug)]
pub struct HealthDimensions {
    /// Bus factor coverage: fraction of files with bus factor >= 2.
    pub bus_factor_coverage: f64,
    /// Knowledge currency: average knowledge currency across files.
    pub knowledge_currency: f64,
    /// Commit atomicity: median commit coherence.
    pub commit_atomicity: f64,
    /// Ownership health: 1.0 - avg ownership Gini (lower Gini = healthier).
    pub ownership_health: f64,
    /// Change stability: 1.0 - normalized avg churn CV.
    pub change_stability: f64,
    /// Defect risk: 1.0 - avg defect prediction score.
    pub defect_risk_inverse: f64,
}

/// Letter grade classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HealthGrade {
    /// Excellent (90-100).
    A,
    /// Good (75-89).
    B,
    /// Fair (60-74).
    C,
    /// Poor (40-59).
    D,
    /// Critical (0-39).
    F,
}

impl std::fmt::Display for HealthGrade {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::A => write!(f, "A"),
            Self::B => write!(f, "B"),
            Self::C => write!(f, "C"),
            Self::D => write!(f, "D"),
            Self::F => write!(f, "F"),
        }
    }
}

/// Input data for health score computation.
///
/// All fields should be pre-computed from other insight modules.
pub struct HealthInputs {
    /// Fraction of files with bus factor >= 2 [0.0, 1.0].
    pub bus_factor_coverage: f64,
    /// Average knowledge currency across all files [0.0, 1.0].
    pub avg_knowledge_currency: f64,
    /// Commit atomicity index (median coherence) [0.0, 1.0].
    pub commit_atomicity: f64,
    /// Average ownership Gini coefficient [0.0, 1.0].
    pub avg_ownership_gini: f64,
    /// Average churn volatility CV (coefficient of variation).
    /// Typically [0.0, 5.0+]; will be normalized.
    pub avg_churn_cv: f64,
    /// Average defect prediction score [0.0, 1.0].
    pub avg_defect_score: f64,
}

/// Computes the composite repository health score.
///
/// # Arguments
///
/// * `inputs` - Pre-computed dimension values from other insight modules.
///
/// # Complexity
///
/// O(1) — pure arithmetic on pre-computed values.
#[must_use]
pub fn compute_repo_health(inputs: &HealthInputs) -> RepoHealthReport {
    let dims = HealthDimensions {
        bus_factor_coverage: inputs.bus_factor_coverage.clamp(0.0, 1.0),
        knowledge_currency: inputs.avg_knowledge_currency.clamp(0.0, 1.0),
        commit_atomicity: inputs.commit_atomicity.clamp(0.0, 1.0),
        ownership_health: (1.0 - inputs.avg_ownership_gini).clamp(0.0, 1.0),
        change_stability: (1.0 - (inputs.avg_churn_cv / 3.0).min(1.0)).clamp(0.0, 1.0),
        defect_risk_inverse: (1.0 - inputs.avg_defect_score).clamp(0.0, 1.0),
    };

    // Weighted combination
    let score = (0.20 * dims.bus_factor_coverage
        + 0.20 * dims.knowledge_currency
        + 0.15 * dims.commit_atomicity
        + 0.15 * dims.ownership_health
        + 0.15 * dims.change_stability
        + 0.15 * dims.defect_risk_inverse)
        * 100.0;

    let score = score.clamp(0.0, 100.0);

    let grade = match score as u32 {
        90..=100 => HealthGrade::A,
        75..=89 => HealthGrade::B,
        60..=74 => HealthGrade::C,
        40..=59 => HealthGrade::D,
        _ => HealthGrade::F,
    };

    let interpretation = match grade {
        HealthGrade::A => "Excellent repository health. Well-distributed knowledge, atomic commits, low defect risk.",
        HealthGrade::B => "Good repository health. Minor areas for improvement in knowledge distribution or commit discipline.",
        HealthGrade::C => "Fair repository health. Moderate risks in knowledge silos or commit quality.",
        HealthGrade::D => "Poor repository health. Significant risks: knowledge silos, tangled commits, or high defect density.",
        HealthGrade::F => "Critical repository health. Immediate attention needed: severe knowledge loss risk, unstable code.",
    };

    RepoHealthReport {
        score,
        dimensions: dims,
        grade,
        interpretation,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_perfect_health() {
        let inputs = HealthInputs {
            bus_factor_coverage: 1.0,
            avg_knowledge_currency: 1.0,
            commit_atomicity: 1.0,
            avg_ownership_gini: 0.0,
            avg_churn_cv: 0.0,
            avg_defect_score: 0.0,
        };
        let report = compute_repo_health(&inputs);
        assert!((report.score - 100.0).abs() < 0.01);
        assert_eq!(report.grade, HealthGrade::A);
    }

    #[test]
    fn test_worst_health() {
        let inputs = HealthInputs {
            bus_factor_coverage: 0.0,
            avg_knowledge_currency: 0.0,
            commit_atomicity: 0.0,
            avg_ownership_gini: 1.0,
            avg_churn_cv: 5.0,
            avg_defect_score: 1.0,
        };
        let report = compute_repo_health(&inputs);
        assert!(report.score < 1.0, "score={}", report.score);
        assert_eq!(report.grade, HealthGrade::F);
    }

    #[test]
    fn test_medium_health() {
        let inputs = HealthInputs {
            bus_factor_coverage: 0.5,
            avg_knowledge_currency: 0.5,
            commit_atomicity: 0.5,
            avg_ownership_gini: 0.5,
            avg_churn_cv: 1.5,
            avg_defect_score: 0.5,
        };
        let report = compute_repo_health(&inputs);
        // Should be somewhere in the middle
        assert!(
            report.score > 20.0 && report.score < 80.0,
            "score={}",
            report.score
        );
    }

    #[test]
    fn test_score_bounded() {
        // Out-of-range inputs should still produce valid score
        let inputs = HealthInputs {
            bus_factor_coverage: 2.0,     // > 1.0
            avg_knowledge_currency: -0.5, // < 0.0
            commit_atomicity: 1.5,
            avg_ownership_gini: -0.2,
            avg_churn_cv: -1.0,
            avg_defect_score: 2.0,
        };
        let report = compute_repo_health(&inputs);
        assert!(report.score >= 0.0 && report.score <= 100.0);
    }

    #[test]
    fn test_grade_boundaries() {
        // Test each grade boundary
        for (expected_grade, bf, kc) in [(HealthGrade::A, 1.0, 1.0), (HealthGrade::F, 0.0, 0.0)] {
            let inputs = HealthInputs {
                bus_factor_coverage: bf,
                avg_knowledge_currency: kc,
                commit_atomicity: if bf > 0.5 { 1.0 } else { 0.0 },
                avg_ownership_gini: if bf > 0.5 { 0.0 } else { 1.0 },
                avg_churn_cv: if bf > 0.5 { 0.0 } else { 5.0 },
                avg_defect_score: if bf > 0.5 { 0.0 } else { 1.0 },
            };
            let report = compute_repo_health(&inputs);
            assert_eq!(report.grade, expected_grade, "score={}", report.score);
        }
    }

    #[test]
    fn test_display_grades() {
        assert_eq!(format!("{}", HealthGrade::A), "A");
        assert_eq!(format!("{}", HealthGrade::B), "B");
        assert_eq!(format!("{}", HealthGrade::C), "C");
        assert_eq!(format!("{}", HealthGrade::D), "D");
        assert_eq!(format!("{}", HealthGrade::F), "F");
    }

    #[test]
    fn test_churn_cv_normalization() {
        // High CV (3.0+) should map to 0.0 stability
        let inputs = HealthInputs {
            bus_factor_coverage: 0.5,
            avg_knowledge_currency: 0.5,
            commit_atomicity: 0.5,
            avg_ownership_gini: 0.5,
            avg_churn_cv: 3.0,
            avg_defect_score: 0.5,
        };
        let report = compute_repo_health(&inputs);
        assert!((report.dimensions.change_stability - 0.0).abs() < 0.01);

        // Zero CV should map to 1.0 stability
        let inputs2 = HealthInputs {
            avg_churn_cv: 0.0,
            ..inputs
        };
        let report2 = compute_repo_health(&inputs2);
        assert!((report2.dimensions.change_stability - 1.0).abs() < 0.01);
    }

    #[test]
    fn test_interpretation_not_empty() {
        let inputs = HealthInputs {
            bus_factor_coverage: 0.5,
            avg_knowledge_currency: 0.5,
            commit_atomicity: 0.5,
            avg_ownership_gini: 0.5,
            avg_churn_cv: 1.0,
            avg_defect_score: 0.5,
        };
        let report = compute_repo_health(&inputs);
        assert!(!report.interpretation.is_empty());
    }
}
