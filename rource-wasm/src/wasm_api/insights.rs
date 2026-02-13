// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Repository insights API.
//!
//! Exposes research-backed software engineering metrics computed from VCS
//! commit history. These metrics provide actionable intelligence about
//! code health, organizational risk, and development patterns.
//!
//! All metrics are computed from the loaded commit data (no external APIs).
//! The insights report and index are cached on the `Rource` struct at load
//! time (Phase 89), so all 38 API methods perform zero recomputation.

use std::fmt::Write;

use wasm_bindgen::prelude::*;

#[cfg(test)]
use rource_core::insights::{self, index::InsightsIndex, CommitRecord, FileActionKind, FileRecord};
use rource_core::insights::{InsightsReport, SummaryStats};

use crate::Rource;

// ============================================================================
// Conversion: rource_vcs::Commit → insights::CommitRecord
// ============================================================================

/// Converts loaded VCS commits to insight-ready records (test-only; production uses `Rource::convert_commits_for_insights`).
#[cfg(test)]
fn convert_commits(commits: &[rource_vcs::Commit]) -> Vec<CommitRecord> {
    commits
        .iter()
        .map(|c| CommitRecord {
            timestamp: c.timestamp,
            author: c.author.clone(),
            message: c.message.clone(),
            files: c
                .files
                .iter()
                .map(|f| FileRecord {
                    path: f.path.to_string_lossy().to_string(),
                    action: match f.action {
                        rource_vcs::FileAction::Create => FileActionKind::Create,
                        rource_vcs::FileAction::Modify => FileActionKind::Modify,
                        rource_vcs::FileAction::Delete => FileActionKind::Delete,
                    },
                })
                .collect(),
        })
        .collect()
}

// ============================================================================
// JSON Serialization Helpers
// ============================================================================

/// Escapes a string for safe JSON embedding.
fn escape_json(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            c if c < '\x20' => {
                let _ = write!(result, "\\u{:04x}", c as u32);
            }
            c => result.push(c),
        }
    }
    result
}

/// Formats the summary section of the insights report.
fn format_summary_json(summary: &SummaryStats) -> String {
    format!(
        r#"{{"totalCommits":{},"totalFiles":{},"totalAuthors":{},"timeSpanSeconds":{},"avgFilesPerCommit":{:.2},"avgCommitEntropy":{:.4},"medianCommitEntropy":{:.4}}}"#,
        summary.total_commits,
        summary.total_files,
        summary.total_authors,
        summary.time_span_seconds,
        summary.avg_files_per_commit,
        summary.avg_commit_entropy,
        summary.median_commit_entropy,
    )
}

/// Formats the complete insights report as JSON.
fn format_insights_json(report: &InsightsReport) -> String {
    let mut json = String::with_capacity(8192);
    json.push_str("{\"summary\":");
    json.push_str(&format_summary_json(&report.summary));
    write_hotspots_json(&mut json, report);
    write_couplings_json(&mut json, report);
    write_ownership_json(&mut json, report);
    write_bus_factors_json(&mut json, report);
    write_temporal_json(&mut json, report);
    write_growth_json(&mut json, report);
    write_work_type_json(&mut json, report);
    write_cadence_json(&mut json, report);
    write_knowledge_json(&mut json, report);
    write_profiles_json(&mut json, report);
    write_lifecycle_json(&mut json, report);
    write_inequality_json(&mut json, report);
    write_change_entropy_json(&mut json, report);
    write_circadian_json(&mut json, report);
    write_change_bursts_json(&mut json, report);
    write_focus_json(&mut json, report);
    write_modularity_json(&mut json, report);
    write_congruence_json(&mut json, report);
    write_survival_json(&mut json, report);
    write_network_json(&mut json, report);
    write_developer_experience_json(&mut json, report);
    write_ownership_fragmentation_json(&mut json, report);
    write_release_rhythm_json(&mut json, report);
    write_knowledge_distribution_json(&mut json, report);
    write_churn_volatility_json(&mut json, report);
    write_truck_factor_json(&mut json, report);
    write_turnover_impact_json(&mut json, report);
    write_commit_complexity_json(&mut json, report);
    write_defect_patterns_json(&mut json, report);
    write_tech_distribution_json(&mut json, report);
    write_activity_heatmap_json(&mut json, report);
    write_tech_expertise_json(&mut json, report);
    // Intelligence tab metrics (Session 7)
    write_contextual_complexity_json(&mut json, report);
    write_commit_cohesion_json(&mut json, report);
    write_change_propagation_json(&mut json, report);
    write_commit_message_entropy_json(&mut json, report);
    write_knowledge_half_life_json(&mut json, report);
    write_architectural_drift_json(&mut json, report);
    write_succession_readiness_json(&mut json, report);
    // Intelligence tab metrics (Session 8: M9-M32)
    write_reviewer_recommendation_json(&mut json, report);
    write_review_response_json(&mut json, report);
    write_onboarding_velocity_json(&mut json, report);
    write_interface_stability_json(&mut json, report);
    write_tech_debt_velocity_json(&mut json, report);
    write_focus_drift_json(&mut json, report);
    write_ai_change_detection_json(&mut json, report);
    write_knowledge_gini_json(&mut json, report);
    write_expertise_profile_json(&mut json, report);
    write_cognitive_load_json(&mut json, report);
    // Strategic tab metrics (next-generation git mining insights)
    write_dora_proxy_json(&mut json, report);
    write_knowledge_currency_json(&mut json, report);
    write_team_rhythm_json(&mut json, report);
    write_commit_coherence_json(&mut json, report);
    write_markov_prediction_json(&mut json, report);
    write_repo_health_json(&mut json, report);
    json.push('}');
    json
}

/// Appends the hotspots section to the JSON output.
fn write_hotspots_json(json: &mut String, report: &InsightsReport) {
    json.push_str(",\"hotspots\":[");
    for (i, h) in report.hotspots.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","totalChanges":{},"weightedChanges":{:.2},"score":{:.2},"creates":{},"modifies":{},"deletes":{},"firstSeen":{},"lastSeen":{}}}"#,
            escape_json(&h.path),
            h.total_changes,
            h.weighted_changes,
            h.score,
            h.creates,
            h.modifies,
            h.deletes,
            h.first_seen,
            h.last_seen,
        );
    }
    json.push(']');
}

/// Appends the couplings section to the JSON output.
fn write_couplings_json(json: &mut String, report: &InsightsReport) {
    json.push_str(",\"couplings\":[");
    for (i, c) in report.couplings.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"fileA":"{}","fileB":"{}","support":{},"confidenceAB":{:.4},"confidenceBA":{:.4},"totalA":{},"totalB":{},"lift":{:.4}}}"#,
            escape_json(&c.file_a),
            escape_json(&c.file_b),
            c.support,
            c.confidence_ab,
            c.confidence_ba,
            c.total_a,
            c.total_b,
            c.lift,
        );
    }
    json.push(']');
}

/// Appends the ownership section to the JSON output.
fn write_ownership_json(json: &mut String, report: &InsightsReport) {
    json.push_str(",\"ownership\":[");
    for (i, o) in report.ownership.iter().take(50).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","topOwner":"{}","topOwnerShare":{:.4},"totalChanges":{},"contributorCount":{}}}"#,
            escape_json(&o.path),
            escape_json(&o.top_owner),
            o.top_owner_share,
            o.total_changes,
            o.contributor_count,
        );
    }
    json.push(']');
}

/// Appends the bus factors section to the JSON output.
fn write_bus_factors_json(json: &mut String, report: &InsightsReport) {
    json.push_str(",\"busFactors\":[");
    for (i, b) in report.bus_factors.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let critical: Vec<String> = b
            .critical_contributors
            .iter()
            .map(|c| format!("\"{}\"", escape_json(c)))
            .collect();
        let _ = write!(
            json,
            r#"{{"directory":"{}","busFactor":{},"fileCount":{},"contributorCount":{},"criticalContributors":[{}]}}"#,
            escape_json(&b.directory),
            b.bus_factor,
            b.file_count,
            b.contributor_count,
            critical.join(","),
        );
    }
    json.push(']');
}

/// Appends the temporal section to the JSON output.
fn write_temporal_json(json: &mut String, report: &InsightsReport) {
    json.push_str(",\"temporal\":{");

    // Activity heatmap as flat array [day0_hour0, day0_hour1, ..., day6_hour23]
    json.push_str("\"activityHeatmap\":[");
    for day in 0..7 {
        for hour in 0..24 {
            if day > 0 || hour > 0 {
                json.push(',');
            }
            let _ = write!(json, "{}", report.temporal.activity_heatmap[day][hour]);
        }
    }
    json.push(']');

    let _ = write!(
        json,
        r#","peakHour":{},"peakDay":{},"commitsPerDay":[{},{},{},{},{},{},{}],"commitsPerHour":[{}]"#,
        report.temporal.peak_hour,
        report.temporal.peak_day,
        report.temporal.commits_per_day[0],
        report.temporal.commits_per_day[1],
        report.temporal.commits_per_day[2],
        report.temporal.commits_per_day[3],
        report.temporal.commits_per_day[4],
        report.temporal.commits_per_day[5],
        report.temporal.commits_per_day[6],
        report
            .temporal
            .commits_per_hour
            .iter()
            .map(std::string::ToString::to_string)
            .collect::<Vec<_>>()
            .join(","),
    );

    // Bursts
    json.push_str(",\"bursts\":[");
    for (i, b) in report.temporal.bursts.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"start":{},"end":{},"commitCount":{},"totalFiles":{},"durationSeconds":{}}}"#,
            b.start, b.end, b.commit_count, b.total_files, b.duration_seconds,
        );
    }
    json.push(']');

    let _ = write!(
        json,
        r#","avgFilesInBursts":{:.2},"avgFilesOutsideBursts":{:.2}}}"#,
        report.temporal.avg_files_in_bursts, report.temporal.avg_files_outside_bursts,
    );
}

/// Appends the growth trajectory section to the JSON output.
fn write_growth_json(json: &mut String, report: &InsightsReport) {
    let g = &report.growth;
    let trend = match g.trend {
        rource_core::insights::growth::GrowthTrend::Accelerating => "accelerating",
        rource_core::insights::growth::GrowthTrend::Stable => "stable",
        rource_core::insights::growth::GrowthTrend::Decelerating => "decelerating",
        rource_core::insights::growth::GrowthTrend::Shrinking => "shrinking",
    };
    let _ = write!(
        json,
        r#","growth":{{"currentFileCount":{},"totalCreated":{},"totalDeleted":{},"netGrowth":{},"avgMonthlyGrowth":{:.2},"trend":"{}","snapshotCount":{}}}"#,
        g.current_file_count,
        g.total_created,
        g.total_deleted,
        g.net_growth,
        g.avg_monthly_growth,
        trend,
        g.snapshots.len(),
    );
}

/// Appends the work-type mix section to the JSON output.
fn write_work_type_json(json: &mut String, report: &InsightsReport) {
    let w = &report.work_type;
    let dominant = match w.dominant_type {
        rource_core::insights::work_type::WorkType::Feature => "feature",
        rource_core::insights::work_type::WorkType::Maintenance => "maintenance",
        rource_core::insights::work_type::WorkType::Cleanup => "cleanup",
        rource_core::insights::work_type::WorkType::Mixed => "mixed",
    };
    let _ = write!(
        json,
        r#","workType":{{"featurePct":{:.1},"maintenancePct":{:.1},"cleanupPct":{:.1},"mixedPct":{:.1},"dominantType":"{}","totalCommits":{}}}"#,
        w.feature_pct, w.maintenance_pct, w.cleanup_pct, w.mixed_pct, dominant, w.total_commits,
    );
}

/// Appends the cadence analysis section to the JSON output.
fn write_cadence_json(json: &mut String, report: &InsightsReport) {
    let c = &report.cadence;
    json.push_str(",\"cadence\":{\"authors\":[");
    for (i, a) in c.authors.iter().take(20).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let cadence_type = match a.cadence_type {
            rource_core::insights::cadence::CadenceType::Regular => "regular",
            rource_core::insights::cadence::CadenceType::Moderate => "moderate",
            rource_core::insights::cadence::CadenceType::Bursty => "bursty",
        };
        let _ = write!(
            json,
            r#"{{"author":"{}","commitCount":{},"meanInterval":{:.0},"medianInterval":{:.0},"cv":{:.2},"cadenceType":"{}","activeSpan":{}}}"#,
            escape_json(&a.author),
            a.commit_count,
            a.mean_interval,
            a.median_interval,
            a.cv,
            cadence_type,
            a.active_span,
        );
    }
    let _ = write!(
        json,
        r#"],"teamMeanInterval":{:.0},"regularCount":{},"burstyCount":{},"moderateCount":{}}}"#,
        c.team_mean_interval, c.regular_count, c.bursty_count, c.moderate_count,
    );
}

/// Appends the knowledge map section to the JSON output.
fn write_knowledge_json(json: &mut String, report: &InsightsReport) {
    let k = &report.knowledge;
    json.push_str(",\"knowledge\":{\"files\":[");
    for (i, f) in k.files.iter().take(50).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","entropy":{:.4},"isSilo":{},"primaryOwner":"{}","contributorCount":{}}}"#,
            escape_json(&f.path),
            f.knowledge_entropy,
            f.is_silo,
            escape_json(&f.primary_owner),
            f.contributor_count,
        );
    }
    json.push_str("],\"directories\":[");
    for (i, d) in k.directories.iter().take(20).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"directory":"{}","avgEntropy":{:.4},"siloPct":{:.1},"fileCount":{},"siloCount":{}}}"#,
            escape_json(&d.directory),
            d.avg_entropy,
            d.silo_percentage,
            d.file_count,
            d.silo_count,
        );
    }
    let _ = write!(
        json,
        r#"],"totalSilos":{},"siloPct":{:.1},"avgEntropy":{:.4}}}"#,
        k.total_silos, k.silo_percentage, k.avg_entropy,
    );
}

/// Appends the developer profiles section to the JSON output.
fn write_profiles_json(json: &mut String, report: &InsightsReport) {
    let p = &report.profiles;
    json.push_str(",\"profiles\":{\"developers\":[");
    for (i, d) in p.developers.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let classification = match d.classification {
            rource_core::insights::profiles::ContributorType::Core => "core",
            rource_core::insights::profiles::ContributorType::Peripheral => "peripheral",
            rource_core::insights::profiles::ContributorType::DriveBy => "drive-by",
        };
        let _ = write!(
            json,
            r#"{{"author":"{}","commitCount":{},"uniqueFiles":{},"avgFilesPerCommit":{:.1},"classification":"{}","activeSpanDays":{:.1}}}"#,
            escape_json(&d.author),
            d.commit_count,
            d.unique_files,
            d.avg_files_per_commit,
            classification,
            d.active_span_days,
        );
    }
    let _ = write!(
        json,
        r#"],"coreCount":{},"peripheralCount":{},"driveByCount":{},"totalContributors":{}}}"#,
        p.core_count, p.peripheral_count, p.drive_by_count, p.total_contributors,
    );
}

/// Appends the file lifecycle section to the JSON output.
fn write_lifecycle_json(json: &mut String, report: &InsightsReport) {
    let l = &report.lifecycle;
    json.push_str(",\"lifecycle\":{\"files\":[");
    for (i, f) in l.files.iter().take(50).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let stage = match f.stage {
            rource_core::insights::lifecycle::LifecycleStage::Active => "active",
            rource_core::insights::lifecycle::LifecycleStage::Stable => "stable",
            rource_core::insights::lifecycle::LifecycleStage::Ephemeral => "ephemeral",
            rource_core::insights::lifecycle::LifecycleStage::Dead => "dead",
            rource_core::insights::lifecycle::LifecycleStage::Deleted => "deleted",
        };
        let _ = write!(
            json,
            r#"{{"path":"{}","stage":"{}","ageDays":{:.1},"modificationCount":{},"modsPerMonth":{:.1},"uniqueAuthors":{}}}"#,
            escape_json(&f.path),
            stage,
            f.age_days,
            f.modification_count,
            f.modifications_per_month,
            f.unique_authors,
        );
    }
    let _ = write!(
        json,
        r#"],"avgLifespanDays":{:.1},"ephemeralCount":{},"deadCount":{},"deletedCount":{},"activeCount":{},"churnRate":{:.2},"totalFilesSeen":{}}}"#,
        l.avg_lifespan_days,
        l.ephemeral_count,
        l.dead_count,
        l.deleted_count,
        l.active_count,
        l.churn_rate,
        l.total_files_seen,
    );
}

/// Appends the inequality / Gini coefficient section to the JSON output.
fn write_inequality_json(json: &mut String, report: &InsightsReport) {
    let iq = &report.inequality;
    let _ = write!(
        json,
        r#","inequality":{{"giniCoefficient":{:.4},"top1PctShare":{:.4},"top10PctShare":{:.4},"top20PctShare":{:.4},"totalDevelopers":{},"totalCommits":{},"lorenzCurve":["#,
        iq.gini_coefficient,
        iq.top_1_pct_share,
        iq.top_10_pct_share,
        iq.top_20_pct_share,
        iq.total_developers,
        iq.total_commits,
    );
    for (i, &(dev_share, commit_share)) in iq.lorenz_curve.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(json, "[{dev_share:.4},{commit_share:.4}]");
    }
    json.push_str("],\"windows\":[");
    for (i, w) in iq.windows.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"windowStart":{},"windowEnd":{},"gini":{:.4},"developerCount":{}}}"#,
            w.window_start, w.window_end, w.gini, w.developer_count,
        );
    }
    json.push_str("]}");
}

/// Appends the change entropy section to the JSON output.
fn write_change_entropy_json(json: &mut String, report: &InsightsReport) {
    let ce = &report.change_entropy;
    let trend = match ce.trend {
        rource_core::insights::change_entropy::EntropyTrend::Increasing => "increasing",
        rource_core::insights::change_entropy::EntropyTrend::Stable => "stable",
        rource_core::insights::change_entropy::EntropyTrend::Decreasing => "decreasing",
    };
    json.push_str(",\"changeEntropy\":{\"windows\":[");
    for (i, w) in ce.windows.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"windowStart":{},"windowEnd":{},"rawEntropy":{:.4},"normalizedEntropy":{:.4},"filesModified":{},"totalModifications":{}}}"#,
            w.window_start,
            w.window_end,
            w.raw_entropy,
            w.normalized_entropy,
            w.files_modified,
            w.total_modifications,
        );
    }
    let max_idx = ce
        .max_entropy_window_idx
        .map_or_else(|| "null".to_string(), |i| i.to_string());
    let _ = write!(
        json,
        r#"],"avgNormalizedEntropy":{:.4},"maxEntropyWindowIdx":{},"trend":"{}"}}"#,
        ce.avg_normalized_entropy, max_idx, trend,
    );
}

/// Appends the circadian risk section to the JSON output.
fn write_circadian_json(json: &mut String, report: &InsightsReport) {
    let cr = &report.circadian;
    json.push_str(",\"circadian\":{\"files\":[");
    for (i, f) in cr.files.iter().take(50).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","totalRisk":{:.4},"highRiskCommits":{},"totalCommits":{},"highRiskFraction":{:.4}}}"#,
            escape_json(&f.path),
            f.total_risk,
            f.high_risk_commits,
            f.total_commits,
            f.high_risk_fraction,
        );
    }
    json.push_str("],\"authors\":[");
    for (i, a) in cr.authors.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","avgRisk":{:.4},"highRiskCommits":{},"totalCommits":{},"preferredHour":{}}}"#,
            escape_json(&a.author),
            a.avg_risk,
            a.high_risk_commits,
            a.total_commits,
            a.preferred_hour,
        );
    }
    json.push_str("],\"hourlyRisk\":[");
    for (i, &r) in cr.hourly_risk.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(json, "{r:.2}");
    }
    let _ = write!(
        json,
        r#"],"highRiskPct":{:.1},"totalCommitsAnalyzed":{}}}"#,
        cr.high_risk_percentage, cr.total_commits_analyzed,
    );
}

/// Appends the change bursts section to the JSON output.
fn write_change_bursts_json(json: &mut String, report: &InsightsReport) {
    let cb = &report.change_bursts;
    json.push_str(",\"changeBursts\":{\"files\":[");
    for (i, f) in cb.files.iter().take(50).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","burstCount":{},"maxBurstLength":{},"totalBurstCommits":{},"maxBurstAuthors":{},"riskScore":{:.4}}}"#,
            escape_json(&f.path),
            f.burst_count,
            f.max_burst_length,
            f.total_burst_commits,
            f.max_burst_authors,
            f.risk_score,
        );
    }
    let _ = write!(
        json,
        r#"],"totalBursts":{},"avgBurstLength":{:.2},"filesWithBursts":{},"multiAuthorBurstCount":{}}}"#,
        cb.total_bursts, cb.avg_burst_length, cb.files_with_bursts, cb.multi_author_burst_count,
    );
}

/// Appends the developer focus / file diffusion section to the JSON output.
fn write_focus_json(json: &mut String, report: &InsightsReport) {
    let fo = &report.focus;
    json.push_str(",\"focus\":{\"developers\":[");
    for (i, d) in fo.developers.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","focusScore":{:.4},"directoriesTouched":{},"commitCount":{}}}"#,
            escape_json(&d.author),
            d.focus_score,
            d.directories_touched,
            d.commit_count,
        );
    }
    json.push_str("],\"files\":[");
    for (i, f) in fo.files.iter().take(50).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","diffusionScore":{:.4},"contributorCount":{},"totalChanges":{}}}"#,
            escape_json(&f.path),
            f.diffusion_score,
            f.contributor_count,
            f.total_changes,
        );
    }
    let _ = write!(
        json,
        r#"],"avgDeveloperFocus":{:.4},"avgFileDiffusion":{:.4}}}"#,
        fo.avg_developer_focus, fo.avg_file_diffusion,
    );
}

/// Appends the co-change modularity section to the JSON output.
fn write_modularity_json(json: &mut String, report: &InsightsReport) {
    let mo = &report.modularity;
    json.push_str(",\"modularity\":{\"directories\":[");
    for (i, d) in mo.directories.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"directory":"{}","modularityScore":{:.4},"internalCoupling":{},"externalCoupling":{}}}"#,
            escape_json(&d.directory),
            d.modularity_score,
            d.internal_coupling,
            d.external_coupling,
        );
    }
    let _ = write!(
        json,
        r#"],"modularityIndex":{:.4},"crossModuleRatio":{:.4},"totalIntraEdges":{},"totalCrossEdges":{}}}"#,
        mo.modularity_index, mo.cross_module_ratio, mo.total_intra_edges, mo.total_cross_edges,
    );
}

/// Appends the sociotechnical congruence section to the JSON output.
fn write_congruence_json(json: &mut String, report: &InsightsReport) {
    let co = &report.congruence;
    json.push_str(",\"congruence\":{\"coordinationGaps\":[");
    for (i, g) in co.coordination_gaps.iter().take(20).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"developerA":"{}","developerB":"{}","sharedDependencies":{}}}"#,
            escape_json(&g.developer_a),
            escape_json(&g.developer_b),
            g.shared_dependencies,
        );
    }
    let _ = write!(
        json,
        r#"],"congruenceScore":{:.4},"requiredCoordinations":{},"actualCoordinations":{},"totalDeveloperPairs":{}}}"#,
        co.congruence_score,
        co.required_coordinations,
        co.actual_coordinations,
        co.total_developer_pairs,
    );
}

/// Appends the file survival (Kaplan-Meier) section to the JSON output.
fn write_survival_json(json: &mut String, report: &InsightsReport) {
    let sv = &report.survival;
    json.push_str(",\"survival\":{\"curve\":[");
    for (i, p) in sv.curve.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"timeDays":{:.1},"survivalProbability":{:.4},"atRisk":{},"events":{}}}"#,
            p.time_days, p.survival_probability, p.at_risk, p.events,
        );
    }
    let median = sv
        .median_survival_days
        .map_or_else(|| "null".to_string(), |d| format!("{d:.1}"));
    let _ = write!(
        json,
        r#"],"medianSurvivalDays":{},"infantMortalityRate":{:.4},"totalBirths":{},"totalDeaths":{},"censoredCount":{}}}"#,
        median, sv.infant_mortality_rate, sv.total_births, sv.total_deaths, sv.censored_count,
    );
}

/// Appends the developer network centrality section to the JSON output.
fn write_network_json(json: &mut String, report: &InsightsReport) {
    let nw = &report.network;
    json.push_str(",\"network\":{\"developers\":[");
    for (i, d) in nw.developers.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","degree":{},"betweenness":{:.4},"clusteringCoefficient":{:.4},"sharedFilesTotal":{}}}"#,
            escape_json(&d.author),
            d.degree,
            d.betweenness,
            d.clustering_coefficient,
            d.shared_files_total,
        );
    }
    let _ = write!(
        json,
        r#"],"networkDensity":{:.4},"connectedComponents":{},"largestComponentSize":{},"totalEdges":{},"avgDegree":{:.2}}}"#,
        nw.network_density,
        nw.connected_components,
        nw.largest_component_size,
        nw.total_edges,
        nw.avg_degree,
    );
}

// ============================================================================
// WASM API
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Returns comprehensive repository insights as JSON from the cached report.
    ///
    /// Includes research-backed metrics:
    ///
    /// - **Hotspots**: Files with high change frequency (defect predictors)
    /// - **Change Coupling**: Hidden dependencies via co-change patterns
    /// - **Code Ownership**: Knowledge concentration per file
    /// - **Bus Factor**: Organizational resilience per directory
    /// - **Temporal Patterns**: Activity heatmap and burst detection
    /// - **Summary**: Commit entropy, author count, time span
    ///
    /// Returns a JSON string with the complete insights report.
    /// Returns `null` if no commits are loaded.
    ///
    /// # Performance
    ///
    /// Report is cached at load time (Phase 89). This method only serializes.
    #[wasm_bindgen(js_name = getInsights)]
    pub fn get_insights(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        Some(format_insights_json(report))
    }

    /// Returns the top N file hotspots as JSON.
    ///
    /// Hotspots are files with disproportionately high change frequency,
    /// weighted by recency. Research shows these predict defect-prone code
    /// with ~89% accuracy (Nagappan et al. 2005).
    ///
    /// # Arguments
    ///
    /// * `limit` - Maximum number of hotspots to return (default: 20)
    #[wasm_bindgen(js_name = getHotspots)]
    pub fn get_hotspots(&self, limit: Option<usize>) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let n = limit.unwrap_or(20).min(report.hotspots.len());

        let mut json = String::with_capacity(1024);
        json.push('[');
        for (i, h) in report.hotspots.iter().take(n).enumerate() {
            if i > 0 {
                json.push(',');
            }
            let _ = write!(
                json,
                r#"{{"path":"{}","totalChanges":{},"weightedChanges":{:.2},"score":{:.2},"creates":{},"modifies":{},"deletes":{}}}"#,
                escape_json(&h.path),
                h.total_changes,
                h.weighted_changes,
                h.score,
                h.creates,
                h.modifies,
                h.deletes,
            );
        }
        json.push(']');
        Some(json)
    }

    /// Returns change coupling pairs as JSON.
    ///
    /// Identifies files that frequently change together, revealing hidden
    /// architectural dependencies that static analysis misses.
    /// Research shows coupling correlates with defects better than complexity
    /// metrics (D'Ambros et al. 2009).
    ///
    /// # Arguments
    ///
    /// * `limit` - Maximum number of coupling pairs to return (default: 20)
    #[wasm_bindgen(js_name = getChangeCoupling)]
    pub fn get_change_coupling(&self, limit: Option<usize>) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let n = limit.unwrap_or(20).min(report.couplings.len());

        let mut json = String::with_capacity(1024);
        json.push('[');
        for (i, c) in report.couplings.iter().take(n).enumerate() {
            if i > 0 {
                json.push(',');
            }
            let _ = write!(
                json,
                r#"{{"fileA":"{}","fileB":"{}","support":{},"confidenceAB":{:.4},"confidenceBA":{:.4},"lift":{:.4}}}"#,
                escape_json(&c.file_a),
                escape_json(&c.file_b),
                c.support,
                c.confidence_ab,
                c.confidence_ba,
                c.lift,
            );
        }
        json.push(']');
        Some(json)
    }

    /// Returns bus factor analysis per directory as JSON.
    ///
    /// The bus factor is the minimum number of contributors who must leave
    /// before a directory becomes unmaintained. Low values (1-2) indicate
    /// critical key-person risk.
    #[wasm_bindgen(js_name = getBusFactors)]
    pub fn get_bus_factors(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;

        let mut json = String::with_capacity(512);
        json.push('[');
        for (i, b) in report.bus_factors.iter().enumerate() {
            if i > 0 {
                json.push(',');
            }
            let critical: Vec<String> = b
                .critical_contributors
                .iter()
                .map(|c| format!("\"{}\"", escape_json(c)))
                .collect();
            let _ = write!(
                json,
                r#"{{"directory":"{}","busFactor":{},"fileCount":{},"contributorCount":{},"criticalContributors":[{}]}}"#,
                escape_json(&b.directory),
                b.bus_factor,
                b.file_count,
                b.contributor_count,
                critical.join(","),
            );
        }
        json.push(']');
        Some(json)
    }

    /// Returns temporal activity patterns as JSON.
    ///
    /// Includes:
    /// - Activity heatmap (7 days x 24 hours)
    /// - Peak activity times
    /// - Change burst detection
    /// - Average files per commit during/outside bursts
    #[wasm_bindgen(js_name = getTemporalPatterns)]
    pub fn get_temporal_patterns(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;

        let mut json = String::with_capacity(1024);
        json.push('{');

        // Heatmap
        json.push_str("\"activityHeatmap\":[");
        for day in 0..7 {
            for hour in 0..24 {
                if day > 0 || hour > 0 {
                    json.push(',');
                }
                let _ = write!(json, "{}", report.temporal.activity_heatmap[day][hour]);
            }
        }
        json.push(']');

        let _ = write!(
            json,
            r#","peakHour":{},"peakDay":{},"burstCount":{},"avgFilesInBursts":{:.2},"avgFilesOutsideBursts":{:.2}}}"#,
            report.temporal.peak_hour,
            report.temporal.peak_day,
            report.temporal.bursts.len(),
            report.temporal.avg_files_in_bursts,
            report.temporal.avg_files_outside_bursts,
        );

        Some(json)
    }

    /// Returns a summary of repository health metrics as JSON.
    ///
    /// Quick overview suitable for dashboard display:
    /// - Total commits, files, authors
    /// - Time span
    /// - Average commit entropy (change scatter)
    /// - Top 5 hotspots
    /// - Lowest bus factors
    #[wasm_bindgen(js_name = getInsightsSummary)]
    pub fn get_insights_summary(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;

        let mut json = String::with_capacity(1024);
        json.push_str("{\"summary\":");
        json.push_str(&format_summary_json(&report.summary));

        // Top 5 hotspots
        json.push_str(",\"topHotspots\":[");
        for (i, h) in report.hotspots.iter().take(5).enumerate() {
            if i > 0 {
                json.push(',');
            }
            let _ = write!(
                json,
                r#"{{"path":"{}","score":{:.2},"totalChanges":{}}}"#,
                escape_json(&h.path),
                h.score,
                h.total_changes,
            );
        }
        json.push(']');

        // Lowest bus factors (most at risk)
        json.push_str(",\"riskDirectories\":[");
        for (i, b) in report.bus_factors.iter().take(5).enumerate() {
            if i > 0 {
                json.push(',');
            }
            let _ = write!(
                json,
                r#"{{"directory":"{}","busFactor":{},"fileCount":{}}}"#,
                escape_json(&b.directory),
                b.bus_factor,
                b.file_count,
            );
        }
        json.push(']');

        // Top coupling
        json.push_str(",\"topCouplings\":[");
        for (i, c) in report.couplings.iter().take(5).enumerate() {
            if i > 0 {
                json.push(',');
            }
            let _ = write!(
                json,
                r#"{{"fileA":"{}","fileB":"{}","support":{}}}"#,
                escape_json(&c.file_a),
                escape_json(&c.file_b),
                c.support,
            );
        }
        json.push(']');

        json.push('}');
        Some(json)
    }

    /// Returns codebase growth trajectory as JSON.
    ///
    /// Tracks active file count over time, growth rate, and trend
    /// classification (Lehman 1996 Laws of Software Evolution).
    #[wasm_bindgen(js_name = getCodebaseGrowth)]
    pub fn get_codebase_growth(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(512);
        json.push('{');
        write_growth_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns work-type mix analysis as JSON.
    ///
    /// Classifies commits by Create/Modify/Delete ratio to reveal whether
    /// the team is building features, maintaining code, or cleaning up
    /// (Hindle et al. 2008, Mockus & Votta 2000).
    #[wasm_bindgen(js_name = getWorkTypeMix)]
    pub fn get_work_type_mix(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(256);
        json.push('{');
        write_work_type_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns commit cadence analysis per developer as JSON.
    ///
    /// Analyzes inter-commit intervals to classify contributors as
    /// regular, moderate, or bursty (Eyolfson et al. 2014).
    #[wasm_bindgen(js_name = getCommitCadence)]
    pub fn get_commit_cadence(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_cadence_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns knowledge map and silo analysis as JSON.
    ///
    /// Computes Shannon entropy of ownership distribution per file to
    /// identify knowledge silos (Rigby & Bird 2013, Fritz et al. 2014).
    #[wasm_bindgen(js_name = getKnowledgeMap)]
    pub fn get_knowledge_map(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        json.push('{');
        write_knowledge_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns developer activity profiles as JSON.
    ///
    /// Classifies contributors as core, peripheral, or drive-by based
    /// on commit share and recency (Mockus et al. 2002).
    #[wasm_bindgen(js_name = getDeveloperProfiles)]
    pub fn get_developer_profiles(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_profiles_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns file lifecycle analysis as JSON.
    ///
    /// Tracks file creation, modification, and deletion patterns to
    /// identify ephemeral, dead, and actively maintained files
    /// (Godfrey & Tu 2000, Gall et al. 1998).
    #[wasm_bindgen(js_name = getFileLifecycles)]
    pub fn get_file_lifecycles(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        json.push('{');
        write_lifecycle_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns contribution inequality / Gini coefficient analysis as JSON.
    ///
    /// Measures how unevenly commits are distributed using the Gini coefficient.
    /// Includes Lorenz curve, top-K% share, and windowed trend analysis
    /// (Chelkowski et al. 2016).
    #[wasm_bindgen(js_name = getContributionInequality)]
    pub fn get_contribution_inequality(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_inequality_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns sliding-window change entropy analysis as JSON.
    ///
    /// Measures Shannon entropy of file modification distribution within
    /// time windows for defect risk prediction (Hassan ICSE 2009).
    #[wasm_bindgen(js_name = getChangeEntropy)]
    pub fn get_change_entropy(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_change_entropy_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns circadian (time-of-day) risk patterns as JSON.
    ///
    /// Assigns risk scores based on hour-of-day and day-of-week.
    /// Commits between midnight–4AM UTC are significantly buggier
    /// (Eyolfson et al. 2011).
    #[wasm_bindgen(js_name = getCircadianRisk)]
    pub fn get_circadian_risk(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        json.push('{');
        write_circadian_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns per-file change burst detection as JSON.
    ///
    /// Detects rapid consecutive changes to individual files.
    /// Files with many bursts are significantly more defect-prone
    /// (Nagappan et al. 2010).
    #[wasm_bindgen(js_name = getChangeBursts)]
    pub fn get_change_bursts(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_change_bursts_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns developer focus and file diffusion analysis as JSON.
    ///
    /// Measures how concentrated developers' activity is (focus) and
    /// how spread out files' contributors are (diffusion).
    /// More focused developers introduce fewer defects (Posnett et al. 2013).
    #[wasm_bindgen(js_name = getDeveloperFocus)]
    pub fn get_developer_focus(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        json.push('{');
        write_focus_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns co-change modularity / DSM analysis as JSON.
    ///
    /// Measures whether co-changing files respect directory boundaries.
    /// High cross-module coupling indicates architectural erosion
    /// (Silva et al. 2014).
    #[wasm_bindgen(js_name = getModularity)]
    pub fn get_modularity(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(512);
        json.push('{');
        write_modularity_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns sociotechnical congruence analysis as JSON.
    ///
    /// Measures alignment between who SHOULD coordinate (from technical
    /// dependencies) and who ACTUALLY does (from shared files).
    /// Conway's Law quantified (Cataldo et al. 2008).
    #[wasm_bindgen(js_name = getCongruence)]
    pub fn get_congruence(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(512);
        json.push('{');
        write_congruence_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns file survival analysis (Kaplan-Meier estimator) as JSON.
    ///
    /// Estimates how long files survive before deletion using the
    /// gold-standard survival analysis technique from biostatistics
    /// (Cito et al. 2021).
    #[wasm_bindgen(js_name = getFileSurvival)]
    pub fn get_file_survival(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_survival_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns developer collaboration network analysis as JSON.
    ///
    /// Builds and analyzes the co-authorship network: density, components,
    /// betweenness centrality, and clustering (Begel et al. 2023).
    #[wasm_bindgen(js_name = getDeveloperNetwork)]
    pub fn get_developer_network(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_network_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns developer experience scores (Mockus & Votta 2000).
    #[wasm_bindgen(js_name = getDeveloperExperience)]
    pub fn get_developer_experience(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_developer_experience_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns per-file ownership fragmentation / Gini (Bird et al. 2011).
    #[wasm_bindgen(js_name = getOwnershipFragmentation)]
    pub fn get_ownership_fragmentation(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_ownership_fragmentation_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns release rhythm analysis (Khomh et al. 2012).
    #[wasm_bindgen(js_name = getReleaseRhythm)]
    pub fn get_release_rhythm(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(512);
        json.push('{');
        write_release_rhythm_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns per-directory knowledge distribution entropy (Constantinou & Mens 2017).
    #[wasm_bindgen(js_name = getKnowledgeDistribution)]
    pub fn get_knowledge_distribution(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_knowledge_distribution_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns code churn volatility per file (Nagappan & Ball 2005).
    #[wasm_bindgen(js_name = getChurnVolatility)]
    pub fn get_churn_volatility(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_churn_volatility_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns enhanced truck factor via DOA model (Avelino et al. 2016).
    #[wasm_bindgen(js_name = getTruckFactor)]
    pub fn get_truck_factor(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_truck_factor_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns developer turnover impact analysis (Mockus 2009).
    #[wasm_bindgen(js_name = getTurnoverImpact)]
    pub fn get_turnover_impact(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_turnover_impact_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns per-commit complexity / tangled change scores (Herzig & Zeller 2013).
    #[wasm_bindgen(js_name = getCommitComplexity)]
    pub fn get_commit_complexity(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        json.push('{');
        write_commit_complexity_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns defect-introducing change patterns (Kim et al. 2008).
    #[wasm_bindgen(js_name = getDefectPatterns)]
    pub fn get_defect_patterns(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(1024);
        json.push('{');
        write_defect_patterns_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns language/technology distribution by file extension.
    #[wasm_bindgen(js_name = getTechDistribution)]
    pub fn get_tech_distribution(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        json.push('{');
        write_tech_distribution_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns commit activity heatmap (day-of-week × hour-of-day grid).
    #[wasm_bindgen(js_name = getActivityHeatmap)]
    pub fn get_activity_heatmap(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(4096);
        json.push('{');
        write_activity_heatmap_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns developer technology expertise profiles.
    #[wasm_bindgen(js_name = getTechExpertise)]
    pub fn get_tech_expertise(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        json.push('{');
        write_tech_expertise_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    // ========================================================================
    // Intelligence tab metrics (Session 7: novel analytical lenses)
    // ========================================================================

    /// Returns contextual complexity (working set size) analysis as JSON.
    ///
    /// For each file, computes the number of other files a developer must
    /// simultaneously understand to safely modify it.
    ///
    /// # Academic Citations
    /// - Bavota et al. (ICSM 2013): structural-semantic coupling
    /// - Gall et al. (ICSE 1998): logical coupling from co-changes
    /// - Denning (CACM 1968): working set model
    #[wasm_bindgen(js_name = getContextualComplexity)]
    pub fn get_contextual_complexity(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        json.push('{');
        write_contextual_complexity_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns commit cohesion index analysis as JSON.
    ///
    /// Measures whether commits are atomic (tightly related changes) or tangled.
    ///
    /// # Academic Citations
    /// - Herzig & Zeller (ICSE 2013): tangled commits
    /// - Kirinuki et al. (SANER 2014): untangling changes
    #[wasm_bindgen(js_name = getCommitCohesion)]
    pub fn get_commit_cohesion(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        json.push('{');
        write_commit_cohesion_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns change propagation prediction as JSON.
    ///
    /// Predicts which files need concurrent modification based on
    /// historical co-change patterns and transitive cascade analysis.
    ///
    /// # Academic Citations
    /// - Ying et al. (MSR 2004): change propagation
    /// - Hassan & Holt (ICSM 2004): predictive change coupling
    #[wasm_bindgen(js_name = getChangePropagation)]
    pub fn get_change_propagation(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        json.push('{');
        write_change_propagation_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns commit message entropy analysis as JSON.
    ///
    /// Measures the information density and quality of commit messages
    /// using Shannon entropy and cross-entropy.
    ///
    /// # Academic Citations
    /// - Dyer et al. (MSR 2013): commit message mining
    /// - Hindle et al. (ICSE 2012): naturalness of code
    #[wasm_bindgen(js_name = getCommitMessageEntropy)]
    pub fn get_commit_message_entropy(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        json.push('{');
        write_commit_message_entropy_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns knowledge half-life analysis as JSON.
    ///
    /// Models exponential knowledge decay with per-file adaptive decay rates.
    ///
    /// # Academic Citations
    /// - Fritz et al. (ICSE 2010): degree-of-knowledge model
    /// - Robillard et al. (IEEE Software 2014): developer memory
    /// - Ebbinghaus (1885): forgetting curve
    #[wasm_bindgen(js_name = getKnowledgeHalfLife)]
    pub fn get_knowledge_half_life(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(4096);
        json.push('{');
        write_knowledge_half_life_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns architectural drift index analysis as JSON.
    ///
    /// Measures divergence between directory structure and co-change clusters
    /// using Normalized Mutual Information (NMI).
    ///
    /// # Academic Citations
    /// - Garcia et al. (WICSA 2009): drift detection
    /// - Maqbool & Babri (JSS 2007): hierarchical clustering comparison
    /// - Raghavan et al. (Phys Rev 2007): label propagation
    #[wasm_bindgen(js_name = getArchitecturalDrift)]
    pub fn get_architectural_drift(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(4096);
        json.push('{');
        write_architectural_drift_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }

    /// Returns succession readiness analysis as JSON.
    ///
    /// For each file, scores how prepared the team is for the primary
    /// contributor to become unavailable.
    ///
    /// # Academic Citations
    /// - Ricca et al. (JSS 2011): developer succession
    /// - Rigby & Bird (FSE 2013): knowledge distribution
    #[wasm_bindgen(js_name = getSuccessionReadiness)]
    pub fn get_succession_readiness(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(4096);
        json.push('{');
        write_succession_readiness_json_standalone(&mut json, report);
        json.push('}');
        Some(json)
    }
}

// ============================================================================
// InsightsIndex API: Per-entity O(1) metric lookups
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Returns aggregated academic metrics for a specific file as JSON.
    ///
    /// Performs O(1) lookup from the cached insights index (computed at load time).
    /// Returns `null` if no commits are loaded or the file is not found.
    ///
    /// # Academic Citations
    ///
    /// The returned metrics aggregate findings from:
    /// - Nagappan & Ball (ICSE 2005): hotspot score
    /// - Bird et al. (ICSE 2011): ownership concentration
    /// - Eyolfson et al. (MSR 2011): circadian risk
    /// - Rigby & Bird (FSE 2013): knowledge entropy
    /// - D'Ambros et al. (TSE 2009): coupling degree
    /// - Godfrey & Tu (ICSM 2000): lifecycle stage
    #[wasm_bindgen(js_name = getFileMetrics)]
    pub fn get_file_metrics(&self, path: &str) -> Option<String> {
        let index = self.cached_index.as_ref()?;
        let fm = index.file_metrics(path)?;
        Some(format_file_metrics_json(fm))
    }

    /// Returns aggregated academic metrics for a specific developer as JSON.
    ///
    /// Performs O(1) lookup from the cached insights index (computed at load time).
    /// Returns `null` if no commits are loaded or the author is not found.
    ///
    /// # Academic Citations
    ///
    /// The returned metrics aggregate findings from:
    /// - Mockus et al. (TSE 2002): developer profiles (core/peripheral)
    /// - Eyolfson et al. (MSR 2014): commit cadence
    /// - Meneely & Williams (FSE 2009): network centrality
    /// - Posnett et al. (ICSE 2013): developer focus
    #[wasm_bindgen(js_name = getUserMetrics)]
    pub fn get_user_metrics(&self, author: &str) -> Option<String> {
        let index = self.cached_index.as_ref()?;
        let um = index.user_metrics(author)?;
        Some(format_user_metrics_json(um))
    }

    /// Returns the complete insights index summary as JSON.
    ///
    /// Contains aggregate counts: total files, total users, knowledge silos,
    /// contributor profile distribution, max hotspot score.
    #[wasm_bindgen(js_name = getInsightsIndexSummary)]
    pub fn get_insights_index_summary(&self) -> Option<String> {
        let index = self.cached_index.as_ref()?;
        Some(format_index_summary_json(index.summary()))
    }

    /// Returns all per-file metrics as a JSON array.
    ///
    /// Each element contains the file path and its aggregated academic metrics.
    /// Useful for bulk visualization (e.g., coloring all files by hotspot score).
    #[wasm_bindgen(js_name = getAllFileMetrics)]
    pub fn get_all_file_metrics(&self) -> Option<String> {
        let index = self.cached_index.as_ref()?;

        let mut json = String::with_capacity(index.file_count() * 200);
        json.push('[');
        for (i, (path, fm)) in index.iter_files().enumerate() {
            if i > 0 {
                json.push(',');
            }
            let _ = write!(json, r#"{{"path":"{}","metrics":"#, escape_json(path));
            json.push_str(&format_file_metrics_json(fm));
            json.push('}');
        }
        json.push(']');
        Some(json)
    }

    /// Returns all per-user metrics as a JSON array.
    ///
    /// Each element contains the author name and their aggregated academic metrics.
    #[wasm_bindgen(js_name = getAllUserMetrics)]
    pub fn get_all_user_metrics(&self) -> Option<String> {
        let index = self.cached_index.as_ref()?;

        let mut json = String::with_capacity(index.user_count() * 200);
        json.push('[');
        for (i, (author, um)) in index.iter_users().enumerate() {
            if i > 0 {
                json.push(',');
            }
            let _ = write!(json, r#"{{"author":"{}","metrics":"#, escape_json(author));
            json.push_str(&format_user_metrics_json(um));
            json.push('}');
        }
        json.push(']');
        Some(json)
    }

    // ========================================================================
    // Session 8: Intelligence tab M9-M32 WASM API methods
    // ========================================================================

    /// Returns code reviewer recommendations as JSON (M9).
    #[wasm_bindgen(js_name = getReviewerRecommendation)]
    pub fn get_reviewer_recommendation(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        write_reviewer_recommendation_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns review response time distribution as JSON (M19).
    #[wasm_bindgen(js_name = getReviewResponse)]
    pub fn get_review_response(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        write_review_response_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns contributor onboarding velocity as JSON (M20).
    #[wasm_bindgen(js_name = getOnboardingVelocity)]
    pub fn get_onboarding_velocity(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        write_onboarding_velocity_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns interface stability scores as JSON (M23).
    #[wasm_bindgen(js_name = getInterfaceStability)]
    pub fn get_interface_stability(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        write_interface_stability_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns technical debt velocity as JSON (M25).
    #[wasm_bindgen(js_name = getTechDebtVelocity)]
    pub fn get_tech_debt_velocity(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        write_tech_debt_velocity_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns development focus drift as JSON (M30).
    #[wasm_bindgen(js_name = getFocusDrift)]
    pub fn get_focus_drift(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        write_focus_drift_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns AI-assisted change detection as JSON (M31).
    #[wasm_bindgen(js_name = getAiChangeDetection)]
    pub fn get_ai_change_detection(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        write_ai_change_detection_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns knowledge Gini coefficient as JSON (M10).
    #[wasm_bindgen(js_name = getKnowledgeGini)]
    pub fn get_knowledge_gini(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        write_knowledge_gini_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns expertise profiles as JSON (M11).
    #[wasm_bindgen(js_name = getExpertiseProfile)]
    pub fn get_expertise_profile(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        write_expertise_profile_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns cognitive load estimates as JSON (M32).
    #[wasm_bindgen(js_name = getCognitiveLoad)]
    pub fn get_cognitive_load(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        write_cognitive_load_json_standalone(&mut json, report);
        Some(json)
    }

    // ========================================================================
    // Strategic tab: next-generation git mining insights
    // ========================================================================

    /// Returns DORA proxy metrics as JSON (Forsgren et al. 2018).
    ///
    /// Includes merge frequency, branch duration, revert ratio, recovery time,
    /// rework ratio, performance tier classification, and 4-week trend windows.
    #[wasm_bindgen(js_name = getDoraProxy)]
    pub fn get_dora_proxy(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        write_dora_proxy_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns knowledge currency index as JSON (Fritz et al. 2010, Ebbinghaus 1885).
    ///
    /// Per-file knowledge freshness combining recency, decay, refreshes, and active contributors.
    #[wasm_bindgen(js_name = getKnowledgeCurrency)]
    pub fn get_knowledge_currency(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(4096);
        write_knowledge_currency_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns team rhythm synchronization as JSON (Fisher 1993, Eyolfson et al. 2011).
    ///
    /// Circular statistics on commit hour distributions with team sync scoring.
    #[wasm_bindgen(js_name = getTeamRhythm)]
    pub fn get_team_rhythm(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(2048);
        write_team_rhythm_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns commit coherence scoring as JSON (Herzig & Zeller 2013).
    ///
    /// Per-commit tangled change detection with atomicity index and developer breakdown.
    #[wasm_bindgen(js_name = getCommitCoherence)]
    pub fn get_commit_coherence(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(4096);
        write_commit_coherence_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns Markov chain next-file prediction as JSON (Hassan & Holt 2004).
    ///
    /// Transition probability matrix for predicting which files change together.
    #[wasm_bindgen(js_name = getMarkovPrediction)]
    pub fn get_markov_prediction(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(4096);
        write_markov_prediction_json_standalone(&mut json, report);
        Some(json)
    }

    /// Returns composite repository health score as JSON (Borg et al. 2024).
    ///
    /// Weighted health score [0-100] with letter grade and dimension breakdown.
    #[wasm_bindgen(js_name = getRepoHealth)]
    pub fn get_repo_health(&self) -> Option<String> {
        let report = self.cached_report.as_ref()?;
        let mut json = String::with_capacity(512);
        write_repo_health_json_standalone(&mut json, report);
        Some(json)
    }
}

// ============================================================================
// InsightsIndex JSON serialization
// ============================================================================

/// Formats a single file's metrics as JSON.
fn format_file_metrics_json(fm: &rource_core::insights::index::FileMetrics) -> String {
    let mut json = String::with_capacity(512);
    let _ = write!(
        json,
        r#"{{"hotspotScore":{:.4},"hotspotRank":{},"totalChanges":{},"contributorCount":{},"topOwnerShare":{:.4},"topOwner":"{}","lifecycleStage":"{}","ageDays":{:.1},"burstCount":{},"burstRiskScore":{:.4},"circadianRisk":{:.4},"knowledgeEntropy":{:.4},"isKnowledgeSilo":{},"diffusionScore":{:.4},"couplingDegree":{},"minorContributors":{},"majorContributors":{},"ownershipGini":{:.4},"defectScore":{:.4},"churnCv":{:.4},"defectPatternScore":{:.4},"knowledgeCurrency":{:.4}}}"#,
        fm.hotspot_score,
        fm.hotspot_rank
            .map_or_else(|| "null".to_string(), |r| r.to_string()),
        fm.total_changes,
        fm.contributor_count,
        fm.top_owner_share,
        escape_json(&fm.top_owner),
        fm.lifecycle_stage,
        fm.age_days,
        fm.burst_count,
        fm.burst_risk_score,
        fm.circadian_risk,
        fm.knowledge_entropy,
        fm.is_knowledge_silo,
        fm.diffusion_score,
        fm.coupling_degree,
        fm.minor_contributors,
        fm.major_contributors,
        fm.ownership_gini,
        fm.defect_score,
        fm.churn_cv,
        fm.defect_pattern_score,
        fm.knowledge_currency,
    );
    json
}

/// Formats a single user's metrics as JSON.
fn format_user_metrics_json(um: &rource_core::insights::index::UserMetrics) -> String {
    let mut json = String::with_capacity(384);
    let _ = write!(
        json,
        r#"{{"commitCount":{},"profileType":"{}","uniqueFiles":{},"avgFilesPerCommit":{:.2},"activeSpanDays":{:.1},"cadenceType":"{}","meanCommitInterval":{:.1},"focusScore":{:.4},"networkDegree":{},"networkBetweenness":{:.4},"circadianAvgRisk":{:.4},"directoriesTouched":{},"experienceScore":{:.4},"tenureDays":{:.1},"truckFactorDoa":{:.4},"soleExpertCount":{},"isDeparted":{},"rhythmType":"{}","meanCoherence":{:.4}}}"#,
        um.commit_count,
        um.profile_type,
        um.unique_files,
        um.avg_files_per_commit,
        um.active_span_days,
        um.cadence_type,
        um.mean_commit_interval,
        um.focus_score,
        um.network_degree,
        um.network_betweenness,
        um.circadian_avg_risk,
        um.directories_touched,
        um.experience_score,
        um.tenure_days,
        um.truck_factor_doa,
        um.sole_expert_count,
        um.is_departed,
        um.rhythm_type,
        um.mean_coherence,
    );
    json
}

/// Formats the index summary as JSON.
fn format_index_summary_json(s: &rource_core::insights::index::IndexSummary) -> String {
    let mut json = String::with_capacity(256);
    let _ = write!(
        json,
        r#"{{"totalFiles":{},"totalUsers":{},"knowledgeSiloCount":{},"filesWithBursts":{},"coreContributorCount":{},"peripheralContributorCount":{},"driveByContributorCount":{},"maxHotspotScore":{:.4},"avgContributorsPerFile":{:.2}}}"#,
        s.total_files,
        s.total_users,
        s.knowledge_silo_count,
        s.files_with_bursts,
        s.core_contributor_count,
        s.peripheral_contributor_count,
        s.drive_by_contributor_count,
        s.max_hotspot_score,
        s.avg_contributors_per_file,
    );
    json
}

/// Standalone growth JSON (without leading comma for top-level endpoints).
fn write_growth_json_standalone(json: &mut String, report: &InsightsReport) {
    // Reuse the section writer but strip the leading comma
    let mut buf = String::new();
    write_growth_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone work-type JSON.
fn write_work_type_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_work_type_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone cadence JSON.
fn write_cadence_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_cadence_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone knowledge JSON.
fn write_knowledge_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_knowledge_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone profiles JSON.
fn write_profiles_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_profiles_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone lifecycle JSON.
fn write_lifecycle_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_lifecycle_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone inequality JSON.
fn write_inequality_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_inequality_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone change entropy JSON.
fn write_change_entropy_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_change_entropy_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone circadian JSON.
fn write_circadian_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_circadian_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone change bursts JSON.
fn write_change_bursts_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_change_bursts_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone focus JSON.
fn write_focus_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_focus_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone modularity JSON.
fn write_modularity_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_modularity_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone congruence JSON.
fn write_congruence_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_congruence_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone survival JSON.
fn write_survival_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_survival_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone network JSON.
fn write_network_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_network_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

// ============================================================================
// Session 4: New Academic Metrics JSON Writers
// ============================================================================

/// Appends developer experience section to the JSON output.
fn write_developer_experience_json(json: &mut String, report: &InsightsReport) {
    let de = &report.developer_experience;
    json.push_str(",\"developerExperience\":{\"avgExperienceScore\":");
    let _ = write!(json, "{:.4}", de.avg_experience_score);
    json.push_str(",\"developers\":[");
    for (i, d) in de.developers.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","experienceScore":{:.4},"tenureDays":{:.1},"totalCommits":{},"uniqueFiles":{}}}"#,
            escape_json(&d.author),
            d.experience_score,
            d.tenure_days,
            d.total_commits,
            d.unique_files,
        );
    }
    json.push_str("]}");
}

/// Appends ownership fragmentation section to the JSON output.
fn write_ownership_fragmentation_json(json: &mut String, report: &InsightsReport) {
    let of = &report.ownership_fragmentation;
    json.push_str(",\"ownershipFragmentation\":{\"avgGini\":");
    let _ = write!(json, "{:.4}", of.avg_gini);
    let _ = write!(
        json,
        ",\"fragmentedCount\":{},\"concentratedCount\":{},\"files\":[",
        of.fragmented_count, of.concentrated_count
    );
    for (i, f) in of.files.iter().take(50).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","giniCoefficient":{:.4},"contributorCount":{},"ownershipType":"{}"}}"#,
            escape_json(&f.path),
            f.gini_coefficient,
            f.contributor_count,
            f.ownership_type,
        );
    }
    json.push_str("]}");
}

/// Appends release rhythm section to the JSON output.
fn write_release_rhythm_json(json: &mut String, report: &InsightsReport) {
    let rr = &report.release_rhythm;
    let _ = write!(
        json,
        r#","releaseRhythm":{{"avgReleaseIntervalDays":{:.1},"releaseRegularity":{:.4},"currentPhase":"{}","velocityTrend":"{}","peakCount":{},"windowCount":{}}}"#,
        rr.avg_release_interval_days,
        rr.release_regularity,
        rr.current_phase,
        rr.velocity_trend,
        rr.peaks.len(),
        rr.windows.len(),
    );
}

/// Appends knowledge distribution section to the JSON output.
fn write_knowledge_distribution_json(json: &mut String, report: &InsightsReport) {
    let kd = &report.knowledge_distribution;
    let _ = write!(
        json,
        r#","knowledgeDistribution":{{"avgNormalizedEntropy":{:.4},"concentratedCount":{},"distributedCount":{},"directories":["#,
        kd.avg_normalized_entropy, kd.concentrated_count, kd.distributed_count,
    );
    for (i, d) in kd.directories.iter().take(50).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"directory":"{}","knowledgeEntropy":{:.4},"normalizedEntropy":{:.4},"contributorCount":{},"dominantContributorShare":{:.4},"dominantContributor":"{}","totalCommits":{}}}"#,
            escape_json(&d.directory),
            d.knowledge_entropy,
            d.normalized_entropy,
            d.contributor_count,
            d.dominant_contributor_share,
            escape_json(&d.dominant_contributor),
            d.total_commits,
        );
    }
    json.push_str("]}");
}

/// Standalone writer for developer experience endpoint.
fn write_developer_experience_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_developer_experience_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for ownership fragmentation endpoint.
fn write_ownership_fragmentation_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_ownership_fragmentation_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for release rhythm endpoint.
fn write_release_rhythm_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_release_rhythm_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for knowledge distribution endpoint.
fn write_knowledge_distribution_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_knowledge_distribution_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

// ============================================================================
// Session 5: New Academic Metrics JSON Writers
// ============================================================================

/// Appends code churn volatility section to the JSON output.
fn write_churn_volatility_json(json: &mut String, report: &InsightsReport) {
    let cv = &report.churn_volatility;
    let _ = write!(
        json,
        r#","churnVolatility":{{"avgCv":{:.4},"volatileCount":{},"stableCount":{},"files":["#,
        cv.avg_cv, cv.volatile_count, cv.stable_count,
    );
    for (i, f) in cv.files.iter().take(100).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","cv":{:.4},"totalChurn":{:.2},"activeWindows":{},"volatilityClass":"{}"}}"#,
            escape_json(&f.path),
            f.cv,
            f.total_churn,
            f.active_windows,
            f.volatility_class,
        );
    }
    json.push_str("]}");
}

/// Appends enhanced truck factor section to the JSON output.
fn write_truck_factor_json(json: &mut String, report: &InsightsReport) {
    let tf = &report.truck_factor;
    let _ = write!(
        json,
        r#","truckFactor":{{"truckFactor":{},"totalFiles":{},"topDevOrphanCount":{},"singleExpertPct":{:.4},"rankedDevelopers":["#,
        tf.truck_factor, tf.total_files, tf.top_dev_orphan_count, tf.single_expert_pct,
    );
    for (i, d) in tf.ranked_developers.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"name":"{}","totalDoa":{:.4},"expertFileCount":{},"soleExpertCount":{}}}"#,
            escape_json(&d.name),
            d.total_doa,
            d.expert_file_count,
            d.sole_expert_count,
        );
    }
    json.push_str("]}");
}

/// Appends developer turnover impact section to the JSON output.
fn write_turnover_impact_json(json: &mut String, report: &InsightsReport) {
    let ti = &report.turnover_impact;
    let _ = write!(
        json,
        r#","turnoverImpact":{{"activeCount":{},"departedCount":{},"orphanRate":{:.4},"totalOrphanedFiles":{},"departedDevelopers":["#,
        ti.active_count, ti.departed_count, ti.orphan_rate, ti.total_orphaned_files,
    );
    for (i, d) in ti.departed_developers.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"name":"{}","lastCommitTs":{},"daysSinceLast":{},"ownedFiles":{},"orphanedFiles":{},"impactScore":{:.4}}}"#,
            escape_json(&d.name),
            d.last_commit_ts,
            d.days_since_last,
            d.owned_files,
            d.orphaned_files,
            d.impact_score,
        );
    }
    json.push_str("]}");
}

/// Appends commit complexity section to the JSON output.
fn write_commit_complexity_json(json: &mut String, report: &InsightsReport) {
    let cc = &report.commit_complexity;
    let _ = write!(
        json,
        r#","commitComplexity":{{"avgComplexity":{:.4},"medianComplexity":{:.4},"p95Complexity":{:.4},"tangledCount":{},"maxComplexity":{:.4},"commits":["#,
        cc.avg_complexity,
        cc.median_complexity,
        cc.p95_complexity,
        cc.tangled_count,
        cc.max_complexity,
    );
    // Top 100 most complex commits
    for (i, c) in cc.commits.iter().take(100).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"commitIdx":{},"author":"{}","timestamp":{},"fileCount":{},"dirCount":{},"actionEntropy":{:.4},"complexityScore":{:.4},"isTangled":{}}}"#,
            c.commit_idx,
            escape_json(&c.author),
            c.timestamp,
            c.file_count,
            c.dir_count,
            c.action_entropy,
            c.complexity_score,
            c.is_tangled,
        );
    }
    json.push_str("]}");
}

/// Appends defect-introducing change patterns section to the JSON output.
fn write_defect_patterns_json(json: &mut String, report: &InsightsReport) {
    let dp = &report.defect_patterns;
    let _ = write!(
        json,
        r#","defectPatterns":{{"largeCommitCount":{},"burstAfterLargeCount":{},"avgScore":{:.4},"highRiskCount":{},"files":["#,
        dp.large_commit_count, dp.burst_after_large_count, dp.avg_score, dp.high_risk_count,
    );
    for (i, f) in dp.files.iter().take(100).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","burstAfterLarge":{},"largeCommitAppearances":{},"score":{:.4},"totalEdits":{}}}"#,
            escape_json(&f.path),
            f.burst_after_large,
            f.large_commit_appearances,
            f.score,
            f.total_edits,
        );
    }
    json.push_str("]}");
}

/// Standalone writer for churn volatility endpoint.
fn write_churn_volatility_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_churn_volatility_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for truck factor endpoint.
fn write_truck_factor_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_truck_factor_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for turnover impact endpoint.
fn write_turnover_impact_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_turnover_impact_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for commit complexity endpoint.
fn write_commit_complexity_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_commit_complexity_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for defect patterns endpoint.
fn write_defect_patterns_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_defect_patterns_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

// ============================================================================
// Session 6: Language Distribution, Activity Heatmap, Tech Expertise
// ============================================================================

/// Appends language/technology distribution section to the JSON output.
fn write_tech_distribution_json(json: &mut String, report: &InsightsReport) {
    let td = &report.tech_distribution;
    let _ = write!(
        json,
        r#","techDistribution":{{"totalFiles":{},"languageCount":{},"primaryLanguage":"{}","primaryLanguagePct":{:.2},"languages":["#,
        td.total_files,
        td.language_count,
        escape_json(&td.primary_language),
        td.primary_language_pct,
    );
    for (i, lang) in td.languages.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"name":"{}","fileCount":{},"percentage":{:.2},"extensions":["#,
            escape_json(&lang.name),
            lang.file_count,
            lang.percentage,
        );
        for (j, ext) in lang.extensions.iter().enumerate() {
            if j > 0 {
                json.push(',');
            }
            let _ = write!(json, r#""{}""#, escape_json(ext));
        }
        json.push_str("]}");
    }
    json.push_str("]}");
}

/// Appends commit activity heatmap section to the JSON output.
fn write_activity_heatmap_json(json: &mut String, report: &InsightsReport) {
    use rource_core::insights::activity_heatmap::day_name;

    let hm = &report.activity_heatmap;
    let _ = write!(
        json,
        r#","activityHeatmap":{{"totalCommits":{},"peakDay":{},"peakDayName":"{}","peakHour":{},"peakCount":{},"workHoursPct":{:.2},"weekendPct":{:.2},"grid":["#,
        hm.total_commits,
        hm.peak_day,
        day_name(hm.peak_day),
        hm.peak_hour,
        hm.peak_count,
        hm.work_hours_pct,
        hm.weekend_pct,
    );
    for (d, day_row) in hm.grid.iter().enumerate() {
        if d > 0 {
            json.push(',');
        }
        json.push('[');
        for (h, &count) in day_row.iter().enumerate() {
            if h > 0 {
                json.push(',');
            }
            let _ = write!(json, "{count}");
        }
        json.push(']');
    }
    json.push_str("]}");
}

/// Appends developer technology expertise section to the JSON output.
fn write_tech_expertise_json(json: &mut String, report: &InsightsReport) {
    let te = &report.tech_expertise;
    let _ = write!(
        json,
        r#","techExpertise":{{"developerCount":{},"dominantTech":"{}","developers":["#,
        te.developer_count,
        escape_json(&te.dominant_tech),
    );
    for (i, dev) in te.developers.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"name":"{}","totalCommits":{},"techCount":{},"primaryTech":"{}","technologies":["#,
            escape_json(&dev.name),
            dev.total_commits,
            dev.tech_count,
            escape_json(&dev.primary_tech),
        );
        for (j, tech) in dev.technologies.iter().enumerate() {
            if j > 0 {
                json.push(',');
            }
            let _ = write!(
                json,
                r#"{{"tech":"{}","commits":{},"percentage":{:.2}}}"#,
                escape_json(&tech.tech),
                tech.commits,
                tech.percentage,
            );
        }
        json.push_str("]}");
    }
    json.push_str("]}");
}

/// Standalone writer for tech distribution endpoint.
fn write_tech_distribution_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_tech_distribution_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for activity heatmap endpoint.
fn write_activity_heatmap_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_activity_heatmap_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for tech expertise endpoint.
fn write_tech_expertise_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_tech_expertise_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

// ============================================================================
// Intelligence tab write functions (Session 7)
// ============================================================================

/// Writes contextual complexity data as a JSON field.
fn write_contextual_complexity_json(json: &mut String, report: &InsightsReport) {
    json.push_str(",\"contextualComplexity\":{");
    let cc = &report.contextual_complexity;
    let _ = write!(
        json,
        r#""avgContextSize":{:.2},"threshold":{:.4},"filesWithContext":{},"maxContextSize":{},"files":["#,
        cc.avg_context_size, cc.threshold, cc.files_with_context, cc.max_context_size
    );
    for (i, f) in cc.files.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","contextSize":{},"weightedComplexity":{:.4},"normalizedComplexity":{:.6},"contextFiles":["#,
            escape_json(&f.path),
            f.context_size,
            f.weighted_complexity,
            f.normalized_complexity
        );
        for (j, (g, conf)) in f.context_files.iter().enumerate() {
            if j > 0 {
                json.push(',');
            }
            let _ = write!(json, r#"["{}",{:.4}]"#, escape_json(g), conf);
        }
        json.push_str("]}");
    }
    json.push_str("]}");
}

/// Writes commit cohesion data as a JSON field.
fn write_commit_cohesion_json(json: &mut String, report: &InsightsReport) {
    json.push_str(",\"commitCohesion\":{");
    let cc = &report.commit_cohesion;
    let _ = write!(
        json,
        r#""medianCohesion":{:.4},"tangledRatio":{:.4},"totalAnalyzed":{},"commits":["#,
        cc.median_cohesion, cc.tangled_ratio, cc.total_analyzed
    );
    for (i, c) in cc.commits.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","timestamp":{},"cohesion":{:.4},"fileCount":{}}}"#,
            escape_json(&c.author),
            c.timestamp,
            c.cohesion,
            c.file_count
        );
    }
    json.push_str("],\"developerCohesion\":[");
    for (i, d) in cc.developer_cohesion.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","medianCohesion":{:.4},"commitCount":{},"tangledRatio":{:.4}}}"#,
            escape_json(&d.author),
            d.median_cohesion,
            d.commit_count,
            d.tangled_ratio
        );
    }
    json.push_str("]}");
}

/// Writes change propagation data as a JSON field.
fn write_change_propagation_json(json: &mut String, report: &InsightsReport) {
    json.push_str(",\"changePropagation\":{");
    let cp = &report.change_propagation;
    let _ = write!(
        json,
        r#""avgRiskScore":{:.4},"avgExpectedDepth":{:.2},"cascadeCount":{},"files":["#,
        cp.avg_risk_score, cp.avg_expected_depth, cp.cascade_count
    );
    for (i, f) in cp.files.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","riskScore":{:.4},"expectedDepth":{:.2},"predictions":["#,
            escape_json(&f.path),
            f.risk_score,
            f.expected_depth
        );
        for (j, (dep, conf)) in f.predictions.iter().enumerate() {
            if j > 0 {
                json.push(',');
            }
            let _ = write!(json, r#"["{}",{:.4}]"#, escape_json(dep), conf);
        }
        json.push_str("],\"depthCounts\":[");
        for (j, count) in f.depth_counts.iter().enumerate() {
            if j > 0 {
                json.push(',');
            }
            let _ = write!(json, "{count}");
        }
        json.push_str("]}");
    }
    json.push_str("]}");
}

/// Writes commit message entropy data as a JSON field.
fn write_commit_message_entropy_json(json: &mut String, report: &InsightsReport) {
    json.push_str(",\"commitMessageEntropy\":{");
    let cme = &report.commit_message_entropy;
    let _ = write!(
        json,
        r#""medianInfoDensity":{:.4},"lowInfoRatio":{:.4},"avgCrossEntropy":{:.4},"totalAnalyzed":{},"noMessageCount":{},"commits":["#,
        cme.median_info_density,
        cme.low_info_ratio,
        cme.avg_cross_entropy,
        cme.total_analyzed,
        cme.no_message_count
    );
    for (i, c) in cme.commits.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","timestamp":{},"tokenEntropy":{:.4},"informationDensity":{:.4},"crossEntropy":{:.4},"isLowInfo":{},"fileCount":{},"uniqueTokens":{},"totalTokens":{}}}"#,
            escape_json(&c.author),
            c.timestamp,
            c.token_entropy,
            c.information_density,
            c.cross_entropy,
            c.is_low_info,
            c.file_count,
            c.unique_tokens,
            c.total_tokens
        );
    }
    json.push_str("],\"developerQuality\":[");
    for (i, d) in cme.developer_quality.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","medianInfoDensity":{:.4},"lowInfoRatio":{:.4},"commitCount":{}}}"#,
            escape_json(&d.author),
            d.median_info_density,
            d.low_info_ratio,
            d.commit_count
        );
    }
    json.push_str("]}");
}

/// Writes knowledge half-life data as a JSON field.
fn write_knowledge_half_life_json(json: &mut String, report: &InsightsReport) {
    json.push_str(",\"knowledgeHalfLife\":{");
    let khl = &report.knowledge_half_life;
    let _ = write!(
        json,
        r#""teamKnowledgeFreshness":{:.4},"cliffCount":{},"medianHalfLifeDays":{:.2},"minHalfLifeDays":{:.2},"maxHalfLifeDays":{:.2},"files":["#,
        khl.team_knowledge_freshness,
        khl.cliff_count,
        khl.median_half_life_days,
        khl.min_half_life_days,
        khl.max_half_life_days
    );
    for (i, f) in khl.files.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","knowledgeFreshness":{:.4},"topExpert":"{}","halfLifeDays":{:.2},"isKnowledgeCliff":{},"experts":["#,
            escape_json(&f.path),
            f.knowledge_freshness,
            escape_json(&f.top_expert),
            f.half_life_days,
            f.is_knowledge_cliff
        );
        for (j, (author, k)) in f.experts.iter().enumerate() {
            if j > 0 {
                json.push(',');
            }
            let _ = write!(json, r#"["{}",{:.4}]"#, escape_json(author), k);
        }
        json.push_str("]}");
    }
    json.push_str("],\"developers\":[");
    for (i, d) in khl.developers.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","knowledgeMass":{:.4},"cliffFileCount":{},"topExpertCount":{}}}"#,
            escape_json(&d.author),
            d.knowledge_mass,
            d.cliff_file_count,
            d.top_expert_count
        );
    }
    json.push_str("]}");
}

/// Writes architectural drift data as a JSON field.
fn write_architectural_drift_json(json: &mut String, report: &InsightsReport) {
    json.push_str(",\"architecturalDrift\":{");
    let ad = &report.architectural_drift;
    let _ = write!(
        json,
        r#""driftIndex":{:.4},"nmi":{:.4},"clusterCount":{},"misplacedCount":{},"directories":["#,
        ad.drift_index, ad.nmi, ad.cluster_count, ad.misplaced_count
    );
    for (i, d) in ad.directories.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"directory":"{}","clusterCount":{},"dominantClusterPct":{:.4},"fileCount":{}}}"#,
            escape_json(&d.directory),
            d.cluster_count,
            d.dominant_cluster_pct,
            d.file_count
        );
    }
    json.push_str("],\"ghostModules\":[");
    for (i, gm) in ad.ghost_modules.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(json, r#"{{"clusterId":{},"directories":["#, gm.cluster_id);
        for (j, dir) in gm.directories.iter().enumerate() {
            if j > 0 {
                json.push(',');
            }
            let _ = write!(json, r#""{}""#, escape_json(dir));
        }
        json.push_str("],\"files\":[");
        for (j, file) in gm.files.iter().enumerate() {
            if j > 0 {
                json.push(',');
            }
            let _ = write!(json, r#""{}""#, escape_json(file));
        }
        json.push_str("]}");
    }
    json.push_str("],\"files\":[");
    for (i, f) in ad.files.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","directory":"{}","clusterId":{},"isMisplaced":{}}}"#,
            escape_json(&f.path),
            escape_json(&f.directory),
            f.cluster_id,
            f.is_misplaced
        );
    }
    json.push_str("]}");
}

/// Writes succession readiness data as a JSON field.
fn write_succession_readiness_json(json: &mut String, report: &InsightsReport) {
    json.push_str(",\"successionReadiness\":{");
    let sr = &report.succession_readiness;
    let _ = write!(
        json,
        r#""codebaseReadiness":{:.4},"singlePointOfFailureCount":{},"adequateSuccessionCount":{},"totalFiles":{},"files":["#,
        sr.codebase_readiness,
        sr.single_point_of_failure_count,
        sr.adequate_succession_count,
        sr.total_files
    );
    for (i, f) in sr.files.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","primaryContributor":"{}","readiness":{:.4},"bestSuccessor":{},"bestSuccessorScore":{:.4},"successionGap":{:.4},"candidates":["#,
            escape_json(&f.path),
            escape_json(&f.primary_contributor),
            f.readiness,
            f.best_successor.as_ref().map_or_else(
                || "null".to_string(),
                |s| {
                    let escaped = escape_json(s);
                    format!("\"{escaped}\"")
                }
            ),
            f.best_successor_score,
            f.succession_gap
        );
        for (j, (name, score)) in f.candidates.iter().enumerate() {
            if j > 0 {
                json.push(',');
            }
            let _ = write!(json, r#"["{}",{:.4}]"#, escape_json(name), score);
        }
        json.push_str("]}");
    }
    json.push_str("]}");
}

// Standalone variants for individual endpoints

/// Standalone writer for contextual complexity endpoint.
fn write_contextual_complexity_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_contextual_complexity_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for commit cohesion endpoint.
fn write_commit_cohesion_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_commit_cohesion_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for change propagation endpoint.
fn write_change_propagation_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_change_propagation_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for commit message entropy endpoint.
fn write_commit_message_entropy_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_commit_message_entropy_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for knowledge half-life endpoint.
fn write_knowledge_half_life_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_knowledge_half_life_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for architectural drift endpoint.
fn write_architectural_drift_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_architectural_drift_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Standalone writer for succession readiness endpoint.
fn write_succession_readiness_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_succession_readiness_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

// ============================================================================
// Session 8 Intelligence tab JSON writers (M9-M32)
// ============================================================================

/// Appends reviewer recommendation data to JSON.
fn write_reviewer_recommendation_json(json: &mut String, report: &InsightsReport) {
    let rr = &report.reviewer_recommendation;
    json.push_str(",\"reviewerRecommendation\":{\"files\":[");
    for (i, f) in rr.files.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        json.push_str("{\"path\":\"");
        json.push_str(&escape_json(&f.path));
        json.push_str("\",\"reviewers\":[");
        for (j, r) in f.reviewers.iter().enumerate() {
            if j > 0 {
                json.push(',');
            }
            let _ = write!(
                json,
                r#"{{"author":"{}","score":{:.4},"ownership":{:.4},"recency":{:.4},"reviewFreq":{:.4}}}"#,
                escape_json(&r.author),
                r.score,
                r.ownership,
                r.recency,
                r.review_freq,
            );
        }
        json.push_str("]}");
    }
    let _ = write!(
        json,
        r#"],"avgReviewersPerFile":{:.2},"singleReviewerCount":{},"totalAnalyzed":{}}}"#,
        rr.avg_reviewers_per_file, rr.single_reviewer_count, rr.total_analyzed,
    );
}

/// Appends review response time data to JSON.
fn write_review_response_json(json: &mut String, report: &InsightsReport) {
    let rr = &report.review_response;
    json.push_str(",\"reviewResponse\":{\"files\":[");
    for (i, f) in rr.files.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","p50Hours":{:.2},"p90Hours":{:.2},"reviewCount":{},"reviewerCount":{}}}"#,
            escape_json(&f.path),
            f.p50_hours,
            f.p90_hours,
            f.review_count,
            f.reviewer_count,
        );
    }
    let _ = write!(
        json,
        r#"],"teamP50Hours":{:.2},"teamP90Hours":{:.2},"slowReviewCount":{},"totalReviews":{}}}"#,
        rr.team_p50_hours, rr.team_p90_hours, rr.slow_review_count, rr.total_reviews,
    );
}

/// Appends onboarding velocity data to JSON.
fn write_onboarding_velocity_json(json: &mut String, report: &InsightsReport) {
    let ov = &report.onboarding_velocity;
    json.push_str(",\"onboardingVelocity\":{\"developers\":[");
    for (i, d) in ov.developers.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","type":"{}","totalCommits":{},"uniqueFiles":{},"activeSpanDays":{:.1},"week14Commits":{},"week58Commits":{}}}"#,
            escape_json(&d.author),
            d.onboarding_type.label(),
            d.total_commits,
            d.unique_files,
            d.active_span_days,
            d.week1_4_commits,
            d.week5_8_commits,
        );
    }
    let _ = write!(
        json,
        r#"],"oneShotCount":{},"fastRampCount":{},"slowRampCount":{},"sustainedCount":{},"medianDaysToCore":{:.1}}}"#,
        ov.one_shot_count,
        ov.fast_ramp_count,
        ov.slow_ramp_count,
        ov.sustained_count,
        ov.median_days_to_core,
    );
}

/// Appends interface stability data to JSON.
fn write_interface_stability_json(json: &mut String, report: &InsightsReport) {
    let is = &report.interface_stability;
    json.push_str(",\"interfaceStability\":{\"directories\":[");
    for (i, d) in is.directories.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"directory":"{}","stability":{:.4},"totalChanges":{},"crossBoundaryChanges":{},"externalContributorCount":{},"fileCount":{}}}"#,
            escape_json(&d.directory),
            d.stability,
            d.total_changes,
            d.cross_boundary_changes,
            d.external_contributor_count,
            d.file_count,
        );
    }
    let _ = write!(
        json,
        r#"],"avgStability":{:.4},"volatileCount":{},"stableCount":{},"totalAnalyzed":{}}}"#,
        is.avg_stability, is.volatile_count, is.stable_count, is.total_analyzed,
    );
}

/// Appends technical debt velocity data to JSON.
fn write_tech_debt_velocity_json(json: &mut String, report: &InsightsReport) {
    let td = &report.tech_debt_velocity;
    json.push_str(",\"techDebtVelocity\":{\"windows\":[");
    for (i, w) in td.windows.iter().take(24).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"start":{},"end":{},"maintenanceRatio":{:.4},"featureRatio":{:.4},"debtReductionRatio":{:.4},"totalCommits":{}}}"#,
            w.start,
            w.end,
            w.maintenance_ratio,
            w.feature_ratio,
            w.debt_reduction_ratio,
            w.total_commits,
        );
    }
    let _ = write!(
        json,
        r#"],"trend":"{}","velocitySlope":{:.6},"overallMaintenanceRatio":{:.4},"overallFeatureRatio":{:.4},"overallDebtReductionRatio":{:.4},"totalClassified":{}}}"#,
        td.trend.label(),
        td.velocity_slope,
        td.overall_maintenance_ratio,
        td.overall_feature_ratio,
        td.overall_debt_reduction_ratio,
        td.total_classified,
    );
}

/// Appends focus drift data to JSON.
fn write_focus_drift_json(json: &mut String, report: &InsightsReport) {
    let fd = &report.focus_drift;
    json.push_str(",\"focusDrift\":{\"directories\":[");
    for (i, d) in fd.directories.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"directory":"{}","trend":"{}","currentShare":{:.4},"previousShare":{:.4},"shareDelta":{:.4},"totalCommits":{}}}"#,
            escape_json(&d.directory),
            d.trend.label(),
            d.current_share,
            d.previous_share,
            d.share_delta,
            d.total_commits,
        );
    }
    let _ = write!(
        json,
        r#"],"risingCount":{},"decliningCount":{},"abandonedCount":{},"totalAnalyzed":{}}}"#,
        fd.rising_count, fd.declining_count, fd.abandoned_count, fd.total_analyzed,
    );
}

/// Appends AI change detection data to JSON.
fn write_ai_change_detection_json(json: &mut String, report: &InsightsReport) {
    let ai = &report.ai_change_detection;
    json.push_str(",\"aiChangeDetection\":{\"flaggedCommits\":[");
    for (i, c) in ai.flagged_commits.iter().take(20).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","timestamp":{},"filesTouched":{},"dirsTouched":{},"anomalyScore":{:.4},"reason":"{}"}}"#,
            escape_json(&c.author),
            c.timestamp,
            c.files_touched,
            c.dirs_touched,
            c.anomaly_score,
            escape_json(&c.reason),
        );
    }
    json.push_str("],\"authorSummaries\":[");
    for (i, s) in ai.author_summaries.iter().take(20).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","flaggedCount":{},"totalCommits":{},"flaggedRatio":{:.4},"baselineMeanFiles":{:.2}}}"#,
            escape_json(&s.author),
            s.flagged_count,
            s.total_commits,
            s.flagged_ratio,
            s.baseline_mean_files,
        );
    }
    let _ = write!(
        json,
        r#"],"totalFlagged":{},"totalAnalyzed":{},"flaggedRatio":{:.4}}}"#,
        ai.total_flagged, ai.total_analyzed, ai.flagged_ratio,
    );
}

/// Appends knowledge Gini data to JSON.
fn write_knowledge_gini_json(json: &mut String, report: &InsightsReport) {
    let kg = &report.knowledge_gini;
    json.push_str(",\"knowledgeGini\":{\"developers\":[");
    for (i, d) in kg.developers.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","filesTouched":{},"totalCommits":{},"knowledgeShare":{:.4}}}"#,
            escape_json(&d.author),
            d.files_touched,
            d.total_commits,
            d.knowledge_share,
        );
    }
    let _ = write!(
        json,
        r#"],"giniCoefficient":{:.4},"top10PctShare":{:.4},"top20PctShare":{:.4},"totalDevelopers":{}}}"#,
        kg.gini_coefficient, kg.top_10_pct_share, kg.top_20_pct_share, kg.total_developers,
    );
}

/// Appends expertise profile data to JSON.
fn write_expertise_profile_json(json: &mut String, report: &InsightsReport) {
    let ep = &report.expertise_profile;
    json.push_str(",\"expertiseProfile\":{\"developers\":[");
    for (i, d) in ep.developers.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","quadrant":"{}","breadth":{:.4},"depth":{:.2},"uniqueFiles":{},"totalCommits":{}}}"#,
            escape_json(&d.author),
            d.quadrant.label(),
            d.breadth,
            d.depth,
            d.unique_files,
            d.total_commits,
        );
    }
    let _ = write!(
        json,
        r#"],"specialistDeepCount":{},"specialistShallowCount":{},"generalistDeepCount":{},"generalistShallowCount":{},"medianBreadth":{:.4},"medianDepth":{:.2}}}"#,
        ep.specialist_deep_count,
        ep.specialist_shallow_count,
        ep.generalist_deep_count,
        ep.generalist_shallow_count,
        ep.median_breadth,
        ep.median_depth,
    );
}

/// Appends cognitive load data to JSON.
fn write_cognitive_load_json(json: &mut String, report: &InsightsReport) {
    let cl = &report.cognitive_load;
    json.push_str(",\"cognitiveLoad\":{\"files\":[");
    for (i, f) in cl.files.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","loadScore":{:.4},"couplingComponent":{:.4},"dirSpreadComponent":{:.4},"authorDiversityComponent":{:.4},"temporalComponent":{:.4},"coupledFileCount":{},"authorCount":{}}}"#,
            escape_json(&f.path),
            f.load_score,
            f.coupling_component,
            f.dir_spread_component,
            f.author_diversity_component,
            f.temporal_component,
            f.coupled_file_count,
            f.author_count,
        );
    }
    let _ = write!(
        json,
        r#"],"avgLoad":{:.4},"highLoadCount":{},"totalAnalyzed":{}}}"#,
        cl.avg_load, cl.high_load_count, cl.total_analyzed,
    );
}

// ============================================================================
// Session 8: Standalone JSON writers for individual WASM API endpoints
// ============================================================================

fn write_reviewer_recommendation_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_reviewer_recommendation_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

fn write_review_response_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_review_response_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

fn write_onboarding_velocity_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_onboarding_velocity_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

fn write_interface_stability_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_interface_stability_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

fn write_tech_debt_velocity_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_tech_debt_velocity_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

fn write_focus_drift_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_focus_drift_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

fn write_ai_change_detection_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_ai_change_detection_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

fn write_knowledge_gini_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_knowledge_gini_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

fn write_expertise_profile_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_expertise_profile_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

fn write_cognitive_load_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_cognitive_load_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

// ============================================================================
// Strategic tab: JSON writers (next-generation git mining insights)
// ============================================================================

/// Appends DORA proxy metrics to the JSON output (Forsgren et al. 2018).
fn write_dora_proxy_json(json: &mut String, report: &InsightsReport) {
    let d = &report.dora_proxy;
    json.push_str(",\"doraProxy\":{");
    let _ = write!(
        json,
        r#""mergeFrequencyPerWeek":{:.4},"avgBranchDurationHours":{:.1},"revertRatio":{:.4},"avgRecoveryHours":{:.1},"reworkRatio":{:.4},"performanceTier":"{}","mergeCount":{},"revertCount":{},"fixCount":{},"totalCommits":{}"#,
        d.merge_frequency_per_week,
        d.avg_branch_duration_hours,
        d.revert_ratio,
        d.avg_recovery_hours,
        d.rework_ratio,
        d.performance_tier,
        d.merge_count,
        d.revert_count,
        d.fix_count,
        d.total_commits,
    );
    // Trend windows
    json.push_str(",\"windows\":[");
    for (i, w) in d.windows.iter().enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"startTs":{},"endTs":{},"mergeCount":{},"revertCount":{},"fixCount":{},"totalCommits":{}}}"#,
            w.start_ts, w.end_ts, w.merge_count, w.revert_count, w.fix_count, w.total_commits,
        );
    }
    json.push_str("]}");
}

fn write_dora_proxy_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_dora_proxy_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Appends knowledge currency metrics to the JSON output (Fritz et al. 2010).
fn write_knowledge_currency_json(json: &mut String, report: &InsightsReport) {
    let kc = &report.knowledge_currency;
    json.push_str(",\"knowledgeCurrency\":{\"files\":[");
    for (i, f) in kc.files.iter().take(50).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"path":"{}","currency":{:.4},"daysSinceLastTouch":{:.1},"refreshCount":{},"activeContributors":{},"totalContributors":{},"decayedKnowledgeSum":{:.4}}}"#,
            escape_json(&f.path),
            f.currency,
            f.days_since_last_touch,
            f.refresh_count,
            f.active_contributor_count,
            f.total_contributor_count,
            f.decayed_knowledge_sum,
        );
    }
    let _ = write!(
        json,
        r#"],"avgCurrency":{:.4},"staleCount":{},"currentCount":{},"totalFiles":{}}}"#,
        kc.avg_currency, kc.stale_count, kc.current_count, kc.total_files,
    );
}

fn write_knowledge_currency_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_knowledge_currency_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Appends team rhythm metrics to the JSON output (Fisher 1993).
fn write_team_rhythm_json(json: &mut String, report: &InsightsReport) {
    let tr = &report.team_rhythm;
    json.push_str(",\"teamRhythm\":{\"developers\":[");
    for (i, d) in tr.developers.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","meanHour":{:.2},"resultantLength":{:.4},"circularVariance":{:.4},"commitCount":{},"rhythmType":"{}"}}"#,
            escape_json(&d.author),
            d.mean_hour,
            d.resultant_length,
            d.circular_variance,
            d.commit_count,
            d.rhythm_type,
        );
    }
    let _ = write!(
        json,
        r#"],"teamSyncScore":{:.4},"meanResultantLength":{:.4},"teamMeanHour":{:.2},"teamCircularVariance":{:.4},"highSyncPairs":{},"lowSyncPairs":{},"totalPairs":{}}}"#,
        tr.team_sync_score,
        tr.mean_resultant_length,
        tr.team_mean_hour,
        tr.team_circular_variance,
        tr.high_sync_pairs,
        tr.low_sync_pairs,
        tr.total_pairs,
    );
}

fn write_team_rhythm_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_team_rhythm_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Appends commit coherence metrics to the JSON output (Herzig & Zeller 2013).
fn write_commit_coherence_json(json: &mut String, report: &InsightsReport) {
    let cc = &report.commit_coherence_score;
    json.push_str(",\"commitCoherence\":{\"commits\":[");
    for (i, c) in cc.commits.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","timestamp":{},"fileCount":{},"coherence":{:.4},"directoryCount":{},"typeHomogeneity":{:.4},"cochangeAffinity":{:.4}}}"#,
            escape_json(&c.author),
            c.timestamp,
            c.file_count,
            c.coherence,
            c.directory_count,
            c.type_homogeneity,
            c.cochange_affinity,
        );
    }
    json.push_str("],\"developerCoherence\":[");
    for (i, d) in cc.developer_coherence.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"author":"{}","meanCoherence":{:.4},"tangledCount":{},"totalCommits":{}}}"#,
            escape_json(&d.author),
            d.mean_coherence,
            d.tangled_count,
            d.total_commits,
        );
    }
    let _ = write!(
        json,
        r#"],"atomicityIndex":{:.4},"tangledFraction":{:.4},"totalAnalyzed":{}}}"#,
        cc.atomicity_index, cc.tangled_fraction, cc.total_analyzed,
    );
}

fn write_commit_coherence_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_commit_coherence_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Appends Markov prediction metrics to the JSON output (Hassan & Holt 2004).
fn write_markov_prediction_json(json: &mut String, report: &InsightsReport) {
    let mp = &report.markov_prediction;
    json.push_str(",\"markovPrediction\":{\"filePredictions\":[");
    for (i, fp) in mp.file_predictions.iter().take(30).enumerate() {
        if i > 0 {
            json.push(',');
        }
        let _ = write!(
            json,
            r#"{{"source":"{}","transitionCount":{},"predictions":["#,
            escape_json(&fp.source),
            fp.transition_count,
        );
        for (j, p) in fp.predictions.iter().enumerate() {
            if j > 0 {
                json.push(',');
            }
            let _ = write!(
                json,
                r#"{{"target":"{}","probability":{:.4},"count":{}}}"#,
                escape_json(&p.target),
                p.probability,
                p.count,
            );
        }
        json.push_str("]}");
    }
    let _ = write!(
        json,
        r#"],"totalFiles":{},"totalTransitions":{},"matrixSparsity":{:.4}}}"#,
        mp.total_files, mp.total_transitions, mp.matrix_sparsity,
    );
}

fn write_markov_prediction_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_markov_prediction_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

/// Appends repository health score to the JSON output (Borg et al. 2024).
fn write_repo_health_json(json: &mut String, report: &InsightsReport) {
    let rh = &report.repo_health;
    let _ = write!(
        json,
        r#","repoHealth":{{"score":{:.1},"grade":"{}","interpretation":"{}","dimensions":{{"busFactorCoverage":{:.4},"knowledgeCurrency":{:.4},"commitAtomicity":{:.4},"ownershipHealth":{:.4},"changeStability":{:.4},"defectRiskInverse":{:.4}}}}}"#,
        rh.score,
        rh.grade,
        escape_json(rh.interpretation),
        rh.dimensions.bus_factor_coverage,
        rh.dimensions.knowledge_currency,
        rh.dimensions.commit_atomicity,
        rh.dimensions.ownership_health,
        rh.dimensions.change_stability,
        rh.dimensions.defect_risk_inverse,
    );
}

fn write_repo_health_json_standalone(json: &mut String, report: &InsightsReport) {
    let mut buf = String::new();
    write_repo_health_json(&mut buf, report);
    json.push_str(buf.trim_start_matches(','));
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_escape_json_basic() {
        assert_eq!(escape_json("hello"), "hello");
        assert_eq!(escape_json("he\"lo"), "he\\\"lo");
        assert_eq!(escape_json("a\\b"), "a\\\\b");
        assert_eq!(escape_json("a\nb"), "a\\nb");
        assert_eq!(escape_json("a\tb"), "a\\tb");
    }

    #[test]
    fn test_escape_json_control_chars() {
        assert_eq!(escape_json("\x00"), "\\u0000");
        assert_eq!(escape_json("\x1f"), "\\u001f");
    }

    #[test]
    fn test_escape_json_unicode() {
        // Unicode characters should pass through unchanged
        assert_eq!(escape_json("日本語"), "日本語");
        assert_eq!(escape_json("café"), "café");
    }

    #[test]
    fn test_format_summary_json() {
        let summary = SummaryStats {
            total_commits: 100,
            total_files: 50,
            total_authors: 5,
            time_span_seconds: 86400,
            avg_files_per_commit: 3.5,
            avg_commit_entropy: 1.2345,
            median_commit_entropy: 1.0,
        };
        let json = format_summary_json(&summary);
        assert!(json.contains("\"totalCommits\":100"));
        assert!(json.contains("\"totalFiles\":50"));
        assert!(json.contains("\"totalAuthors\":5"));
        assert!(json.contains("\"avgFilesPerCommit\":3.50"));
    }

    #[test]
    fn test_convert_commits_empty() {
        let commits: Vec<rource_vcs::Commit> = Vec::new();
        let records = convert_commits(&commits);
        assert!(records.is_empty());
    }

    #[test]
    fn test_convert_commits_preserves_data() {
        use rource_vcs::{Commit, FileChange};
        let commits = vec![Commit::new("abc123", 1000, "Alice")
            .with_file(FileChange::create("src/main.rs"))
            .with_file(FileChange::modify("src/lib.rs"))];

        let records = convert_commits(&commits);
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].author, "Alice");
        assert_eq!(records[0].timestamp, 1000);
        assert_eq!(records[0].files.len(), 2);
        assert_eq!(records[0].files[0].path, "src/main.rs");
        assert!(matches!(records[0].files[0].action, FileActionKind::Create));
        assert!(matches!(records[0].files[1].action, FileActionKind::Modify));
    }

    #[test]
    fn test_format_insights_json_structure() {
        let records = vec![CommitRecord {
            timestamp: 1000,
            author: "Alice".to_string(),
            message: None,
            files: vec![FileRecord {
                path: "test.rs".to_string(),
                action: FileActionKind::Modify,
            }],
        }];
        let report = insights::compute_insights(&records);
        let json = format_insights_json(&report);

        // Verify JSON structure
        assert!(json.starts_with('{'));
        assert!(json.ends_with('}'));
        assert!(json.contains("\"summary\":"));
        assert!(json.contains("\"hotspots\":"));
        assert!(json.contains("\"couplings\":"));
        assert!(json.contains("\"ownership\":"));
        assert!(json.contains("\"busFactors\":"));
        assert!(json.contains("\"temporal\":"));
        assert!(json.contains("\"growth\":"));
        assert!(json.contains("\"workType\":"));
        assert!(json.contains("\"cadence\":"));
        assert!(json.contains("\"knowledge\":"));
        assert!(json.contains("\"profiles\":"));
        assert!(json.contains("\"lifecycle\":"));
        assert!(json.contains("\"inequality\":"));
        assert!(json.contains("\"changeEntropy\":"));
        assert!(json.contains("\"circadian\":"));
        assert!(json.contains("\"changeBursts\":"));
        assert!(json.contains("\"focus\":"));
        assert!(json.contains("\"modularity\":"));
        assert!(json.contains("\"congruence\":"));
        assert!(json.contains("\"survival\":"));
        assert!(json.contains("\"network\":"));
    }

    #[test]
    fn test_growth_json() {
        let records = vec![
            CommitRecord {
                timestamp: 1000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Create,
                }],
            },
            CommitRecord {
                timestamp: 2000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "b.rs".to_string(),
                    action: FileActionKind::Create,
                }],
            },
        ];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_growth_json(&mut json, &report);
        assert!(json.contains("\"currentFileCount\":2"));
        assert!(json.contains("\"totalCreated\":2"));
        assert!(json.contains("\"netGrowth\":2"));
    }

    #[test]
    fn test_work_type_json() {
        let records = vec![CommitRecord {
            timestamp: 1000,
            author: "Alice".to_string(),
            message: None,
            files: vec![
                FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Create,
                },
                FileRecord {
                    path: "b.rs".to_string(),
                    action: FileActionKind::Create,
                },
            ],
        }];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_work_type_json(&mut json, &report);
        assert!(json.contains("\"featurePct\":"));
        assert!(json.contains("\"dominantType\":"));
    }

    #[test]
    fn test_cadence_json() {
        let records = vec![
            CommitRecord {
                timestamp: 1000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Modify,
                }],
            },
            CommitRecord {
                timestamp: 2000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Modify,
                }],
            },
        ];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_cadence_json(&mut json, &report);
        assert!(json.contains("\"authors\":["));
        assert!(json.contains("\"teamMeanInterval\":"));
    }

    #[test]
    fn test_knowledge_json() {
        let records = vec![CommitRecord {
            timestamp: 1000,
            author: "Alice".to_string(),
            message: None,
            files: vec![FileRecord {
                path: "solo.rs".to_string(),
                action: FileActionKind::Create,
            }],
        }];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_knowledge_json(&mut json, &report);
        assert!(json.contains("\"totalSilos\":"));
        assert!(json.contains("\"isSilo\":true"));
    }

    #[test]
    fn test_profiles_json() {
        let records = vec![
            CommitRecord {
                timestamp: 1000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Modify,
                }],
            },
            CommitRecord {
                timestamp: 2000,
                author: "Bob".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "b.rs".to_string(),
                    action: FileActionKind::Create,
                }],
            },
        ];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_profiles_json(&mut json, &report);
        assert!(json.contains("\"developers\":["));
        assert!(json.contains("\"coreCount\":"));
        assert!(json.contains("\"totalContributors\":"));
    }

    #[test]
    fn test_lifecycle_json() {
        let records = vec![
            CommitRecord {
                timestamp: 1000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Create,
                }],
            },
            CommitRecord {
                timestamp: 2000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Delete,
                }],
            },
        ];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_lifecycle_json(&mut json, &report);
        assert!(json.contains("\"totalFilesSeen\":"));
        assert!(json.contains("\"churnRate\":"));
    }

    #[test]
    fn test_inequality_json() {
        let records = vec![
            CommitRecord {
                timestamp: 1000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Create,
                }],
            },
            CommitRecord {
                timestamp: 2000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "b.rs".to_string(),
                    action: FileActionKind::Create,
                }],
            },
            CommitRecord {
                timestamp: 3000,
                author: "Bob".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "c.rs".to_string(),
                    action: FileActionKind::Create,
                }],
            },
        ];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_inequality_json(&mut json, &report);
        assert!(json.contains("\"giniCoefficient\":"));
        assert!(json.contains("\"lorenzCurve\":"));
        assert!(json.contains("\"totalDevelopers\":"));
    }

    #[test]
    fn test_change_entropy_json() {
        let records = vec![
            CommitRecord {
                timestamp: 1000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Modify,
                }],
            },
            CommitRecord {
                timestamp: 2000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "b.rs".to_string(),
                    action: FileActionKind::Modify,
                }],
            },
        ];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_change_entropy_json(&mut json, &report);
        assert!(json.contains("\"changeEntropy\":"));
        assert!(json.contains("\"avgNormalizedEntropy\":"));
        assert!(json.contains("\"trend\":"));
    }

    #[test]
    fn test_circadian_json() {
        let records = vec![CommitRecord {
            timestamp: 3600, // 01:00 UTC — high risk
            author: "Alice".to_string(),
            message: None,
            files: vec![FileRecord {
                path: "a.rs".to_string(),
                action: FileActionKind::Modify,
            }],
        }];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_circadian_json(&mut json, &report);
        assert!(json.contains("\"circadian\":"));
        assert!(json.contains("\"hourlyRisk\":"));
        assert!(json.contains("\"totalCommitsAnalyzed\":"));
    }

    #[test]
    fn test_change_bursts_json() {
        let records = vec![
            CommitRecord {
                timestamp: 1000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Modify,
                }],
            },
            CommitRecord {
                timestamp: 2000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Modify,
                }],
            },
        ];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_change_bursts_json(&mut json, &report);
        assert!(json.contains("\"changeBursts\":"));
        assert!(json.contains("\"totalBursts\":"));
        assert!(json.contains("\"filesWithBursts\":"));
    }

    #[test]
    fn test_focus_json() {
        let records = vec![CommitRecord {
            timestamp: 1000,
            author: "Alice".to_string(),
            message: None,
            files: vec![FileRecord {
                path: "src/a.rs".to_string(),
                action: FileActionKind::Modify,
            }],
        }];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_focus_json(&mut json, &report);
        assert!(json.contains("\"focus\":"));
        assert!(json.contains("\"avgDeveloperFocus\":"));
        assert!(json.contains("\"avgFileDiffusion\":"));
    }

    #[test]
    fn test_modularity_json() {
        let records = vec![CommitRecord {
            timestamp: 1000,
            author: "Alice".to_string(),
            message: None,
            files: vec![FileRecord {
                path: "a.rs".to_string(),
                action: FileActionKind::Create,
            }],
        }];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_modularity_json(&mut json, &report);
        assert!(json.contains("\"modularity\":"));
        assert!(json.contains("\"modularityIndex\":"));
        assert!(json.contains("\"crossModuleRatio\":"));
    }

    #[test]
    fn test_congruence_json() {
        let records = vec![CommitRecord {
            timestamp: 1000,
            author: "Alice".to_string(),
            message: None,
            files: vec![FileRecord {
                path: "a.rs".to_string(),
                action: FileActionKind::Create,
            }],
        }];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_congruence_json(&mut json, &report);
        assert!(json.contains("\"congruence\":"));
        assert!(json.contains("\"congruenceScore\":"));
        assert!(json.contains("\"requiredCoordinations\":"));
    }

    #[test]
    fn test_survival_json() {
        let records = vec![
            CommitRecord {
                timestamp: 1000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Create,
                }],
            },
            CommitRecord {
                timestamp: 2000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Delete,
                }],
            },
        ];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_survival_json(&mut json, &report);
        assert!(json.contains("\"survival\":"));
        assert!(json.contains("\"totalBirths\":"));
        assert!(json.contains("\"infantMortalityRate\":"));
    }

    #[test]
    fn test_network_json() {
        let records = vec![
            CommitRecord {
                timestamp: 1000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "shared.rs".to_string(),
                    action: FileActionKind::Modify,
                }],
            },
            CommitRecord {
                timestamp: 2000,
                author: "Bob".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "shared.rs".to_string(),
                    action: FileActionKind::Modify,
                }],
            },
        ];
        let report = insights::compute_insights(&records);
        let mut json = String::new();
        write_network_json(&mut json, &report);
        assert!(json.contains("\"network\":"));
        assert!(json.contains("\"networkDensity\":"));
        assert!(json.contains("\"avgDegree\":"));
    }

    #[test]
    fn test_format_insights_json_escaping() {
        let records = vec![CommitRecord {
            timestamp: 1000,
            author: "O'Brien".to_string(),
            message: None,
            files: vec![FileRecord {
                path: "path/with \"quotes\".rs".to_string(),
                action: FileActionKind::Modify,
            }],
        }];
        let report = insights::compute_insights(&records);
        let json = format_insights_json(&report);

        // Quotes in paths should be escaped
        assert!(json.contains("\\\"quotes\\\""));
    }

    // ================================================================
    // InsightsIndex JSON serialization tests
    // ================================================================

    #[test]
    fn test_format_file_metrics_json_structure() {
        let records = vec![
            CommitRecord {
                timestamp: 1000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "src/main.rs".to_string(),
                    action: FileActionKind::Create,
                }],
            },
            CommitRecord {
                timestamp: 2000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "src/main.rs".to_string(),
                    action: FileActionKind::Modify,
                }],
            },
        ];
        let report = insights::compute_insights(&records);
        let index = InsightsIndex::from_report(&report);
        let fm = index.file_metrics("src/main.rs").unwrap();
        let json = format_file_metrics_json(fm);

        assert!(json.starts_with('{'));
        assert!(json.ends_with('}'));
        assert!(json.contains("\"hotspotScore\":"));
        assert!(json.contains("\"totalChanges\":"));
        assert!(json.contains("\"contributorCount\":"));
        assert!(json.contains("\"topOwner\":\"Alice\""));
        assert!(json.contains("\"lifecycleStage\":"));
        assert!(json.contains("\"burstCount\":"));
        assert!(json.contains("\"circadianRisk\":"));
        assert!(json.contains("\"knowledgeEntropy\":"));
        assert!(json.contains("\"isKnowledgeSilo\":"));
        assert!(json.contains("\"diffusionScore\":"));
        assert!(json.contains("\"couplingDegree\":"));
    }

    #[test]
    fn test_format_user_metrics_json_structure() {
        let records = vec![
            CommitRecord {
                timestamp: 1000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Create,
                }],
            },
            CommitRecord {
                timestamp: 2000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "b.rs".to_string(),
                    action: FileActionKind::Create,
                }],
            },
        ];
        let report = insights::compute_insights(&records);
        let index = InsightsIndex::from_report(&report);
        let um = index.user_metrics("Alice").unwrap();
        let json = format_user_metrics_json(um);

        assert!(json.starts_with('{'));
        assert!(json.ends_with('}'));
        assert!(json.contains("\"commitCount\":"));
        assert!(json.contains("\"profileType\":"));
        assert!(json.contains("\"uniqueFiles\":"));
        assert!(json.contains("\"avgFilesPerCommit\":"));
        assert!(json.contains("\"cadenceType\":"));
        assert!(json.contains("\"focusScore\":"));
        assert!(json.contains("\"networkDegree\":"));
        assert!(json.contains("\"directoriesTouched\":"));
    }

    #[test]
    fn test_format_index_summary_json_structure() {
        let records = vec![
            CommitRecord {
                timestamp: 1000,
                author: "Alice".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "a.rs".to_string(),
                    action: FileActionKind::Create,
                }],
            },
            CommitRecord {
                timestamp: 2000,
                author: "Bob".to_string(),
                message: None,
                files: vec![FileRecord {
                    path: "b.rs".to_string(),
                    action: FileActionKind::Create,
                }],
            },
        ];
        let report = insights::compute_insights(&records);
        let index = InsightsIndex::from_report(&report);
        let json = format_index_summary_json(index.summary());

        assert!(json.starts_with('{'));
        assert!(json.ends_with('}'));
        assert!(json.contains("\"totalFiles\":"));
        assert!(json.contains("\"totalUsers\":"));
        assert!(json.contains("\"knowledgeSiloCount\":"));
        assert!(json.contains("\"coreContributorCount\":"));
        assert!(json.contains("\"maxHotspotScore\":"));
        assert!(json.contains("\"avgContributorsPerFile\":"));
    }

    #[test]
    fn test_format_file_metrics_json_escapes_special_chars() {
        // Verify JSON escaping in top_owner field
        let fm = rource_core::insights::index::FileMetrics {
            top_owner: "O'Brien \"The Dev\"".to_string(),
            ..Default::default()
        };
        let json = format_file_metrics_json(&fm);
        // Quotes should be escaped
        assert!(json.contains("O'Brien \\\"The Dev\\\""));
    }
}
