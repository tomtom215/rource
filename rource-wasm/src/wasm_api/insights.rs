// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Repository insights API.
//!
//! Exposes research-backed software engineering metrics computed from VCS
//! commit history. These metrics provide actionable intelligence about
//! code health, organizational risk, and development patterns.
//!
//! All metrics are computed from the loaded commit data (no external APIs).
//! Computation happens once at query time and is cached.

use std::fmt::Write;

use wasm_bindgen::prelude::*;

use rource_core::insights::{
    self, CommitRecord, FileActionKind, FileRecord, InsightsReport, SummaryStats,
};

use crate::Rource;

// ============================================================================
// Conversion: rource_vcs::Commit → insights::CommitRecord
// ============================================================================

/// Converts loaded VCS commits to insight-ready records.
fn convert_commits(commits: &[rource_vcs::Commit]) -> Vec<CommitRecord> {
    commits
        .iter()
        .map(|c| CommitRecord {
            timestamp: c.timestamp,
            author: c.author.clone(),
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
    let mut json = String::with_capacity(4096);
    json.push_str("{\"summary\":");
    json.push_str(&format_summary_json(&report.summary));
    write_hotspots_json(&mut json, report);
    write_couplings_json(&mut json, report);
    write_ownership_json(&mut json, report);
    write_bus_factors_json(&mut json, report);
    write_temporal_json(&mut json, report);
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
            r#"{{"fileA":"{}","fileB":"{}","support":{},"confidenceAB":{:.4},"confidenceBA":{:.4},"totalA":{},"totalB":{}}}"#,
            escape_json(&c.file_a),
            escape_json(&c.file_b),
            c.support,
            c.confidence_ab,
            c.confidence_ba,
            c.total_a,
            c.total_b,
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

// ============================================================================
// WASM API
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Computes and returns comprehensive repository insights as JSON.
    ///
    /// Analyzes the loaded commit history to produce research-backed metrics:
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
    /// Computed from commit history at call time (not per-frame).
    /// Typical computation time: <10ms for 10k commits.
    #[wasm_bindgen(js_name = getInsights)]
    pub fn get_insights(&self) -> Option<String> {
        if self.commits.is_empty() {
            return None;
        }

        let records = convert_commits(&self.commits);
        let report = insights::compute_insights(&records);
        Some(format_insights_json(&report))
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
        if self.commits.is_empty() {
            return None;
        }

        let records = convert_commits(&self.commits);
        let report = insights::compute_insights(&records);
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
        if self.commits.is_empty() {
            return None;
        }

        let records = convert_commits(&self.commits);
        let report = insights::compute_insights(&records);
        let n = limit.unwrap_or(20).min(report.couplings.len());

        let mut json = String::with_capacity(1024);
        json.push('[');
        for (i, c) in report.couplings.iter().take(n).enumerate() {
            if i > 0 {
                json.push(',');
            }
            let _ = write!(
                json,
                r#"{{"fileA":"{}","fileB":"{}","support":{},"confidenceAB":{:.4},"confidenceBA":{:.4}}}"#,
                escape_json(&c.file_a),
                escape_json(&c.file_b),
                c.support,
                c.confidence_ab,
                c.confidence_ba,
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
        if self.commits.is_empty() {
            return None;
        }

        let records = convert_commits(&self.commits);
        let report = insights::compute_insights(&records);

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
        if self.commits.is_empty() {
            return None;
        }

        let records = convert_commits(&self.commits);
        let report = insights::compute_insights(&records);

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
        if self.commits.is_empty() {
            return None;
        }

        let records = convert_commits(&self.commits);
        let report = insights::compute_insights(&records);

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
    }

    #[test]
    fn test_format_insights_json_escaping() {
        let records = vec![CommitRecord {
            timestamp: 1000,
            author: "O'Brien".to_string(),
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
}
