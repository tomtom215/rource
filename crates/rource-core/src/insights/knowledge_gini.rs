// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Knowledge distribution Gini coefficient analysis (M10).
//!
//! Measures inequality of code knowledge across team members. High Gini
//! indicates knowledge hoarding; low Gini indicates well-distributed expertise.
//!
//! # Research Basis
//!
//! Yamashita & Moonen (2013) "Do Developers Care About Code Smells? An
//! Exploratory Survey" (WCRE, DOI: 10.1109/WCRE.2013.6671299).
//!
//! Greiler et al. (2015) "Code Ownership and Software Quality: A Replication
//! Study" (FSE, DOI: 10.1145/2786805.2786852).
//!
//! # Algorithm
//!
//! Standard Gini coefficient on per-developer file-weighted contribution:
//! `G = (2 × Σ i×x_i) / (n × Σ x_i) - (n+1)/n`
//! where `x_i` is sorted ascending contribution count per developer.
//!
//! # Complexity
//!
//! - Computed from `file_authors` map: O(A log A) where A = authors

use rustc_hash::FxHashMap;

/// Per-developer knowledge distribution profile.
#[derive(Debug, Clone)]
pub struct DeveloperKnowledge {
    /// Developer name.
    pub author: String,
    /// Total files touched.
    pub files_touched: u32,
    /// Total commits across all files.
    pub total_commits: u32,
    /// Knowledge share: this developer's commits / total commits.
    pub knowledge_share: f64,
}

/// Complete knowledge Gini report.
#[derive(Debug, Clone)]
pub struct KnowledgeGiniReport {
    /// Per-developer knowledge profiles (sorted by `knowledge_share` descending).
    pub developers: Vec<DeveloperKnowledge>,
    /// Gini coefficient ∈ [0, 1]. 0 = perfect equality, 1 = total inequality.
    pub gini_coefficient: f64,
    /// Share of total commits held by top 10% of developers.
    pub top_10_pct_share: f64,
    /// Share of total commits held by top 20% of developers.
    pub top_20_pct_share: f64,
    /// Total developers analyzed.
    pub total_developers: usize,
}

/// Computes the knowledge Gini coefficient from `file_authors` data.
///
/// This function does not need an accumulator — it operates on the
/// already-accumulated `file_authors` map.
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn compute_knowledge_gini(
    file_authors: &FxHashMap<String, FxHashMap<String, u32>>,
) -> KnowledgeGiniReport {
    // Aggregate per-developer: total commits and unique files
    let mut dev_commits: FxHashMap<String, (u32, u32)> = FxHashMap::default();

    for authors in file_authors.values() {
        for (author, &count) in authors {
            let entry = dev_commits.entry(author.clone()).or_insert((0, 0));
            entry.0 += count; // total commits
            entry.1 += 1; // files touched
        }
    }

    let grand_total: u32 = dev_commits.values().map(|&(c, _)| c).sum();
    let grand_total_f = f64::from(grand_total.max(1));

    let mut developers: Vec<DeveloperKnowledge> = dev_commits
        .into_iter()
        .map(
            |(author, (total_commits, files_touched))| DeveloperKnowledge {
                author,
                files_touched,
                total_commits,
                knowledge_share: f64::from(total_commits) / grand_total_f,
            },
        )
        .collect();

    // Sort by commits ascending for Gini computation
    developers.sort_by_key(|d| d.total_commits);

    let n = developers.len();
    let gini_coefficient = if n <= 1 || grand_total == 0 {
        0.0
    } else {
        let n_f = n as f64;
        let sum_x: f64 = developers.iter().map(|d| f64::from(d.total_commits)).sum();
        let weighted_sum: f64 = developers
            .iter()
            .enumerate()
            .map(|(i, d)| (i as f64 + 1.0) * f64::from(d.total_commits))
            .sum();
        (2.0 * weighted_sum) / (n_f * sum_x) - (n_f + 1.0) / n_f
    };

    // Sort descending for display and top-N share computation
    developers.sort_by(|a, b| {
        b.knowledge_share
            .partial_cmp(&a.knowledge_share)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let top_10_count = (n as f64 * 0.1).ceil() as usize;
    let top_20_count = (n as f64 * 0.2).ceil() as usize;

    let top_10_pct_share: f64 = developers
        .iter()
        .take(top_10_count.max(1))
        .map(|d| d.knowledge_share)
        .sum();
    let top_20_pct_share: f64 = developers
        .iter()
        .take(top_20_count.max(1))
        .map(|d| d.knowledge_share)
        .sum();

    developers.truncate(50);

    KnowledgeGiniReport {
        developers,
        gini_coefficient,
        top_10_pct_share,
        top_20_pct_share,
        total_developers: n,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_file_authors(
        entries: &[(&str, &[(&str, u32)])],
    ) -> FxHashMap<String, FxHashMap<String, u32>> {
        entries
            .iter()
            .map(|(path, authors)| {
                let author_map: FxHashMap<String, u32> =
                    authors.iter().map(|(a, c)| (a.to_string(), *c)).collect();
                (path.to_string(), author_map)
            })
            .collect()
    }

    #[test]
    fn test_empty() {
        let report = compute_knowledge_gini(&FxHashMap::default());
        assert!(report.developers.is_empty());
        assert!((report.gini_coefficient - 0.0).abs() < 1e-10);
    }

    #[test]
    fn test_single_developer() {
        let data = make_file_authors(&[("a.rs", &[("Alice", 10)])]);
        let report = compute_knowledge_gini(&data);
        assert_eq!(report.total_developers, 1);
        assert!((report.gini_coefficient - 0.0).abs() < 1e-10);
        assert!((report.developers[0].knowledge_share - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_equal_distribution() {
        let data = make_file_authors(&[
            ("a.rs", &[("Alice", 5), ("Bob", 5)]),
            ("b.rs", &[("Alice", 5), ("Bob", 5)]),
        ]);
        let report = compute_knowledge_gini(&data);
        assert_eq!(report.total_developers, 2);
        assert!(
            report.gini_coefficient.abs() < 1e-10,
            "equal distribution should have gini=0, got {}",
            report.gini_coefficient
        );
    }

    #[test]
    fn test_unequal_distribution() {
        let data = make_file_authors(&[("a.rs", &[("Alice", 100)]), ("b.rs", &[("Bob", 1)])]);
        let report = compute_knowledge_gini(&data);
        assert!(
            report.gini_coefficient > 0.3,
            "unequal distribution should have high gini, got {}",
            report.gini_coefficient
        );
    }

    #[test]
    fn test_top_share_computed() {
        let data = make_file_authors(&[(
            "a.rs",
            &[("Alice", 80), ("Bob", 10), ("Carol", 5), ("Dave", 5)],
        )]);
        let report = compute_knowledge_gini(&data);
        assert!(report.top_10_pct_share > 0.0);
        assert!(report.top_20_pct_share > 0.0);
    }
}
