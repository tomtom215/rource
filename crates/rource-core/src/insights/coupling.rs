// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Change coupling detection.
//!
//! Identifies files that frequently change together in the same commits,
//! revealing hidden architectural dependencies that static analysis misses.
//!
//! # Research Basis
//!
//! D'Ambros et al. (2009) showed that change coupling correlates with defects
//! better than classic OO complexity metrics. Files with high coupling density
//! are especially risky for severe defects.
//!
//! # Algorithm
//!
//! For each non-bulk commit (≤50 files), we generate all unique file pairs
//! and increment their co-change count. We then compute:
//!
//! - **Support**: Number of commits where both files changed together
//! - **Confidence(A→B)**: `P(B | A) = support / total_changes_a`
//! - **Confidence(B→A)**: `P(A | B) = support / total_changes_b`
//!
//! # Data Structure
//!
//! Uses a sparse `HashMap<(String, String), u32>` for the co-change matrix.
//! File pairs are stored in sorted order (lexicographic) to ensure uniqueness.

use rustc_hash::FxHashMap;

use super::FileRecord;

/// A pair of files with measured change coupling.
#[derive(Debug, Clone)]
pub struct CouplingPair {
    /// First file path (lexicographically smaller).
    pub file_a: String,
    /// Second file path (lexicographically larger).
    pub file_b: String,
    /// Number of commits where both files changed together.
    pub support: u32,
    /// `P(B | A) = support / total_changes(A)`.
    pub confidence_ab: f64,
    /// `P(A | B) = support / total_changes(B)`.
    pub confidence_ba: f64,
    /// Total changes to file A across all commits.
    pub total_a: u32,
    /// Total changes to file B across all commits.
    pub total_b: u32,
}

/// Accumulates co-change data during commit processing.
pub struct CouplingAccumulator {
    /// Sparse co-change matrix: `(a, b)` → co-change count (a < b lexicographic).
    co_changes: FxHashMap<(String, String), u32>,
    /// Total change count per file (for confidence computation).
    file_totals: FxHashMap<String, u32>,
}

impl Default for CouplingAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl CouplingAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            co_changes: FxHashMap::default(),
            file_totals: FxHashMap::default(),
        }
    }

    /// Records a commit's file changes for coupling analysis.
    ///
    /// For k files, generates k*(k-1)/2 unique pairs.
    /// The caller is responsible for filtering bulk commits.
    pub fn record_commit(&mut self, files: &[FileRecord]) {
        // Collect unique file paths from this commit
        let mut paths: Vec<&str> = files.iter().map(|f| f.path.as_str()).collect();
        paths.sort_unstable();
        paths.dedup();

        // Increment per-file totals
        for &path in &paths {
            *self.file_totals.entry(path.to_string()).or_insert(0) += 1;
        }

        // Generate all unique pairs (O(k²) but k is bounded by BULK_COMMIT_THRESHOLD)
        for i in 0..paths.len() {
            for j in (i + 1)..paths.len() {
                let key = (paths[i].to_string(), paths[j].to_string());
                *self.co_changes.entry(key).or_insert(0) += 1;
            }
        }
    }

    /// Finalizes the accumulator into a list of coupling pairs.
    ///
    /// Only pairs with support ≥ `min_support` are included.
    #[must_use]
    pub fn finalize(self, min_support: u32) -> Vec<CouplingPair> {
        self.co_changes
            .into_iter()
            .filter(|(_, count)| *count >= min_support)
            .map(|((file_a, file_b), support)| {
                let total_a = self.file_totals.get(&file_a).copied().unwrap_or(1);
                let total_b = self.file_totals.get(&file_b).copied().unwrap_or(1);

                CouplingPair {
                    file_a,
                    file_b,
                    support,
                    confidence_ab: f64::from(support) / f64::from(total_a),
                    confidence_ba: f64::from(support) / f64::from(total_b),
                    total_a,
                    total_b,
                }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::insights::FileActionKind;

    fn file(path: &str) -> FileRecord {
        FileRecord {
            path: path.to_string(),
            action: FileActionKind::Modify,
        }
    }

    #[test]
    fn test_no_coupling_single_file_commits() {
        let mut acc = CouplingAccumulator::new();
        acc.record_commit(&[file("a.rs")]);
        acc.record_commit(&[file("b.rs")]);
        let pairs = acc.finalize(1);
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_basic_coupling() {
        let mut acc = CouplingAccumulator::new();
        acc.record_commit(&[file("a.rs"), file("b.rs")]);
        acc.record_commit(&[file("a.rs"), file("b.rs")]);
        acc.record_commit(&[file("a.rs"), file("b.rs")]);

        let pairs = acc.finalize(1);
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].support, 3);
        assert!((pairs[0].confidence_ab - 1.0).abs() < f64::EPSILON);
        assert!((pairs[0].confidence_ba - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_asymmetric_confidence() {
        let mut acc = CouplingAccumulator::new();
        // a.rs and b.rs change together twice
        acc.record_commit(&[file("a.rs"), file("b.rs")]);
        acc.record_commit(&[file("a.rs"), file("b.rs")]);
        // a.rs changes alone once
        acc.record_commit(&[file("a.rs"), file("c.rs")]);

        let pairs = acc.finalize(2);
        let ab = pairs
            .iter()
            .find(|p| p.file_a == "a.rs" && p.file_b == "b.rs");
        assert!(ab.is_some());
        let ab = ab.unwrap();

        // a.rs changed 3 times total, b.rs 2 times
        assert_eq!(ab.total_a, 3);
        assert_eq!(ab.total_b, 2);
        // P(b|a) = 2/3, P(a|b) = 2/2 = 1.0
        assert!((ab.confidence_ab - 2.0 / 3.0).abs() < 0.01);
        assert!((ab.confidence_ba - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_min_support_filtering() {
        let mut acc = CouplingAccumulator::new();
        acc.record_commit(&[file("a.rs"), file("b.rs")]);
        // Only 1 co-change — should be filtered at min_support=2
        let pairs = acc.finalize(2);
        assert!(pairs.is_empty());

        // But kept at min_support=1
        let mut acc2 = CouplingAccumulator::new();
        acc2.record_commit(&[file("a.rs"), file("b.rs")]);
        let pairs2 = acc2.finalize(1);
        assert_eq!(pairs2.len(), 1);
    }

    #[test]
    fn test_duplicate_files_in_commit() {
        let mut acc = CouplingAccumulator::new();
        // Same file appears twice in one commit — should be deduped
        acc.record_commit(&[file("a.rs"), file("a.rs"), file("b.rs")]);
        acc.record_commit(&[file("a.rs"), file("b.rs")]);

        let pairs = acc.finalize(1);
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].support, 2);
    }

    #[test]
    fn test_three_file_pairs() {
        let mut acc = CouplingAccumulator::new();
        acc.record_commit(&[file("a.rs"), file("b.rs"), file("c.rs")]);
        acc.record_commit(&[file("a.rs"), file("b.rs"), file("c.rs")]);

        let pairs = acc.finalize(1);
        // 3 files → 3 pairs: (a,b), (a,c), (b,c)
        assert_eq!(pairs.len(), 3);
        for pair in &pairs {
            assert_eq!(pair.support, 2);
        }
    }

    #[test]
    fn test_lexicographic_ordering() {
        let mut acc = CouplingAccumulator::new();
        // Even if b.rs comes before a.rs in the input, the pair key should be (a.rs, b.rs)
        acc.record_commit(&[file("z.rs"), file("a.rs")]);
        acc.record_commit(&[file("z.rs"), file("a.rs")]);

        let pairs = acc.finalize(1);
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].file_a, "a.rs");
        assert_eq!(pairs[0].file_b, "z.rs");
    }

    #[test]
    fn test_default() {
        let acc = CouplingAccumulator::default();
        let pairs = acc.finalize(1);
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_confidence_exact_values() {
        // Kills mutants: / vs * in confidence computation
        // a.rs changes 4 times, b.rs changes 3 times, they co-change 2 times
        let mut acc = CouplingAccumulator::new();
        acc.record_commit(&[file("a.rs"), file("b.rs")]); // co-change 1
        acc.record_commit(&[file("a.rs"), file("b.rs")]); // co-change 2
        acc.record_commit(&[file("a.rs"), file("c.rs")]); // a alone (with c)
        acc.record_commit(&[file("a.rs")]); // a alone
        acc.record_commit(&[file("b.rs")]); // b alone

        let pairs = acc.finalize(2);
        let ab = pairs
            .iter()
            .find(|p| p.file_a == "a.rs" && p.file_b == "b.rs")
            .expect("a.rs-b.rs pair should exist");

        assert_eq!(ab.support, 2);
        assert_eq!(ab.total_a, 4);
        assert_eq!(ab.total_b, 3);
        // confidence_ab = 2/4 = 0.5
        assert!(
            (ab.confidence_ab - 0.5).abs() < f64::EPSILON,
            "confidence_ab={}, expected=0.5",
            ab.confidence_ab
        );
        // confidence_ba = 2/3 ≈ 0.6667
        assert!(
            (ab.confidence_ba - 2.0 / 3.0).abs() < 1e-10,
            "confidence_ba={}, expected={}",
            ab.confidence_ba,
            2.0 / 3.0
        );
        // If / were *, confidence_ab would be 2*4=8.0 — verify it's not
        assert!(ab.confidence_ab <= 1.0, "confidence must be ≤ 1.0");
        assert!(ab.confidence_ba <= 1.0, "confidence must be ≤ 1.0");
    }

    #[test]
    fn test_file_totals_tracked_correctly() {
        // Kills mutants: += vs -= on file_totals and co_changes counters
        let mut acc = CouplingAccumulator::new();
        acc.record_commit(&[file("x.rs"), file("y.rs")]);
        acc.record_commit(&[file("x.rs"), file("y.rs")]);
        acc.record_commit(&[file("x.rs"), file("y.rs")]);

        let pairs = acc.finalize(1);
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].total_a, 3, "x.rs should have 3 total changes");
        assert_eq!(pairs[0].total_b, 3, "y.rs should have 3 total changes");
        assert_eq!(pairs[0].support, 3, "co-change count should be 3");
    }

    #[test]
    fn test_confidence_asymmetric_file_counts() {
        // Kills: replace / with * in confidence_ab = support / total_a
        // File a.rs changed 100 times, file b.rs changed 3 times, co-change 3 times
        let mut acc = CouplingAccumulator::new();
        // 3 co-changes
        for _ in 0..3 {
            acc.record_commit(&[file("a.rs"), file("b.rs")]);
        }
        // 97 solo changes to a.rs
        for _ in 0..97 {
            acc.record_commit(&[file("a.rs"), file("z_other.rs")]);
        }

        let pairs = acc.finalize(1);
        let ab = pairs
            .iter()
            .find(|p| p.file_a == "a.rs" && p.file_b == "b.rs")
            .expect("a.rs-b.rs pair must exist");

        assert_eq!(ab.support, 3);
        assert_eq!(ab.total_a, 100);
        assert_eq!(ab.total_b, 3);
        // confidence_ab = 3/100 = 0.03
        assert!(
            (ab.confidence_ab - 0.03).abs() < 1e-10,
            "confidence_ab={}, expected=0.03",
            ab.confidence_ab
        );
        // confidence_ba = 3/3 = 1.0
        assert!(
            (ab.confidence_ba - 1.0).abs() < 1e-10,
            "confidence_ba={}, expected=1.0",
            ab.confidence_ba
        );
    }

    #[test]
    fn test_three_file_commit_generates_three_pairs() {
        // Kills: off-by-one in j = (i+1)..paths.len() loop
        let mut acc = CouplingAccumulator::new();
        acc.record_commit(&[file("a.rs"), file("b.rs"), file("c.rs")]);

        let pairs = acc.finalize(1);
        // 3 choose 2 = 3 pairs
        assert_eq!(pairs.len(), 3, "3 files should produce exactly 3 pairs");
        // Each pair has support=1
        for pair in &pairs {
            assert_eq!(pair.support, 1);
        }
    }

    #[test]
    fn test_four_file_commit_generates_six_pairs() {
        // Kills: combinatorial correctness of pair generation
        let mut acc = CouplingAccumulator::new();
        acc.record_commit(&[file("a.rs"), file("b.rs"), file("c.rs"), file("d.rs")]);

        let pairs = acc.finalize(1);
        // 4 choose 2 = 6 pairs
        assert_eq!(pairs.len(), 6, "4 files should produce exactly 6 pairs");
    }

    #[test]
    fn test_single_file_commit_no_coupling() {
        // Kills: boundary condition on pair generation (i < paths.len(), j starts at i+1)
        let mut acc = CouplingAccumulator::new();
        acc.record_commit(&[file("alone.rs")]);
        acc.record_commit(&[file("alone.rs")]);
        acc.record_commit(&[file("alone.rs")]);

        let pairs = acc.finalize(1);
        assert!(
            pairs.is_empty(),
            "single-file commits produce no coupling pairs"
        );
    }

    #[test]
    fn test_confidence_zero_when_no_co_change() {
        // Kills: support count increment (if += 0 instead of += 1)
        let mut acc = CouplingAccumulator::new();
        // a.rs and b.rs never co-change
        acc.record_commit(&[file("a.rs"), file("c.rs")]);
        acc.record_commit(&[file("b.rs"), file("c.rs")]);

        let pairs = acc.finalize(1);
        // No pair for (a.rs, b.rs) since they never co-changed
        let ab = pairs
            .iter()
            .find(|p| p.file_a == "a.rs" && p.file_b == "b.rs");
        assert!(
            ab.is_none(),
            "files that never co-change should have no pair"
        );
    }

    #[test]
    fn test_support_count_increments_correctly() {
        // Kills: += 1 vs += 0 or -= 1 in co_changes counter
        let mut acc = CouplingAccumulator::new();
        acc.record_commit(&[file("a.rs"), file("b.rs")]);
        let pairs1 = CouplingAccumulator::new();
        // Use separate accumulator to check intermediate state
        let mut acc2 = CouplingAccumulator::new();
        acc2.record_commit(&[file("a.rs"), file("b.rs")]);
        let p1 = acc2.finalize(1);
        assert_eq!(p1[0].support, 1, "1 co-change → support=1");

        let mut acc3 = CouplingAccumulator::new();
        acc3.record_commit(&[file("a.rs"), file("b.rs")]);
        acc3.record_commit(&[file("a.rs"), file("b.rs")]);
        let p2 = acc3.finalize(1);
        assert_eq!(p2[0].support, 2, "2 co-changes → support=2");

        // Unused accumulator to suppress warning
        let _ = pairs1.finalize(1);
        let _ = acc.finalize(1);
    }

    #[test]
    fn test_confidence_boundary_at_one() {
        // Kills: confidence clamp logic — when files always co-change, confidence = 1.0
        let mut acc = CouplingAccumulator::new();
        for _ in 0..10 {
            acc.record_commit(&[file("a.rs"), file("b.rs")]);
        }

        let pairs = acc.finalize(1);
        assert_eq!(pairs.len(), 1);
        assert!(
            (pairs[0].confidence_ab - 1.0).abs() < 1e-10,
            "always co-changed → confidence_ab=1.0, got={}",
            pairs[0].confidence_ab
        );
        assert!(
            (pairs[0].confidence_ba - 1.0).abs() < 1e-10,
            "always co-changed → confidence_ba=1.0, got={}",
            pairs[0].confidence_ba
        );
    }

    #[test]
    fn test_file_total_increment_per_commit() {
        // Kills: += 1 vs += 0 on file_totals counter
        let mut acc = CouplingAccumulator::new();
        acc.record_commit(&[file("a.rs"), file("b.rs")]);
        acc.record_commit(&[file("a.rs")]);
        acc.record_commit(&[file("a.rs"), file("c.rs")]);

        let pairs = acc.finalize(1);
        let ab = pairs
            .iter()
            .find(|p| p.file_a == "a.rs" && p.file_b == "b.rs")
            .expect("a.rs-b.rs pair");

        assert_eq!(ab.total_a, 3, "a.rs appeared in 3 commits");
        assert_eq!(ab.total_b, 1, "b.rs appeared in 1 commit");
    }

    #[test]
    fn test_min_support_boundary_exactly_at_threshold() {
        // Kills: >= vs > in min_support filter
        let mut acc = CouplingAccumulator::new();
        acc.record_commit(&[file("a.rs"), file("b.rs")]);
        acc.record_commit(&[file("a.rs"), file("b.rs")]);
        acc.record_commit(&[file("a.rs"), file("b.rs")]);

        // At min_support=3, support=3 should be included (>=)
        let pairs = acc.finalize(3);
        assert_eq!(
            pairs.len(),
            1,
            "support=3 with min_support=3 should be included"
        );
        assert_eq!(pairs[0].support, 3);

        // At min_support=4, support=3 should be excluded
        let mut acc2 = CouplingAccumulator::new();
        acc2.record_commit(&[file("a.rs"), file("b.rs")]);
        acc2.record_commit(&[file("a.rs"), file("b.rs")]);
        acc2.record_commit(&[file("a.rs"), file("b.rs")]);
        let pairs2 = acc2.finalize(4);
        assert!(
            pairs2.is_empty(),
            "support=3 with min_support=4 should be excluded"
        );
    }

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        fn file(path: &str) -> crate::insights::FileRecord {
            crate::insights::FileRecord {
                path: path.to_string(),
                action: crate::insights::FileActionKind::Modify,
            }
        }

        proptest! {
            /// Confidence values are always in [0, 1].
            #[test]
            fn prop_confidence_bounded(n_commits in 2usize..10, n_files in 2usize..6) {
                let mut acc = CouplingAccumulator::new();
                let file_names: Vec<String> = (0..n_files).map(|i| format!("f{i}.rs")).collect();
                for c in 0..n_commits {
                    // Each commit touches a subset of files
                    let subset: Vec<_> = file_names.iter()
                        .enumerate()
                        .filter(|(i, _)| (c + i) % 2 == 0)
                        .map(|(_, name)| file(name))
                        .collect();
                    if subset.len() >= 2 {
                        acc.record_commit(&subset);
                    }
                }
                let pairs = acc.finalize(1);
                for pair in &pairs {
                    prop_assert!(pair.confidence_ab >= 0.0 && pair.confidence_ab <= 1.0 + 1e-10,
                        "confidence_ab={} out of [0,1]", pair.confidence_ab);
                    prop_assert!(pair.confidence_ba >= 0.0 && pair.confidence_ba <= 1.0 + 1e-10,
                        "confidence_ba={} out of [0,1]", pair.confidence_ba);
                }
            }

            /// Coupling pairs are always lexicographically ordered (file_a < file_b).
            #[test]
            fn prop_lex_order(n_commits in 2usize..8, n_files in 2usize..6) {
                let mut acc = CouplingAccumulator::new();
                let file_names: Vec<String> = (0..n_files).map(|i| format!("f{i}.rs")).collect();
                for _ in 0..n_commits {
                    let files: Vec<_> = file_names.iter().map(|n| file(n)).collect();
                    acc.record_commit(&files);
                }
                let pairs = acc.finalize(1);
                for pair in &pairs {
                    prop_assert!(pair.file_a < pair.file_b,
                        "file_a={} >= file_b={}", pair.file_a, pair.file_b);
                }
            }

            /// Support is always ≤ min(total_a, total_b).
            #[test]
            fn prop_support_bounded(n_commits in 2usize..10) {
                let mut acc = CouplingAccumulator::new();
                for _ in 0..n_commits {
                    acc.record_commit(&[file("a.rs"), file("b.rs")]);
                }
                let pairs = acc.finalize(1);
                for pair in &pairs {
                    let min_total = pair.total_a.min(pair.total_b);
                    prop_assert!(pair.support <= min_total,
                        "support={} > min(total_a={}, total_b={})",
                        pair.support, pair.total_a, pair.total_b);
                }
            }

            /// Number of pairs from k unique files is at most C(k, 2) = k*(k-1)/2.
            #[test]
            fn prop_pair_count_bounded(n_files in 2usize..8) {
                let mut acc = CouplingAccumulator::new();
                let files: Vec<_> = (0..n_files).map(|i| file(&format!("f{i}.rs"))).collect();
                acc.record_commit(&files);
                acc.record_commit(&files); // Need support >= 2
                let pairs = acc.finalize(2);
                let max_pairs = n_files * (n_files - 1) / 2;
                prop_assert!(pairs.len() <= max_pairs,
                    "pairs={} > C({},2)={}", pairs.len(), n_files, max_pairs);
            }
        }
    }
}
