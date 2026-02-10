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
}
