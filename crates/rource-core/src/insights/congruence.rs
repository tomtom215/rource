// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Sociotechnical congruence analysis (Conway's Law quantified).
//!
//! Measures alignment between who SHOULD coordinate (inferred from technical
//! co-change dependencies) and who ACTUALLY coordinates (inferred from working
//! on the same files).
//!
//! # Research Basis
//!
//! Cataldo, Herbsleb & Carley (2008) "Socio-Technical Congruence: A Framework for
//! Assessing the Impact of Technical and Work Dependencies on Software Development
//! Productivity" (ESEM 2008) showed 32% improvement in modification request resolution
//! time when coordination patterns match coordination needs.
//!
//! Cataldo et al. (2009) "Software Dependencies, Work Dependencies, and Their Impact
//! on Failures" (IEEE TSE 35(6), pp. 864–878) extended the framework.
//!
//! Kwan et al. (2013) "Socio-Technical Congruence in OSS Projects: Exploring
//! Conway's Law in FreeBSD" (IFIP 2013) validated on FreeBSD.
//!
//! # Algorithm
//!
//! 1. Build Technical Dependency set TD from coupling pairs
//! 2. Build Developer-File mapping from `file_authors`
//! 3. Coordination Requirements CR: for each (fᵢ, fⱼ) in TD, all (d₁, d₂) pairs
//!    where d₁ modified fᵢ and d₂ modified fⱼ (d₁ ≠ d₂)
//! 4. Actual Coordination AC: for each file f, all (d₁, d₂) pairs who both modified f
//! 5. Congruence = |CR ∩ AC| / |CR|
//!
//! # Complexity
//!
//! - O(C × d² + F × d²) where C = coupling pairs, d = avg developers per file

use rustc_hash::{FxHashMap, FxHashSet};

use super::coupling::CouplingPair;

/// A coordination gap between two developers who should but don't coordinate.
#[derive(Debug, Clone)]
pub struct CoordinationGap {
    /// First developer.
    pub developer_a: String,
    /// Second developer.
    pub developer_b: String,
    /// Number of technical dependencies linking them.
    pub shared_dependencies: u32,
}

/// Complete sociotechnical congruence report.
#[derive(Debug, Clone)]
pub struct CongruenceReport {
    /// Overall congruence score in \[0, 1\].
    /// Higher = better alignment with Conway's Law.
    pub congruence_score: f64,
    /// |CR| — number of developer pairs that should coordinate.
    pub required_coordinations: u32,
    /// |CR ∩ AC| — number of required pairs that actually coordinate.
    pub actual_coordinations: u32,
    /// Top pairs that SHOULD but DON'T coordinate, sorted by `shared_dependencies` desc.
    pub coordination_gaps: Vec<CoordinationGap>,
    /// Total unique developer pairs in the project.
    pub total_developer_pairs: u32,
}

/// Computes sociotechnical congruence from coupling data and file ownership.
///
/// # Arguments
///
/// * `couplings` - Finalized co-change coupling pairs (technical dependencies)
/// * `file_authors` - Map of file → (author → change count) (actual coordination)
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn compute_congruence(
    couplings: &[CouplingPair],
    file_authors: &FxHashMap<String, FxHashMap<String, u32>>,
) -> CongruenceReport {
    if couplings.is_empty() || file_authors.is_empty() {
        return CongruenceReport {
            congruence_score: 1.0, // vacuously congruent
            required_coordinations: 0,
            actual_coordinations: 0,
            coordination_gaps: Vec::new(),
            total_developer_pairs: 0,
        };
    }

    // Build Coordination Requirements (CR):
    // For each coupled file pair (fi, fj), all developer pairs (d1, d2) where
    // d1 modified fi and d2 modified fj, d1 ≠ d2
    let mut cr: FxHashMap<(String, String), u32> = FxHashMap::default();

    for pair in couplings {
        let devs_a: Vec<&str> = file_authors
            .get(&pair.file_a)
            .map_or_else(Vec::new, |m| m.keys().map(String::as_str).collect());
        let devs_b: Vec<&str> = file_authors
            .get(&pair.file_b)
            .map_or_else(Vec::new, |m| m.keys().map(String::as_str).collect());

        for &d1 in &devs_a {
            for &d2 in &devs_b {
                if d1 != d2 {
                    let key = normalize_pair(d1, d2);
                    *cr.entry(key).or_insert(0) += 1;
                }
            }
        }
    }

    // Build Actual Coordination (AC):
    // For each file, all developer pairs who both modified it
    let mut ac: FxHashSet<(String, String)> = FxHashSet::default();

    for authors in file_authors.values() {
        let devs: Vec<&str> = authors.keys().map(String::as_str).collect();
        for i in 0..devs.len() {
            for j in (i + 1)..devs.len() {
                let key = normalize_pair(devs[i], devs[j]);
                ac.insert(key);
            }
        }
    }

    // Congruence = |CR ∩ AC| / |CR|
    let required_coordinations = cr.len() as u32;
    let mut actual_coordinations: u32 = 0;
    let mut gaps: Vec<CoordinationGap> = Vec::new();

    for (pair, dep_count) in &cr {
        if ac.contains(pair) {
            actual_coordinations += 1;
        } else {
            gaps.push(CoordinationGap {
                developer_a: pair.0.clone(),
                developer_b: pair.1.clone(),
                shared_dependencies: *dep_count,
            });
        }
    }

    gaps.sort_by(|a, b| b.shared_dependencies.cmp(&a.shared_dependencies));
    gaps.truncate(20);

    let congruence_score = if required_coordinations > 0 {
        f64::from(actual_coordinations) / f64::from(required_coordinations)
    } else {
        1.0
    };

    CongruenceReport {
        congruence_score,
        required_coordinations,
        actual_coordinations,
        coordination_gaps: gaps,
        total_developer_pairs: ac.len() as u32,
    }
}

/// Normalizes a developer pair to a canonical order (lexicographic).
fn normalize_pair(a: &str, b: &str) -> (String, String) {
    if a <= b {
        (a.to_string(), b.to_string())
    } else {
        (b.to_string(), a.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_coupling(a: &str, b: &str) -> CouplingPair {
        CouplingPair {
            file_a: a.to_string(),
            file_b: b.to_string(),
            support: 3,
            confidence_ab: 1.0,
            confidence_ba: 1.0,
            total_a: 3,
            total_b: 3,
        }
    }

    fn make_file_authors(entries: &[(&str, &[&str])]) -> FxHashMap<String, FxHashMap<String, u32>> {
        entries
            .iter()
            .map(|(path, authors)| {
                let author_map: FxHashMap<String, u32> =
                    authors.iter().map(|a| (a.to_string(), 1)).collect();
                (path.to_string(), author_map)
            })
            .collect()
    }

    #[test]
    fn test_perfect_congruence() {
        // Files a.rs and b.rs are coupled. Alice modifies both → she coordinates with herself (excluded).
        // Actually: Alice and Bob both modify a.rs AND b.rs → CR pair exists AND AC pair exists.
        let couplings = vec![make_coupling("a.rs", "b.rs")];
        let fa = make_file_authors(&[("a.rs", &["Alice", "Bob"]), ("b.rs", &["Alice", "Bob"])]);
        let report = compute_congruence(&couplings, &fa);
        // CR: (Alice, Bob) since Alice→a, Bob→b and Alice→b, Bob→a
        // AC: (Alice, Bob) share both files
        assert!(
            (report.congruence_score - 1.0).abs() < f64::EPSILON,
            "score={}, expected=1.0",
            report.congruence_score
        );
        assert!(report.coordination_gaps.is_empty());
    }

    #[test]
    fn test_zero_congruence() {
        // a.rs modified only by Alice, b.rs modified only by Bob. They're coupled but never share files.
        let couplings = vec![make_coupling("a.rs", "b.rs")];
        let fa = make_file_authors(&[("a.rs", &["Alice"]), ("b.rs", &["Bob"])]);
        let report = compute_congruence(&couplings, &fa);
        // CR: (Alice, Bob) — they should coordinate
        // AC: empty — they never share a file
        assert!(
            report.congruence_score.abs() < f64::EPSILON,
            "score={}, expected=0.0",
            report.congruence_score
        );
        assert_eq!(report.required_coordinations, 1);
        assert_eq!(report.actual_coordinations, 0);
        assert_eq!(report.coordination_gaps.len(), 1);
    }

    #[test]
    fn test_partial_congruence() {
        // Two coupling pairs, one fulfilled, one not
        let couplings = vec![make_coupling("a.rs", "b.rs"), make_coupling("c.rs", "d.rs")];
        let fa = make_file_authors(&[
            ("a.rs", &["Alice"]),
            ("b.rs", &["Bob"]),
            ("c.rs", &["Carol"]),
            ("d.rs", &["Carol"]), // Carol on both → she coordinates with herself (excluded)
        ]);
        // CR from (a,b): (Alice, Bob) — gap (no shared file)
        // CR from (c,d): no pairs since Carol is the only dev for both files
        // So CR = {(Alice, Bob)}, AC = {} → congruence = 0.0
        let report = compute_congruence(&couplings, &fa);
        assert_eq!(report.required_coordinations, 1);
        assert_eq!(report.actual_coordinations, 0);
    }

    #[test]
    fn test_single_developer() {
        // Only 1 developer → no pairs needed → congruence = 1.0
        let couplings = vec![make_coupling("a.rs", "b.rs")];
        let fa = make_file_authors(&[("a.rs", &["Alice"]), ("b.rs", &["Alice"])]);
        let report = compute_congruence(&couplings, &fa);
        // No d1 ≠ d2 pairs possible → CR empty → vacuously congruent
        assert!(
            (report.congruence_score - 1.0).abs() < f64::EPSILON,
            "single dev should be vacuously congruent"
        );
    }

    #[test]
    fn test_no_coupling() {
        // No technical dependencies → vacuously congruent
        let fa = make_file_authors(&[("a.rs", &["Alice", "Bob"])]);
        let report = compute_congruence(&[], &fa);
        assert!(
            (report.congruence_score - 1.0).abs() < f64::EPSILON,
            "no coupling = vacuously congruent"
        );
    }

    #[test]
    fn test_coordination_gaps_sorted() {
        // Multiple gaps, sorted by shared_dependencies descending
        let couplings = vec![
            make_coupling("a.rs", "b.rs"),
            make_coupling("a.rs", "c.rs"),
            make_coupling("a.rs", "d.rs"),
        ];
        let fa = make_file_authors(&[
            ("a.rs", &["Alice"]),
            ("b.rs", &["Bob"]),
            ("c.rs", &["Carol"]),
            ("d.rs", &["Dave"]),
        ]);
        let report = compute_congruence(&couplings, &fa);
        // All pairs are gaps
        assert!(!report.coordination_gaps.is_empty());
        for i in 1..report.coordination_gaps.len() {
            assert!(
                report.coordination_gaps[i].shared_dependencies
                    <= report.coordination_gaps[i - 1].shared_dependencies,
                "gaps not sorted at index {}",
                i
            );
        }
    }

    #[test]
    fn test_gap_identifies_correct_pair() {
        let couplings = vec![make_coupling("a.rs", "b.rs")];
        let fa = make_file_authors(&[("a.rs", &["Alice"]), ("b.rs", &["Bob"])]);
        let report = compute_congruence(&couplings, &fa);
        let gap = &report.coordination_gaps[0];
        // Pair should be Alice-Bob (normalized order)
        assert!(
            (gap.developer_a == "Alice" && gap.developer_b == "Bob")
                || (gap.developer_a == "Bob" && gap.developer_b == "Alice"),
            "gap pair should be Alice-Bob, got {}-{}",
            gap.developer_a,
            gap.developer_b
        );
    }

    #[test]
    fn test_self_pairs_excluded() {
        // Alice modifies both coupled files — no self-pair in CR
        let couplings = vec![make_coupling("a.rs", "b.rs")];
        let fa = make_file_authors(&[("a.rs", &["Alice"]), ("b.rs", &["Alice"])]);
        let report = compute_congruence(&couplings, &fa);
        assert_eq!(
            report.required_coordinations, 0,
            "self-pairs should be excluded"
        );
    }
}
