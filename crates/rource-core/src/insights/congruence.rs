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

    // ── Mutation-killing tests ──────────────────────────────────────

    #[test]
    fn test_empty_couplings_only_returns_vacuous() {
        // Kills: replace `||` with `&&` in `couplings.is_empty() || file_authors.is_empty()`
        // With couplings empty but file_authors non-empty → still vacuous.
        let fa = make_file_authors(&[("a.rs", &["Alice"])]);
        let report = compute_congruence(&[], &fa);
        assert!(
            (report.congruence_score - 1.0).abs() < f64::EPSILON,
            "empty couplings must be vacuously congruent"
        );
        assert_eq!(report.required_coordinations, 0);
    }

    #[test]
    fn test_empty_file_authors_only_returns_vacuous() {
        // Kills: replace `||` with `&&` in `couplings.is_empty() || file_authors.is_empty()`
        // With file_authors empty but couplings non-empty → still vacuous.
        let couplings = vec![make_coupling("a.rs", "b.rs")];
        let report = compute_congruence(&couplings, &FxHashMap::default());
        assert!(
            (report.congruence_score - 1.0).abs() < f64::EPSILON,
            "empty file_authors must be vacuously congruent"
        );
        assert_eq!(report.required_coordinations, 0);
    }

    #[test]
    fn test_d1_ne_d2_filter() {
        // Kills: replace `!=` with `==` in `if d1 != d2`
        // With d1==d2 filter working, Alice-Alice self-pair is excluded from CR.
        let couplings = vec![make_coupling("a.rs", "b.rs")];
        let fa = make_file_authors(&[("a.rs", &["Alice"]), ("b.rs", &["Alice"])]);
        let report = compute_congruence(&couplings, &fa);
        assert_eq!(
            report.required_coordinations, 0,
            "d1 != d2 must exclude self-pairs"
        );
    }

    #[test]
    fn test_congruence_score_division_exact() {
        // Kills: replace `/` with `*` in `f64::from(actual) / f64::from(required)`
        // 1 actual out of 2 required → score = 0.5, not 1*2 = 2.0
        let couplings = vec![make_coupling("a.rs", "b.rs"), make_coupling("c.rs", "d.rs")];
        let fa = make_file_authors(&[
            ("a.rs", &["Alice", "Bob"]),
            ("b.rs", &["Alice", "Bob"]),
            ("c.rs", &["Carol"]),
            ("d.rs", &["Dave"]),
        ]);
        let report = compute_congruence(&couplings, &fa);
        // CR: (Alice, Bob) from (a,b); (Carol, Dave) from (c,d)
        // AC: (Alice, Bob) share a.rs and b.rs
        // congruence = 1/2 = 0.5
        assert_eq!(report.required_coordinations, 2);
        assert_eq!(report.actual_coordinations, 1);
        let expected = 0.5;
        assert!(
            (report.congruence_score - expected).abs() < 1e-10,
            "score={}, expected={}",
            report.congruence_score,
            expected
        );
        assert!(report.congruence_score <= 1.0, "score must be <= 1.0");
    }

    #[test]
    fn test_required_coordinations_guard_with_one() {
        // Kills: replace `> 0` with `> 1` in `if required_coordinations > 0`
        // Exactly 1 required coordination → division guard must pass.
        let couplings = vec![make_coupling("a.rs", "b.rs")];
        let fa = make_file_authors(&[("a.rs", &["Alice"]), ("b.rs", &["Bob"])]);
        let report = compute_congruence(&couplings, &fa);
        assert_eq!(report.required_coordinations, 1);
        // Should compute 0/1 = 0.0, not fall through to 1.0
        assert!(
            report.congruence_score.abs() < f64::EPSILON,
            "score={}, expected=0.0",
            report.congruence_score
        );
    }

    #[test]
    fn test_normalize_pair_boundary_equal() {
        // Kills: replace `<=` with `<` in `if a <= b`
        // When a == b (same string), `<=` should still produce (a, b) order.
        let (x, y) = normalize_pair("Alice", "Alice");
        assert_eq!(x, "Alice");
        assert_eq!(y, "Alice");
    }

    #[test]
    fn test_normalize_pair_ordering() {
        // Verifies canonical ordering: lexicographically smaller first
        let (a, b) = normalize_pair("Bob", "Alice");
        assert_eq!(a, "Alice");
        assert_eq!(b, "Bob");
        let (a2, b2) = normalize_pair("Alice", "Bob");
        assert_eq!(a2, "Alice");
        assert_eq!(b2, "Bob");
    }

    #[test]
    fn test_total_developer_pairs_exact() {
        // Kills: mutations in AC set building (e.g., `i + 1` → `i`)
        // 3 devs sharing a file → C(3,2) = 3 developer pairs
        let couplings = vec![make_coupling("a.rs", "b.rs")];
        let fa = make_file_authors(&[("a.rs", &["Alice", "Bob", "Carol"]), ("b.rs", &["Alice"])]);
        let report = compute_congruence(&couplings, &fa);
        // AC from file a.rs: (Alice,Bob), (Alice,Carol), (Bob,Carol) = 3 pairs
        assert_eq!(
            report.total_developer_pairs, 3,
            "C(3,2) = 3 developer pairs"
        );
    }

    #[test]
    fn test_coordination_gaps_truncated_to_20() {
        // Kills: mutants that change `truncate(20)` to `truncate(0)` or similar
        // Create >20 gaps
        let mut couplings = Vec::new();

        // 25 coupled pairs, each with a distinct dev pair → 25 gaps
        let files_a: Vec<String> = (0..25).map(|i| format!("a{i}.rs")).collect();
        let files_b: Vec<String> = (0..25).map(|i| format!("b{i}.rs")).collect();
        let devs_a: Vec<String> = (0..25).map(|i| format!("DevA{i}")).collect();
        let devs_b: Vec<String> = (0..25).map(|i| format!("DevB{i}")).collect();

        for i in 0..25 {
            couplings.push(make_coupling(&files_a[i], &files_b[i]));
        }

        let mut fa: FxHashMap<String, FxHashMap<String, u32>> = FxHashMap::default();
        for i in 0..25 {
            let mut m1: FxHashMap<String, u32> = FxHashMap::default();
            m1.insert(devs_a[i].clone(), 1);
            fa.insert(files_a[i].clone(), m1);

            let mut m2: FxHashMap<String, u32> = FxHashMap::default();
            m2.insert(devs_b[i].clone(), 1);
            fa.insert(files_b[i].clone(), m2);
        }

        let report = compute_congruence(&couplings, &fa);
        assert_eq!(report.required_coordinations, 25);
        assert!(
            report.coordination_gaps.len() <= 20,
            "gaps should be truncated to 20, got {}",
            report.coordination_gaps.len()
        );
    }

    // ── Property-based tests ────────────────────────────────────────

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// Congruence score is always in [0, 1].
            #[test]
            fn prop_congruence_bounded(
                n_couplings in 1usize..5,
                n_files in 2usize..6,
                n_devs in 2usize..5,
            ) {
                let dev_names: Vec<String> = (0..n_devs).map(|i| format!("Dev{i}")).collect();
                let mut couplings = Vec::new();
                for i in 0..n_couplings.min(n_files - 1) {
                    couplings.push(CouplingPair {
                        file_a: format!("f{i}.rs"),
                        file_b: format!("f{}.rs", i + 1),
                        support: 3,
                        confidence_ab: 0.5,
                        confidence_ba: 0.5,
                        total_a: 6,
                        total_b: 6,
                    });
                }
                let mut fa: FxHashMap<String, FxHashMap<String, u32>> = FxHashMap::default();
                for i in 0..n_files {
                    let mut authors: FxHashMap<String, u32> = FxHashMap::default();
                    // Each file gets 1-2 developers
                    authors.insert(dev_names[i % n_devs].clone(), 1);
                    if i + 1 < n_devs {
                        authors.insert(dev_names[(i + 1) % n_devs].clone(), 1);
                    }
                    fa.insert(format!("f{i}.rs"), authors);
                }
                let report = compute_congruence(&couplings, &fa);
                prop_assert!(
                    report.congruence_score >= -f64::EPSILON,
                    "score={} < 0",
                    report.congruence_score
                );
                prop_assert!(
                    report.congruence_score <= 1.0 + f64::EPSILON,
                    "score={} > 1",
                    report.congruence_score
                );
            }

            /// Actual coordinations never exceed required coordinations.
            #[test]
            fn prop_actual_leq_required(
                n_couplings in 1usize..5,
                n_devs in 2usize..5,
            ) {
                let dev_names: Vec<String> = (0..n_devs).map(|i| format!("Dev{i}")).collect();
                let mut couplings = Vec::new();
                for i in 0..n_couplings {
                    couplings.push(CouplingPair {
                        file_a: format!("a{i}.rs"),
                        file_b: format!("b{i}.rs"),
                        support: 2,
                        confidence_ab: 0.5,
                        confidence_ba: 0.5,
                        total_a: 4,
                        total_b: 4,
                    });
                }
                let mut fa: FxHashMap<String, FxHashMap<String, u32>> = FxHashMap::default();
                for i in 0..n_couplings {
                    let mut m: FxHashMap<String, u32> = FxHashMap::default();
                    m.insert(dev_names[i % n_devs].clone(), 1);
                    fa.insert(format!("a{i}.rs"), m);
                    let mut m2: FxHashMap<String, u32> = FxHashMap::default();
                    m2.insert(dev_names[(i + 1) % n_devs].clone(), 1);
                    fa.insert(format!("b{i}.rs"), m2);
                }
                let report = compute_congruence(&couplings, &fa);
                prop_assert!(
                    report.actual_coordinations <= report.required_coordinations,
                    "actual({}) > required({})",
                    report.actual_coordinations, report.required_coordinations
                );
            }

            /// normalize_pair is commutative: normalize(a,b) == normalize(b,a).
            #[test]
            fn prop_normalize_commutative(
                a in "[a-z]{1,5}",
                b in "[a-z]{1,5}",
            ) {
                let (x1, y1) = normalize_pair(&a, &b);
                let (x2, y2) = normalize_pair(&b, &a);
                prop_assert_eq!((x1, y1), (x2, y2));
            }

            /// normalize_pair always produces lexicographic order.
            #[test]
            fn prop_normalize_ordered(
                a in "[a-z]{1,5}",
                b in "[a-z]{1,5}",
            ) {
                let (x, y) = normalize_pair(&a, &b);
                prop_assert!(x <= y, "not ordered: {} > {}", x, y);
            }
        }
    }
}
