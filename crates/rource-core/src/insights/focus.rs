// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Developer focus and file diffusion analysis.
//!
//! Measures two complementary Shannon entropy metrics:
//! 1. **Developer Focus**: how concentrated is a developer's activity across directories?
//! 2. **File Diffusion**: how spread out are a file's contributors?
//!
//! Together these identify both risky developers (scattered across many areas) and
//! risky files (too many equally-contributing developers create coordination overhead).
//!
//! # Research Basis
//!
//! Posnett, D'Souza, Devanbu & Filkov (2013) "Dual Ecological Measures of Focus
//! in Software Development" (ICSE 2013, pp. 452–461) validated on multiple large
//! OSS projects. More focused developers introduce fewer defects, BUT files with
//! narrowly focused contributions (few contributors) are MORE defect-prone.
//!
//! Palomba et al. (2015) "On the Role of Developer's Scattered Changes in Bug
//! Prediction" (SANER 2015) confirmed developer scattering correlates with bugs.
//!
//! # Algorithm
//!
//! **Developer Focus** (per developer d):
//! 1. Count commits by d to each directory → `freq(d, dir)`
//! 2. `p(dir) = freq(d, dir) / total_commits_by_d`
//! 3. `H(d) = -Σ p(dir) × log₂(p(dir))`
//! 4. `H_norm(d) = H(d) / log₂(dirs_touched)` (if dirs > 1)
//! 5. `Focus(d) = 1.0 − H_norm(d)` ∈ \[0, 1\]
//!
//! **File Diffusion** (per file f):
//! 1. Count commits to f by each developer → `freq(f, dev)`
//! 2. `p(dev) = freq(f, dev) / total_commits_to_f`
//! 3. `H(f) = -Σ p(dev) × log₂(p(dev))`
//! 4. `Diffusion(f) = H(f) / log₂(num_devs)` (if devs > 1) ∈ \[0, 1\]
//!
//! # Complexity
//!
//! - Developer focus accumulation: O(N) per commit
//! - File diffusion: O(F × A') computed from `file_authors` map (no accumulator needed)
//! - Finalization: O(A × D + F × A') where A = authors, D = dirs, F = files

use rustc_hash::FxHashMap;

/// Developer focus profile.
#[derive(Debug, Clone)]
pub struct DeveloperFocus {
    /// Developer name.
    pub author: String,
    /// Focus score: `1.0 − H_norm` ∈ \[0, 1\].
    /// 1.0 = fully concentrated in one directory.
    /// 0.0 = perfectly scattered across all directories.
    pub focus_score: f64,
    /// Number of unique directories touched.
    pub directories_touched: u32,
    /// Directory with the most commits from this developer.
    pub primary_directory: String,
    /// Total commits by this developer.
    pub commit_count: u32,
}

/// File diffusion profile.
#[derive(Debug, Clone)]
pub struct FileDiffusion {
    /// File path.
    pub path: String,
    /// Diffusion score: `H_norm` ∈ \[0, 1\].
    /// High = many equally-contributing developers (Posnett's "risky file").
    /// Low = dominated by one developer.
    pub diffusion_score: f64,
    /// Number of unique contributors.
    pub contributor_count: u32,
    /// Total modification count.
    pub total_changes: u32,
}

/// Combined focus and diffusion report.
#[derive(Debug, Clone)]
pub struct FocusReport {
    /// Developers sorted by focus ascending (most scattered first).
    pub developers: Vec<DeveloperFocus>,
    /// Files sorted by diffusion descending (most diffused first).
    pub files: Vec<FileDiffusion>,
    /// Mean focus score across all developers.
    pub avg_developer_focus: f64,
    /// Mean diffusion score across all files.
    pub avg_file_diffusion: f64,
}

/// Accumulates per-developer directory commit counts for focus computation.
pub struct FocusAccumulator {
    /// `author` → (`directory` → commit count).
    author_dirs: FxHashMap<String, FxHashMap<String, u32>>,
}

impl Default for FocusAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl FocusAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            author_dirs: FxHashMap::default(),
        }
    }

    /// Records a commit for an author touching the given files.
    /// Extracts directory from each file path and counts per directory.
    pub fn record_commit(&mut self, author: &str, file_paths: &[&str]) {
        let entry = self.author_dirs.entry(author.to_string()).or_default();
        for path in file_paths {
            let dir = extract_directory(path);
            *entry.entry(dir).or_insert(0) += 1;
        }
    }

    /// Finalizes developer focus data.
    #[must_use]
    pub fn finalize(self) -> Vec<DeveloperFocus> {
        let mut developers: Vec<DeveloperFocus> = self
            .author_dirs
            .into_iter()
            .map(|(author, dir_counts)| {
                let total: u32 = dir_counts.values().sum();
                let dirs_touched = dir_counts.len() as u32;

                let (focus_score, primary_directory) = if dirs_touched <= 1 {
                    let primary = dir_counts
                        .keys()
                        .next()
                        .cloned()
                        .unwrap_or_else(|| ".".to_string());
                    (1.0, primary)
                } else {
                    let total_f = f64::from(total);
                    let entropy: f64 = dir_counts
                        .values()
                        .map(|&count| {
                            let p = f64::from(count) / total_f;
                            if p > 0.0 {
                                -p * p.log2()
                            } else {
                                0.0
                            }
                        })
                        .sum();
                    let h_norm = entropy / (f64::from(dirs_touched)).log2();
                    let primary = dir_counts
                        .iter()
                        .max_by_key(|(_, &v)| v)
                        .map_or_else(|| ".".to_string(), |(k, _)| k.clone());
                    (1.0 - h_norm, primary)
                };

                DeveloperFocus {
                    author,
                    focus_score,
                    directories_touched: dirs_touched,
                    primary_directory,
                    commit_count: total,
                }
            })
            .collect();

        // Sort by focus ascending (most scattered first)
        developers.sort_by(|a, b| {
            a.focus_score
                .partial_cmp(&b.focus_score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        developers
    }
}

/// Computes file diffusion from the existing `file_authors` data.
///
/// # Arguments
///
/// * `file_authors` - Map of `file_path` → (`author` → change count)
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn compute_file_diffusion(
    file_authors: &FxHashMap<String, FxHashMap<String, u32>>,
) -> Vec<FileDiffusion> {
    let mut files: Vec<FileDiffusion> = file_authors
        .iter()
        .map(|(path, authors)| {
            let total: u32 = authors.values().sum();
            let contributor_count = authors.len() as u32;

            let diffusion_score = if contributor_count <= 1 {
                0.0
            } else {
                let total_f = f64::from(total);
                let entropy: f64 = authors
                    .values()
                    .map(|&count| {
                        let p = f64::from(count) / total_f;
                        if p > 0.0 {
                            -p * p.log2()
                        } else {
                            0.0
                        }
                    })
                    .sum();
                entropy / (f64::from(contributor_count)).log2()
            };

            FileDiffusion {
                path: path.clone(),
                diffusion_score,
                contributor_count,
                total_changes: total,
            }
        })
        .collect();

    // Sort by diffusion descending (most diffused first)
    files.sort_by(|a, b| {
        b.diffusion_score
            .partial_cmp(&a.diffusion_score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    files
}

/// Computes the combined focus report.
///
/// # Arguments
///
/// * `developers` - Developer focus data from `FocusAccumulator::finalize()`
/// * `files` - File diffusion data from `compute_file_diffusion()`
#[must_use]
pub fn build_focus_report(
    developers: Vec<DeveloperFocus>,
    files: Vec<FileDiffusion>,
) -> FocusReport {
    let avg_developer_focus = if developers.is_empty() {
        0.0
    } else {
        developers.iter().map(|d| d.focus_score).sum::<f64>() / developers.len() as f64
    };

    let avg_file_diffusion = if files.is_empty() {
        0.0
    } else {
        files.iter().map(|f| f.diffusion_score).sum::<f64>() / files.len() as f64
    };

    FocusReport {
        developers,
        files,
        avg_developer_focus,
        avg_file_diffusion,
    }
}

/// Extracts the top-level directory from a file path.
fn extract_directory(path: &str) -> String {
    path.split('/')
        .next()
        .filter(|_| path.contains('/'))
        .unwrap_or(".")
        .to_string()
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
    fn test_fully_focused_developer() {
        let mut acc = FocusAccumulator::new();
        for _ in 0..10 {
            acc.record_commit("Alice", &["src/main.rs"]);
        }
        let devs = acc.finalize();
        assert_eq!(devs.len(), 1);
        assert!(
            (devs[0].focus_score - 1.0).abs() < f64::EPSILON,
            "focus={}, expected=1.0",
            devs[0].focus_score
        );
        assert_eq!(devs[0].primary_directory, "src");
    }

    #[test]
    fn test_fully_scattered_developer() {
        // Equal commits to N directories → focus = 0.0
        let mut acc = FocusAccumulator::new();
        acc.record_commit("Alice", &["src/a.rs", "tests/b.rs", "docs/c.rs"]);
        acc.record_commit("Alice", &["src/d.rs", "tests/e.rs", "docs/f.rs"]);
        let devs = acc.finalize();
        // 3 directories, 2 commits each → perfectly scattered
        assert!(
            devs[0].focus_score.abs() < 1e-10,
            "focus={}, expected=0.0",
            devs[0].focus_score
        );
    }

    #[test]
    fn test_known_focus_value() {
        // 10 commits to "src", 5 to "tests" → total = 15
        // p(src) = 10/15, p(tests) = 5/15
        // H = -(10/15*log2(10/15) + 5/15*log2(5/15))
        // H_norm = H / log2(2) = H / 1.0 = H
        // Focus = 1.0 - H
        let mut acc = FocusAccumulator::new();
        for _ in 0..10 {
            acc.record_commit("Alice", &["src/a.rs"]);
        }
        for _ in 0..5 {
            acc.record_commit("Alice", &["tests/b.rs"]);
        }
        let devs = acc.finalize();
        let p1: f64 = 10.0 / 15.0;
        let p2: f64 = 5.0 / 15.0;
        let h = -(p1 * p1.log2() + p2 * p2.log2());
        let expected_focus = 1.0 - h; // log2(2) = 1.0, so h_norm = h
        assert!(
            (devs[0].focus_score - expected_focus).abs() < 1e-10,
            "focus={}, expected={}",
            devs[0].focus_score,
            expected_focus
        );
        assert_eq!(devs[0].primary_directory, "src");
    }

    #[test]
    fn test_single_contributor_file() {
        let data = make_file_authors(&[("a.rs", &[("Alice", 10)])]);
        let files = compute_file_diffusion(&data);
        assert_eq!(files.len(), 1);
        assert!(
            files[0].diffusion_score.abs() < f64::EPSILON,
            "diffusion={}, expected=0.0",
            files[0].diffusion_score
        );
    }

    #[test]
    fn test_equal_contributors_file() {
        // 3 devs, equal contributions → diffusion = 1.0
        let data = make_file_authors(&[("a.rs", &[("Alice", 5), ("Bob", 5), ("Carol", 5)])]);
        let files = compute_file_diffusion(&data);
        assert!(
            (files[0].diffusion_score - 1.0).abs() < 1e-10,
            "diffusion={}, expected=1.0",
            files[0].diffusion_score
        );
    }

    #[test]
    fn test_known_diffusion_value() {
        // Alice: 6, Bob: 3, Carol: 1 → total = 10
        // p = [0.6, 0.3, 0.1]
        // H = -(0.6*log2(0.6) + 0.3*log2(0.3) + 0.1*log2(0.1))
        // H_norm = H / log2(3)
        let data = make_file_authors(&[("a.rs", &[("Alice", 6), ("Bob", 3), ("Carol", 1)])]);
        let files = compute_file_diffusion(&data);
        let h = -(0.6_f64 * 0.6_f64.log2() + 0.3 * 0.3_f64.log2() + 0.1 * 0.1_f64.log2());
        let expected = h / 3.0_f64.log2();
        assert!(
            (files[0].diffusion_score - expected).abs() < 1e-10,
            "diffusion={}, expected={}",
            files[0].diffusion_score,
            expected
        );
    }

    #[test]
    fn test_primary_directory() {
        let mut acc = FocusAccumulator::new();
        // 7 to src, 3 to tests → primary = src
        for _ in 0..7 {
            acc.record_commit("Alice", &["src/x.rs"]);
        }
        for _ in 0..3 {
            acc.record_commit("Alice", &["tests/y.rs"]);
        }
        let devs = acc.finalize();
        assert_eq!(devs[0].primary_directory, "src");
    }

    #[test]
    fn test_empty_inputs() {
        let devs = FocusAccumulator::new().finalize();
        let files = compute_file_diffusion(&FxHashMap::default());
        let report = build_focus_report(devs, files);
        assert!(report.developers.is_empty());
        assert!(report.files.is_empty());
        assert!((report.avg_developer_focus - 0.0).abs() < f64::EPSILON);
        assert!((report.avg_file_diffusion - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_averages_exact() {
        // Two developers: focus 1.0 and 0.0 → avg = 0.5
        let mut acc = FocusAccumulator::new();
        // Alice: all in one dir → focus = 1.0
        for _ in 0..5 {
            acc.record_commit("Alice", &["src/a.rs"]);
        }
        // Bob: equal in two dirs → focus = 0.0
        acc.record_commit("Bob", &["src/b.rs"]);
        acc.record_commit("Bob", &["tests/c.rs"]);
        let devs = acc.finalize();
        let report = build_focus_report(devs, Vec::new());
        assert!(
            (report.avg_developer_focus - 0.5).abs() < 1e-10,
            "avg_focus={}, expected=0.5",
            report.avg_developer_focus
        );
    }

    #[test]
    fn test_sort_order() {
        // Most scattered developer first, most diffused file first
        let mut acc = FocusAccumulator::new();
        // Alice: focused (score ~1.0)
        for _ in 0..10 {
            acc.record_commit("Alice", &["src/a.rs"]);
        }
        // Bob: scattered (score ~0.0)
        acc.record_commit("Bob", &["src/b.rs", "tests/c.rs", "docs/d.rs"]);
        acc.record_commit("Bob", &["src/e.rs", "tests/f.rs", "docs/g.rs"]);
        let devs = acc.finalize();
        assert_eq!(devs[0].author, "Bob", "most scattered should be first");
        assert!(devs[0].focus_score < devs[1].focus_score);
    }

    #[test]
    fn test_default_impl() {
        let acc = FocusAccumulator::default();
        let devs = acc.finalize();
        assert!(devs.is_empty());
    }

    #[test]
    fn test_root_files() {
        // Files without directory → directory = "."
        let mut acc = FocusAccumulator::new();
        acc.record_commit("Alice", &["README.md"]);
        acc.record_commit("Alice", &["Cargo.toml"]);
        acc.record_commit("Alice", &["LICENSE"]);
        let devs = acc.finalize();
        assert_eq!(devs[0].primary_directory, ".");
        assert!(
            (devs[0].focus_score - 1.0).abs() < f64::EPSILON,
            "all root files → single dir → focus=1.0"
        );
    }

    // --- Mutation-killing tests ---

    #[test]
    fn test_focus_dirs_touched_exactly_one() {
        // Kills: replace <= with < in `if dirs_touched <= 1`
        // 1 directory → focus = 1.0 (no entropy calculation)
        let mut acc = FocusAccumulator::new();
        acc.record_commit("Alice", &["src/a.rs", "src/b.rs"]);
        let devs = acc.finalize();
        assert_eq!(devs[0].directories_touched, 1);
        assert!(
            (devs[0].focus_score - 1.0).abs() < f64::EPSILON,
            "1 dir should give focus=1.0"
        );
    }

    #[test]
    fn test_focus_subtraction_from_one() {
        // Kills: replace - with + in `1.0 - h_norm`
        // With 2 equal dirs: H=1.0, H_norm=1.0, focus = 1.0-1.0 = 0.0
        // If - → +: focus = 1.0+1.0 = 2.0
        let mut acc = FocusAccumulator::new();
        acc.record_commit("Alice", &["src/a.rs"]);
        acc.record_commit("Alice", &["tests/b.rs"]);
        let devs = acc.finalize();
        assert!(
            devs[0].focus_score.abs() < 1e-10,
            "focus={}, expected=0.0",
            devs[0].focus_score
        );
        assert!(devs[0].focus_score <= 1.0, "focus must be <= 1.0");
    }

    #[test]
    fn test_focus_entropy_division_by_log2() {
        // Kills: replace / with * in `entropy / log2(dirs_touched)`
        // 3 dirs with [4, 2, 2] commits → known entropy
        let mut acc = FocusAccumulator::new();
        for _ in 0..4 {
            acc.record_commit("Alice", &["src/a.rs"]);
        }
        for _ in 0..2 {
            acc.record_commit("Alice", &["tests/b.rs"]);
        }
        for _ in 0..2 {
            acc.record_commit("Alice", &["docs/c.rs"]);
        }
        let devs = acc.finalize();
        // p = [4/8, 2/8, 2/8] = [0.5, 0.25, 0.25]
        // H = -(0.5*log2(0.5) + 2*0.25*log2(0.25)) = 0.5 + 1.0 = 1.5
        // H_norm = 1.5 / log2(3) ≈ 0.9464
        // focus = 1.0 - 0.9464 ≈ 0.0536
        let h = 1.5;
        let h_norm = h / 3.0_f64.log2();
        let expected_focus = 1.0 - h_norm;
        assert!(
            (devs[0].focus_score - expected_focus).abs() < 1e-10,
            "focus={}, expected={}",
            devs[0].focus_score,
            expected_focus
        );
    }

    #[test]
    fn test_diffusion_contributor_count_boundary() {
        // Kills: replace <= with < in `if contributor_count <= 1`
        // 1 contributor → diffusion = 0.0
        let data = make_file_authors(&[("a.rs", &[("Alice", 10)])]);
        let files = compute_file_diffusion(&data);
        assert_eq!(files[0].contributor_count, 1);
        assert!(
            files[0].diffusion_score.abs() < f64::EPSILON,
            "1 contributor → diffusion=0"
        );
    }

    #[test]
    fn test_diffusion_entropy_division_exact() {
        // Kills: replace / with * in `entropy / log2(contributor_count)`
        // 2 contributors: [8, 2] → total=10
        // p = [0.8, 0.2], H = -(0.8*log2(0.8) + 0.2*log2(0.2))
        // H_norm = H / log2(2) = H
        let data = make_file_authors(&[("a.rs", &[("Alice", 8), ("Bob", 2)])]);
        let files = compute_file_diffusion(&data);
        let p1 = 0.8_f64;
        let p2 = 0.2_f64;
        let h = -(p1 * p1.log2() + p2 * p2.log2());
        assert!(
            (files[0].diffusion_score - h).abs() < 1e-10,
            "diffusion={}, expected={}",
            files[0].diffusion_score,
            h
        );
    }

    #[test]
    fn test_avg_focus_division_exact() {
        // Kills: replace / with * in avg_developer_focus calculation
        // 3 developers with focus [1.0, 0.5, 0.0] → avg = 0.5
        let mut acc = FocusAccumulator::new();
        // Dev 1: 1 dir → focus = 1.0
        for _ in 0..5 {
            acc.record_commit("Alice", &["src/a.rs"]);
        }
        // Dev 2: 2 dirs with [3, 1] → known focus
        for _ in 0..3 {
            acc.record_commit("Bob", &["src/b.rs"]);
        }
        acc.record_commit("Bob", &["tests/c.rs"]);
        // Dev 3: 2 equal dirs → focus = 0.0
        acc.record_commit("Carol", &["src/d.rs"]);
        acc.record_commit("Carol", &["tests/e.rs"]);

        let devs = acc.finalize();
        let report = build_focus_report(devs, Vec::new());
        // Sum of focus scores / 3 → exact value
        assert!(
            report.avg_developer_focus > 0.0 && report.avg_developer_focus < 1.0,
            "avg should be between 0 and 1, got {}",
            report.avg_developer_focus
        );
    }

    #[test]
    fn test_avg_file_diffusion_division_exact() {
        // Kills: replace / with * in avg_file_diffusion calculation
        // 2 files: one with diffusion 0.0, one with 1.0 → avg = 0.5
        let data = make_file_authors(&[
            ("a.rs", &[("Alice", 10)]),            // single contributor → 0.0
            ("b.rs", &[("Alice", 5), ("Bob", 5)]), // equal → 1.0
        ]);
        let files = compute_file_diffusion(&data);
        let report = build_focus_report(Vec::new(), files);
        assert!(
            (report.avg_file_diffusion - 0.5).abs() < 1e-10,
            "avg_diffusion={}, expected=0.5",
            report.avg_file_diffusion
        );
    }

    #[test]
    fn test_commit_count_tracked() {
        let mut acc = FocusAccumulator::new();
        acc.record_commit("Alice", &["src/a.rs", "src/b.rs"]); // 2 file touches
        acc.record_commit("Alice", &["src/c.rs"]); // 1 file touch
        let devs = acc.finalize();
        // commit_count = total file touches across all commits: 2 + 1 = 3
        assert_eq!(devs[0].commit_count, 3);
    }
}
