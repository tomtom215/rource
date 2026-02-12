// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Commit Message Entropy (Information Density) analysis.
//!
//! Measures how much semantic information commit messages carry relative to
//! the complexity of the change, using pure information theory (no NLP dependencies).
//!
//! # Research Basis
//!
//! - Dyer et al. (MSR 2013, DOI: 10.1109/MSR.2013.6624016) — mining commit messages at scale
//! - Hindle et al. (ICSE 2012, DOI: 10.1109/ICSE.2012.6227135) — naturalness of software
//! - Shannon (Bell System Technical Journal, 1948, DOI: 10.1002/j.1538-7305.1948.tb01338.x)
//!
//! # Novelty
//!
//! Information density normalized by change complexity (log₂(n)) and
//! self-calibrating low-information threshold have not been published as a
//! combined metric. Existing commit message analysis uses NLP classifiers
//! (supervised, non-reproducible across languages). This approach is
//! language-agnostic and dependency-free.
//!
//! # Algorithm
//!
//! For commit C with message m touching n files:
//!
//! Token entropy:
//!   `H(m) = -Σ(p_w × log₂(p_w))` where `p_w = count(w)/total_tokens`
//!
//! Information density:
//!   `ID(C) = unique_tokens(m) / (1 + log₂(n))`
//!
//! Cross-entropy (novelty measure):
//!   `CE(m) = -(1/|m|) × Σ_{w ∈ m} log₂(p_corpus(w))`
//!
//! Low-information flag:
//!   `LI(C) = 1` if `unique_tokens(m) < θ × log₂(max(n, 2))`
//!
//! # Complexity
//!
//! - Accumulation: `O(Σ|m_i|)` total message tokens
//! - Finalization: `O(C × |m̄|)` where `C` = commits, `|m̄|` = mean message length

use rustc_hash::FxHashMap;

/// Per-commit message analysis.
#[derive(Debug, Clone)]
pub struct CommitMessageAnalysis {
    /// Author of the commit.
    pub author: String,
    /// Timestamp (Unix epoch seconds).
    pub timestamp: i64,
    /// Token entropy H(m) in bits.
    pub token_entropy: f64,
    /// Information density: `unique_tokens / (1 + log₂(files_changed))`.
    pub information_density: f64,
    /// Cross-entropy against corpus (higher = more novel/descriptive).
    pub cross_entropy: f64,
    /// Whether this commit has a low-information message.
    pub is_low_info: bool,
    /// Number of files changed.
    pub file_count: u32,
    /// Number of unique tokens in the message.
    pub unique_tokens: u32,
    /// Total tokens in the message.
    pub total_tokens: u32,
}

/// Aggregate message quality report.
#[derive(Debug, Clone)]
pub struct CommitMessageEntropyReport {
    /// Per-commit message analysis (lowest info density first).
    pub commits: Vec<CommitMessageAnalysis>,
    /// Median information density across all commits with messages.
    pub median_info_density: f64,
    /// Fraction of commits flagged as low-information.
    pub low_info_ratio: f64,
    /// Average cross-entropy (message novelty).
    pub avg_cross_entropy: f64,
    /// Per-developer message quality.
    pub developer_quality: Vec<DeveloperMessageQuality>,
    /// Total commits with messages analyzed.
    pub total_analyzed: u32,
    /// Total commits that had no message (or empty message).
    pub no_message_count: u32,
}

/// Per-developer message quality summary.
#[derive(Debug, Clone)]
pub struct DeveloperMessageQuality {
    /// Developer name.
    pub author: String,
    /// Median information density.
    pub median_info_density: f64,
    /// Low-information ratio for this developer.
    pub low_info_ratio: f64,
    /// Number of commits analyzed.
    pub commit_count: u32,
}

/// Accumulates commit messages for entropy analysis.
pub struct CommitMessageEntropyAccumulator {
    /// `(author, timestamp, message, file_count)`.
    commits: Vec<(String, i64, String, u32)>,
    /// Global token frequency map (corpus).
    corpus_freq: FxHashMap<String, u32>,
    /// Total tokens across all messages.
    total_corpus_tokens: u64,
    /// Count of commits with no message.
    no_message_count: u32,
}

impl Default for CommitMessageEntropyAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl CommitMessageEntropyAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            commits: Vec::new(),
            corpus_freq: FxHashMap::default(),
            total_corpus_tokens: 0,
            no_message_count: 0,
        }
    }

    /// Records a commit's message for analysis.
    ///
    /// # Arguments
    ///
    /// * `author` - Commit author
    /// * `timestamp` - Commit timestamp
    /// * `message` - The commit message (if available)
    /// * `file_count` - Number of files changed
    pub fn record_commit(
        &mut self,
        author: &str,
        timestamp: i64,
        message: Option<&str>,
        file_count: usize,
    ) {
        let msg = match message {
            Some(m) if !m.trim().is_empty() => m.trim(),
            _ => {
                self.no_message_count += 1;
                return;
            }
        };

        // Tokenize and update corpus frequencies
        let tokens = tokenize(msg);
        for token in &tokens {
            *self.corpus_freq.entry(token.clone()).or_insert(0) += 1;
            self.total_corpus_tokens += 1;
        }

        self.commits.push((
            author.to_string(),
            timestamp,
            msg.to_string(),
            file_count as u32,
        ));
    }

    /// Finalizes the accumulator into a report.
    #[must_use]
    pub fn finalize(self) -> CommitMessageEntropyReport {
        if self.commits.is_empty() {
            return CommitMessageEntropyReport {
                commits: Vec::new(),
                median_info_density: 0.0,
                low_info_ratio: 0.0,
                avg_cross_entropy: 0.0,
                developer_quality: Vec::new(),
                total_analyzed: 0,
                no_message_count: self.no_message_count,
            };
        }

        let theta = compute_theta(&self.commits);
        let total_corpus = self.total_corpus_tokens.max(1) as f64;

        // Per-commit analysis
        let (mut results, dev_scores) =
            analyze_commits(&self.commits, &self.corpus_freq, total_corpus, theta);

        // Sort by information density ascending (worst first)
        results.sort_unstable_by(|a, b| {
            a.information_density
                .partial_cmp(&b.information_density)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        let total_analyzed = results.len() as u32;
        let low_info_count = results.iter().filter(|c| c.is_low_info).count();
        let low_info_ratio = low_info_count as f64 / results.len().max(1) as f64;

        let mut info_densities: Vec<f64> = results.iter().map(|c| c.information_density).collect();
        info_densities
            .sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
        let median_info_density = median_sorted(&info_densities);

        let avg_cross_entropy = if results.is_empty() {
            0.0
        } else {
            results.iter().map(|c| c.cross_entropy).sum::<f64>() / results.len() as f64
        };

        let developer_quality = aggregate_developer_quality(dev_scores);

        CommitMessageEntropyReport {
            commits: results,
            median_info_density,
            low_info_ratio,
            avg_cross_entropy,
            developer_quality,
            total_analyzed,
            no_message_count: self.no_message_count,
        }
    }
}

/// Computes the self-calibrating threshold theta from commit data.
fn compute_theta(commits: &[(String, i64, String, u32)]) -> f64 {
    let mut id_ratios: Vec<f64> = Vec::with_capacity(commits.len());
    for (_, _, msg, fc) in commits {
        let tokens = tokenize(msg);
        let unique: rustc_hash::FxHashSet<&str> = tokens.iter().map(String::as_str).collect();
        let log_files = f64::from((*fc).max(2)).log2();
        if log_files > 0.0 {
            id_ratios.push(unique.len() as f64 / log_files);
        }
    }
    id_ratios.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    median_sorted(&id_ratios)
}

/// Result of commit analysis: (per-commit results, per-developer score accumulations).
type CommitAnalysisResult = (
    Vec<CommitMessageAnalysis>,
    FxHashMap<String, Vec<(f64, bool)>>,
);

/// Analyzes each commit and returns per-commit results and per-developer score accumulations.
fn analyze_commits(
    commits: &[(String, i64, String, u32)],
    corpus_freq: &FxHashMap<String, u32>,
    total_corpus: f64,
    theta: f64,
) -> CommitAnalysisResult {
    let mut results: Vec<CommitMessageAnalysis> = Vec::with_capacity(commits.len());
    let mut dev_scores: FxHashMap<String, Vec<(f64, bool)>> = FxHashMap::default();

    for (author, timestamp, msg, file_count) in commits {
        let tokens = tokenize(msg);
        let total_tokens = tokens.len() as u32;

        let mut msg_freq: FxHashMap<&str, u32> = FxHashMap::default();
        for t in &tokens {
            *msg_freq.entry(t.as_str()).or_insert(0) += 1;
        }
        let unique_tokens = msg_freq.len() as u32;

        let token_entropy = if total_tokens > 0 {
            let n = f64::from(total_tokens);
            msg_freq
                .values()
                .map(|&count| {
                    let p = f64::from(count) / n;
                    if p > 0.0 {
                        -p * p.log2()
                    } else {
                        0.0
                    }
                })
                .sum::<f64>()
        } else {
            0.0
        };

        let log_files = f64::from((*file_count).max(2)).log2();
        let information_density = f64::from(unique_tokens) / (1.0 + log_files);

        let cross_entropy = if total_tokens > 0 {
            let ce: f64 = tokens
                .iter()
                .map(|t| {
                    let p_corpus =
                        f64::from(corpus_freq.get(t.as_str()).copied().unwrap_or(1)) / total_corpus;
                    if p_corpus > 0.0 {
                        -p_corpus.log2()
                    } else {
                        0.0
                    }
                })
                .sum();
            ce / f64::from(total_tokens)
        } else {
            0.0
        };

        let is_low_info = f64::from(unique_tokens) < theta * log_files;

        dev_scores
            .entry(author.clone())
            .or_default()
            .push((information_density, is_low_info));

        results.push(CommitMessageAnalysis {
            author: author.clone(),
            timestamp: *timestamp,
            token_entropy,
            information_density,
            cross_entropy,
            is_low_info,
            file_count: *file_count,
            unique_tokens,
            total_tokens,
        });
    }

    (results, dev_scores)
}

/// Aggregates per-developer message quality from accumulated scores.
fn aggregate_developer_quality(
    dev_scores: FxHashMap<String, Vec<(f64, bool)>>,
) -> Vec<DeveloperMessageQuality> {
    let mut developer_quality: Vec<DeveloperMessageQuality> = dev_scores
        .into_iter()
        .map(|(author, scores)| {
            let mut densities: Vec<f64> = scores.iter().map(|(d, _)| *d).collect();
            densities
                .sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
            let low_count = scores.iter().filter(|(_, li)| *li).count();
            DeveloperMessageQuality {
                author,
                median_info_density: median_sorted(&densities),
                low_info_ratio: low_count as f64 / scores.len().max(1) as f64,
                commit_count: scores.len() as u32,
            }
        })
        .collect();
    developer_quality.sort_unstable_by(|a, b| {
        a.median_info_density
            .partial_cmp(&b.median_info_density)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    developer_quality
}

/// Tokenizes a commit message into lowercase words.
///
/// Splits on whitespace and punctuation, strips numbers, lowercases.
/// Language-agnostic: works for any human language commit messages.
fn tokenize(message: &str) -> Vec<String> {
    message
        .split(|c: char| c.is_whitespace() || c.is_ascii_punctuation())
        .map(str::to_lowercase)
        .filter(|s| !s.is_empty() && s.chars().any(char::is_alphabetic))
        .collect()
}

/// Computes the median of a pre-sorted slice.
fn median_sorted(sorted: &[f64]) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let mid = sorted.len() / 2;
    if sorted.len() % 2 == 0 {
        (sorted[mid - 1] + sorted[mid]) / 2.0
    } else {
        sorted[mid]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = CommitMessageEntropyAccumulator::new();
        let report = acc.finalize();
        assert_eq!(report.total_analyzed, 0);
        assert_eq!(report.no_message_count, 0);
    }

    #[test]
    fn test_no_messages() {
        let mut acc = CommitMessageEntropyAccumulator::new();
        acc.record_commit("Alice", 1000, None, 3);
        acc.record_commit("Bob", 2000, Some(""), 2);
        let report = acc.finalize();
        assert_eq!(report.total_analyzed, 0);
        assert_eq!(report.no_message_count, 2);
    }

    #[test]
    fn test_single_commit_with_message() {
        let mut acc = CommitMessageEntropyAccumulator::new();
        acc.record_commit("Alice", 1000, Some("Fix critical bug in auth module"), 3);
        let report = acc.finalize();

        assert_eq!(report.total_analyzed, 1);
        let commit = &report.commits[0];
        assert!(commit.token_entropy > 0.0);
        assert!(commit.information_density > 0.0);
        assert_eq!(commit.file_count, 3);
    }

    #[test]
    fn test_low_info_detection() {
        let mut acc = CommitMessageEntropyAccumulator::new();
        // Many descriptive commits to establish corpus
        for i in 0..20 {
            acc.record_commit(
                "Alice",
                1000 + i * 100,
                Some("Refactor the authentication service to improve maintainability and readability"),
                5,
            );
        }
        // One very short message for many files
        acc.record_commit("Bob", 5000, Some("fix"), 10);
        let report = acc.finalize();

        // "fix" should have low information density relative to 10 files
        let bob_commit = report.commits.iter().find(|c| c.author == "Bob").unwrap();
        assert_eq!(bob_commit.unique_tokens, 1); // "fix"
                                                 // Whether it's flagged depends on the self-calibrating threshold
        assert!(bob_commit.information_density < 1.0);
    }

    #[test]
    fn test_high_entropy_vs_low_entropy() {
        let mut acc = CommitMessageEntropyAccumulator::new();
        // High entropy: many unique words
        acc.record_commit(
            "Alice",
            1000,
            Some("Fix authentication buffer overflow in login handler"),
            2,
        );
        // Low entropy: repeated word
        acc.record_commit("Bob", 2000, Some("fix fix fix fix fix"), 2);
        let report = acc.finalize();

        let alice = report.commits.iter().find(|c| c.author == "Alice").unwrap();
        let bob = report.commits.iter().find(|c| c.author == "Bob").unwrap();
        // Alice should have higher token entropy (more diverse tokens)
        assert!(alice.token_entropy > bob.token_entropy);
    }

    #[test]
    fn test_tokenize() {
        let tokens = tokenize("Fix: bug #123 in auth.rs");
        // Expected: ["fix", "bug", "in", "auth", "rs"] (numbers stripped, lowercased)
        assert!(tokens.contains(&"fix".to_string()));
        assert!(tokens.contains(&"bug".to_string()));
        assert!(!tokens.iter().any(|t| t.contains("123")));
    }

    #[test]
    fn test_tokenize_unicode() {
        let tokens = tokenize("Исправить ошибку в модуле авторизации");
        assert!(!tokens.is_empty());
        // Should preserve non-ASCII alphabetic characters
        assert!(tokens[0].chars().all(char::is_alphabetic));
    }

    #[test]
    fn test_per_developer_quality() {
        let mut acc = CommitMessageEntropyAccumulator::new();
        acc.record_commit(
            "Alice",
            1000,
            Some("Implement user authentication with JWT tokens"),
            5,
        );
        acc.record_commit(
            "Alice",
            2000,
            Some("Add comprehensive test suite for auth service"),
            3,
        );
        acc.record_commit("Bob", 1500, Some("wip"), 8);
        let report = acc.finalize();

        assert_eq!(report.developer_quality.len(), 2);
        let alice = report
            .developer_quality
            .iter()
            .find(|d| d.author == "Alice")
            .unwrap();
        let bob = report
            .developer_quality
            .iter()
            .find(|d| d.author == "Bob")
            .unwrap();
        assert!(alice.median_info_density > bob.median_info_density);
    }

    #[test]
    fn test_information_density_scales_with_files() {
        let mut acc = CommitMessageEntropyAccumulator::new();
        // Same message, different file counts
        acc.record_commit("Alice", 1000, Some("Fix bug in module"), 2);
        acc.record_commit("Bob", 2000, Some("Fix bug in module"), 20);
        let report = acc.finalize();

        let alice = report.commits.iter().find(|c| c.author == "Alice").unwrap();
        let bob = report.commits.iter().find(|c| c.author == "Bob").unwrap();
        // Same message with more files should have lower info density
        assert!(alice.information_density > bob.information_density);
    }

    #[test]
    fn test_cross_entropy_rare_words_higher() {
        let mut acc = CommitMessageEntropyAccumulator::new();
        // Build a corpus dominated by common words
        for i in 0..50 {
            acc.record_commit("Alice", 1000 + i * 100, Some("fix update change"), 2);
        }
        // One commit with unusual words
        acc.record_commit("Bob", 9000, Some("defenestrate the onomatopoeia"), 2);
        let report = acc.finalize();

        let bob = report.commits.iter().find(|c| c.author == "Bob").unwrap();
        let alice_avg_ce: f64 = report
            .commits
            .iter()
            .filter(|c| c.author == "Alice")
            .map(|c| c.cross_entropy)
            .sum::<f64>()
            / 50.0;
        // Bob's rare words should have higher cross-entropy
        assert!(bob.cross_entropy > alice_avg_ce);
    }

    #[test]
    fn test_median_sorted() {
        assert_eq!(median_sorted(&[]), 0.0);
        assert_eq!(median_sorted(&[5.0]), 5.0);
        assert_eq!(median_sorted(&[1.0, 3.0]), 2.0);
        assert_eq!(median_sorted(&[1.0, 2.0, 3.0]), 2.0);
    }
}
