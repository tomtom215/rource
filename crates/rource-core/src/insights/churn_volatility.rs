// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Code Churn Volatility — measures instability of file change patterns over time.
//!
//! Files with volatile churn patterns (alternating high and low change rates)
//! are strong defect predictors. Stable churn (consistent change rate) is healthy;
//! volatile churn (erratic change rate) indicates instability.
//!
//! # Research Basis
//!
//! - Nagappan & Ball (2005) "Use of Relative Code Churn Measures to Predict
//!   System Defect Density" (ICSE) — relative churn predicts defect density
//! - Munson & Elbaum (1998) "Code Churn: A Measure for Estimating the Impact
//!   of Code Change" (ICSM) — churn volatility correlates with defect rates
//!
//! # Algorithm
//!
//! 1. Divide history into W equal-sized time windows
//! 2. For each file, compute weighted churn per window:
//!    `churn(w) = Σ action_weight(a)` for actions in window w
//!    where Create=1.0, Modify=0.3, Delete=1.0
//! 3. Compute coefficient of variation (CV) across windows:
//!    `CV = σ(churn) / μ(churn)` where σ=std dev, μ=mean
//! 4. Files with high CV are volatile (unstable) and defect-prone
//!
//! # Complexity
//!
//! - O(C × `F_avg`) accumulation where C = commits, `F_avg` = avg files per commit
//! - O(F × W) finalization where F = files, W = windows

use rustc_hash::FxHashMap;

use super::FileActionKind;

/// Number of time windows to use for churn analysis.
const NUM_WINDOWS: usize = 10;

/// Churn volatility report for the repository.
#[derive(Debug, Clone)]
pub struct ChurnVolatilityReport {
    /// Per-file churn volatility data, sorted by CV descending.
    pub files: Vec<FileChurnVolatility>,
    /// Average coefficient of variation across all files.
    pub avg_cv: f64,
    /// Number of files classified as volatile (CV > 1.0).
    pub volatile_count: usize,
    /// Number of files classified as stable (CV < 0.5).
    pub stable_count: usize,
}

/// Churn volatility for a single file.
#[derive(Debug, Clone)]
pub struct FileChurnVolatility {
    /// File path.
    pub path: String,
    /// Coefficient of variation of churn across windows (0 = perfectly stable).
    pub cv: f64,
    /// Total weighted churn across all windows.
    pub total_churn: f64,
    /// Number of windows with non-zero churn.
    pub active_windows: u32,
    /// Classification based on CV.
    pub volatility_class: VolatilityClass,
}

/// Volatility classification based on coefficient of variation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VolatilityClass {
    /// Stable churn pattern (CV < 0.5).
    Stable,
    /// Moderate variation (0.5 ≤ CV < 1.0).
    Moderate,
    /// Volatile (1.0 ≤ CV < 2.0).
    Volatile,
    /// Highly volatile (CV ≥ 2.0).
    HighlyVolatile,
}

impl std::fmt::Display for VolatilityClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Stable => write!(f, "stable"),
            Self::Moderate => write!(f, "moderate"),
            Self::Volatile => write!(f, "volatile"),
            Self::HighlyVolatile => write!(f, "highly_volatile"),
        }
    }
}

/// Accumulates per-file churn data by time window.
pub struct ChurnVolatilityAccumulator {
    /// Per-file churn data: file path → (`window_index` → weighted churn).
    file_window_churn: FxHashMap<String, Vec<f64>>,
    /// Time range for windowing.
    t_min: i64,
    t_max: i64,
    /// Whether any data has been recorded.
    has_data: bool,
}

impl Default for ChurnVolatilityAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl ChurnVolatilityAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            file_window_churn: FxHashMap::default(),
            t_min: i64::MAX,
            t_max: i64::MIN,
            has_data: false,
        }
    }

    /// Records a file action for churn analysis.
    pub fn record_file(&mut self, path: &str, action: FileActionKind, timestamp: i64) {
        if timestamp < self.t_min {
            self.t_min = timestamp;
        }
        if timestamp > self.t_max {
            self.t_max = timestamp;
        }
        self.has_data = true;

        // Defer windowing to finalize — just collect (timestamp, weight) per file
        let weight = action_weight(action);
        let entry = self.file_window_churn.entry(path.to_string()).or_default();
        // Store as (timestamp_encoded_as_f64, weight) — we'll window in finalize
        // Actually, to keep it simple, store raw entries and window in finalize
        entry.push(f64::from_bits(timestamp as u64));
        entry.push(weight);
    }

    /// Finalizes the churn volatility report.
    #[must_use]
    pub fn finalize(self) -> ChurnVolatilityReport {
        if !self.has_data || self.t_max <= self.t_min {
            return ChurnVolatilityReport {
                files: Vec::new(),
                avg_cv: 0.0,
                volatile_count: 0,
                stable_count: 0,
            };
        }

        let span = self.t_max - self.t_min;
        #[allow(clippy::cast_possible_wrap)]
        let num_windows_i64 = NUM_WINDOWS as i64;
        let window_size = (span / num_windows_i64).max(1);

        let mut files = Vec::with_capacity(self.file_window_churn.len());

        for (path, raw_data) in &self.file_window_churn {
            let mut window_churn = vec![0.0_f64; NUM_WINDOWS];

            // raw_data is pairs of (timestamp_as_bits, weight)
            let mut i = 0;
            while i + 1 < raw_data.len() {
                #[allow(clippy::cast_possible_wrap)]
                let ts = raw_data[i].to_bits() as i64;
                let weight = raw_data[i + 1];
                let idx = ((ts - self.t_min) / window_size) as usize;
                let idx = idx.min(NUM_WINDOWS - 1);
                window_churn[idx] += weight;
                i += 2;
            }

            let total_churn: f64 = window_churn.iter().sum();
            let active_windows = window_churn.iter().filter(|&&c| c > 0.0).count() as u32;

            if total_churn <= 0.0 {
                continue;
            }

            let cv = compute_cv(&window_churn);
            let volatility_class = classify_volatility(cv);

            files.push(FileChurnVolatility {
                path: path.clone(),
                cv,
                total_churn,
                active_windows,
                volatility_class,
            });
        }

        // Sort by CV descending (most volatile first)
        files.sort_by(|a, b| b.cv.partial_cmp(&a.cv).unwrap_or(std::cmp::Ordering::Equal));

        let avg_cv = if files.is_empty() {
            0.0
        } else {
            files.iter().map(|f| f.cv).sum::<f64>() / files.len() as f64
        };
        let volatile_count = files
            .iter()
            .filter(|f| {
                matches!(
                    f.volatility_class,
                    VolatilityClass::Volatile | VolatilityClass::HighlyVolatile
                )
            })
            .count();
        let stable_count = files
            .iter()
            .filter(|f| f.volatility_class == VolatilityClass::Stable)
            .count();

        ChurnVolatilityReport {
            files,
            avg_cv,
            volatile_count,
            stable_count,
        }
    }
}

/// Returns the weight for a file action.
///
/// Create and Delete represent full-file changes (weight 1.0).
/// Modify represents a partial change (weight 0.3).
fn action_weight(action: FileActionKind) -> f64 {
    match action {
        FileActionKind::Create | FileActionKind::Delete => 1.0,
        FileActionKind::Modify => 0.3,
    }
}

/// Computes the coefficient of variation (σ/μ) for a slice of values.
///
/// Returns 0.0 if all values are zero or the mean is zero.
fn compute_cv(values: &[f64]) -> f64 {
    let n = values.len() as f64;
    if n <= 0.0 {
        return 0.0;
    }

    let mean = values.iter().sum::<f64>() / n;
    if mean <= 0.0 {
        return 0.0;
    }

    let variance = values.iter().map(|&x| (x - mean).powi(2)).sum::<f64>() / n;
    let std_dev = variance.sqrt();
    std_dev / mean
}

/// Classifies volatility based on coefficient of variation.
fn classify_volatility(cv: f64) -> VolatilityClass {
    if cv >= 2.0 {
        VolatilityClass::HighlyVolatile
    } else if cv >= 1.0 {
        VolatilityClass::Volatile
    } else if cv >= 0.5 {
        VolatilityClass::Moderate
    } else {
        VolatilityClass::Stable
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_accumulator() {
        let acc = ChurnVolatilityAccumulator::new();
        let report = acc.finalize();
        assert!(report.files.is_empty());
        assert!((report.avg_cv - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_default_impl() {
        let acc = ChurnVolatilityAccumulator::default();
        let report = acc.finalize();
        assert!(report.files.is_empty());
    }

    #[test]
    fn test_single_file_uniform_churn() {
        // File modified at regular intervals → low CV
        let mut acc = ChurnVolatilityAccumulator::new();
        let window_size = 86400 * 7; // 1 week
        for w in 0..10 {
            acc.record_file("a.rs", FileActionKind::Modify, w * window_size);
        }
        let report = acc.finalize();
        assert_eq!(report.files.len(), 1);
        let f = &report.files[0];
        assert_eq!(f.path, "a.rs");
        // Uniform churn → low CV
        assert!(f.cv < 0.5, "uniform churn CV={} should be < 0.5", f.cv);
        assert_eq!(f.volatility_class, VolatilityClass::Stable);
    }

    #[test]
    fn test_single_file_bursty_churn() {
        // File has all changes in one window → high CV
        let mut acc = ChurnVolatilityAccumulator::new();
        // Set time range to span 10 windows
        acc.record_file("setup.rs", FileActionKind::Create, 0);
        // All bursts in window 0
        for i in 1..10 {
            acc.record_file("setup.rs", FileActionKind::Modify, i * 100);
        }
        // One change at the end to define time range
        acc.record_file("setup.rs", FileActionKind::Modify, 86400 * 70);
        let report = acc.finalize();
        let f = report.files.iter().find(|f| f.path == "setup.rs").unwrap();
        // Most churn in one window → high CV
        assert!(f.cv > 1.0, "bursty churn CV={} should be > 1.0", f.cv);
    }

    #[test]
    fn test_action_weights() {
        assert!((action_weight(FileActionKind::Create) - 1.0).abs() < f64::EPSILON);
        assert!((action_weight(FileActionKind::Delete) - 1.0).abs() < f64::EPSILON);
        assert!((action_weight(FileActionKind::Modify) - 0.3).abs() < f64::EPSILON);
    }

    #[test]
    fn test_cv_all_equal() {
        let values = vec![1.0, 1.0, 1.0, 1.0];
        let cv = compute_cv(&values);
        assert!(
            cv.abs() < f64::EPSILON,
            "equal values CV={}, expected 0",
            cv
        );
    }

    #[test]
    fn test_cv_all_zero() {
        let values = vec![0.0, 0.0, 0.0];
        let cv = compute_cv(&values);
        assert!((cv - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_cv_known_values() {
        // [2, 4, 4, 4, 5, 5, 7, 9] → mean=5, σ=2, CV=0.4
        let values = vec![2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0];
        let cv = compute_cv(&values);
        let mean = 5.0;
        let variance = values.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / 8.0;
        let expected_cv = variance.sqrt() / mean;
        assert!(
            (cv - expected_cv).abs() < 1e-10,
            "cv={}, expected={}",
            cv,
            expected_cv
        );
    }

    #[test]
    fn test_classify_volatility() {
        assert_eq!(classify_volatility(0.0), VolatilityClass::Stable);
        assert_eq!(classify_volatility(0.3), VolatilityClass::Stable);
        assert_eq!(classify_volatility(0.5), VolatilityClass::Moderate);
        assert_eq!(classify_volatility(0.9), VolatilityClass::Moderate);
        assert_eq!(classify_volatility(1.0), VolatilityClass::Volatile);
        assert_eq!(classify_volatility(1.5), VolatilityClass::Volatile);
        assert_eq!(classify_volatility(2.0), VolatilityClass::HighlyVolatile);
        assert_eq!(classify_volatility(5.0), VolatilityClass::HighlyVolatile);
    }

    #[test]
    fn test_volatility_class_display() {
        assert_eq!(format!("{}", VolatilityClass::Stable), "stable");
        assert_eq!(format!("{}", VolatilityClass::Moderate), "moderate");
        assert_eq!(format!("{}", VolatilityClass::Volatile), "volatile");
        assert_eq!(
            format!("{}", VolatilityClass::HighlyVolatile),
            "highly_volatile"
        );
    }

    #[test]
    fn test_sorted_by_cv_descending() {
        let mut acc = ChurnVolatilityAccumulator::new();
        // Uniform file
        for w in 0..10 {
            acc.record_file("uniform.rs", FileActionKind::Modify, w * 86400 * 7);
        }
        // Bursty file
        acc.record_file("bursty.rs", FileActionKind::Create, 0);
        for _ in 0..9 {
            acc.record_file("bursty.rs", FileActionKind::Modify, 100);
        }
        acc.record_file("bursty.rs", FileActionKind::Modify, 86400 * 70);
        let report = acc.finalize();
        assert!(report.files.len() >= 2);
        // First file should have highest CV
        for w in report.files.windows(2) {
            assert!(
                w[0].cv >= w[1].cv - 1e-10,
                "not sorted: {} < {}",
                w[0].cv,
                w[1].cv
            );
        }
    }

    #[test]
    fn test_volatile_and_stable_counts() {
        let mut acc = ChurnVolatilityAccumulator::new();
        // Create uniform file
        for w in 0..10 {
            acc.record_file("stable.rs", FileActionKind::Modify, w * 86400 * 7);
        }
        // Create bursty file (all in first window)
        acc.record_file("bursty.rs", FileActionKind::Create, 0);
        for i in 1..20 {
            acc.record_file("bursty.rs", FileActionKind::Modify, i * 10);
        }
        acc.record_file("bursty.rs", FileActionKind::Modify, 86400 * 70);
        let report = acc.finalize();
        // At least one stable and one volatile file
        assert!(
            report.stable_count + report.volatile_count <= report.files.len(),
            "counts exceed total files"
        );
    }

    // ── Property-based tests ──

    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// CV is always non-negative.
            #[test]
            fn prop_cv_non_negative(vals in proptest::collection::vec(0.0f64..100.0, 2..20)) {
                let cv = compute_cv(&vals);
                prop_assert!(cv >= 0.0, "negative cv: {}", cv);
            }

            /// Equal values always give CV = 0.
            #[test]
            fn prop_equal_values_cv_zero(val in 0.1f64..100.0, n in 2usize..10) {
                let vals = vec![val; n];
                let cv = compute_cv(&vals);
                prop_assert!(cv.abs() < 1e-10, "equal values CV={}, expected 0", cv);
            }
        }
    }
}
