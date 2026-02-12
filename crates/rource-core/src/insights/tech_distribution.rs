// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Language & Technology Distribution — classifies files by programming
//! language and technology stack based on file extensions.
//!
//! This provides a high-level overview of the repository's technology
//! composition, similar to GitHub's language breakdown but computed from
//! the commit history (capturing the *active* technology distribution,
//! not just the current snapshot).
//!
//! # Research Basis
//!
//! - Mockus et al. (2002) "Two Case Studies of Open Source Software
//!   Development: Apache and Mozilla" (TOSEM) — file type classification
//!   for developer role analysis
//! - Kalliamvakou et al. (2016) "An In-Depth Study of the Promises and
//!   Perils of Mining GitHub" (EMSE) — language distribution as repository
//!   characteristic
//!
//! # Algorithm
//!
//! 1. Extract file extension from each unique file path
//! 2. Map extension to language/technology category
//! 3. Count unique files per category (from latest state: created - deleted)
//! 4. Compute percentage distribution
//!
//! # Complexity
//!
//! - O(F) where F = unique files touched in history

use rustc_hash::{FxHashMap, FxHashSet};

use super::FileActionKind;

/// Technology distribution report for the repository.
#[derive(Debug, Clone)]
pub struct TechDistributionReport {
    /// Per-language/technology breakdown, sorted by file count descending.
    pub languages: Vec<LanguageEntry>,
    /// Total unique files analyzed.
    pub total_files: usize,
    /// Number of distinct language categories detected.
    pub language_count: usize,
    /// Primary language (highest file count).
    pub primary_language: String,
    /// Primary language percentage.
    pub primary_language_pct: f64,
}

/// A single language/technology entry.
#[derive(Debug, Clone)]
pub struct LanguageEntry {
    /// Language or technology name.
    pub name: String,
    /// Number of active files (created but not deleted).
    pub file_count: usize,
    /// Percentage of total files.
    pub percentage: f64,
    /// Representative file extensions.
    pub extensions: Vec<String>,
}

/// Accumulates file paths to compute technology distribution.
pub struct TechDistributionAccumulator {
    /// Tracks which files currently exist (created but not deleted).
    active_files: FxHashSet<String>,
    /// All file paths ever seen.
    all_files: FxHashSet<String>,
}

impl Default for TechDistributionAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl TechDistributionAccumulator {
    /// Creates a new empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            active_files: FxHashSet::default(),
            all_files: FxHashSet::default(),
        }
    }

    /// Records a file action for tech distribution analysis.
    pub fn record_file(&mut self, path: &str, action: FileActionKind) {
        self.all_files.insert(path.to_string());
        match action {
            FileActionKind::Create | FileActionKind::Modify => {
                self.active_files.insert(path.to_string());
            }
            FileActionKind::Delete => {
                self.active_files.remove(path);
            }
        }
    }

    /// Finalizes the technology distribution report.
    #[must_use]
    pub fn finalize(self) -> TechDistributionReport {
        if self.active_files.is_empty() {
            return TechDistributionReport {
                languages: Vec::new(),
                total_files: 0,
                language_count: 0,
                primary_language: String::new(),
                primary_language_pct: 0.0,
            };
        }

        // Classify each file by extension
        let mut lang_files: FxHashMap<&str, Vec<String>> = FxHashMap::default();
        let mut lang_exts: FxHashMap<&str, FxHashSet<String>> = FxHashMap::default();

        for path in &self.active_files {
            let ext = path
                .rsplit_once('.')
                .map(|(_, e)| e.to_lowercase())
                .unwrap_or_default();
            let lang = classify_extension(&ext);
            lang_files.entry(lang).or_default().push(path.clone());
            if !ext.is_empty() {
                lang_exts.entry(lang).or_default().insert(format!(".{ext}"));
            }
        }

        let total_files = self.active_files.len();
        let mut languages: Vec<LanguageEntry> = lang_files
            .iter()
            .map(|(&name, files)| {
                let mut exts: Vec<String> = lang_exts
                    .get(name)
                    .map(|s| s.iter().cloned().collect())
                    .unwrap_or_default();
                exts.sort();
                exts.truncate(5);
                LanguageEntry {
                    name: name.to_string(),
                    file_count: files.len(),
                    percentage: files.len() as f64 / total_files as f64 * 100.0,
                    extensions: exts,
                }
            })
            .collect();

        languages.sort_by(|a, b| b.file_count.cmp(&a.file_count));

        let primary = languages.first();
        let primary_language = primary.map_or(String::new(), |l| l.name.clone());
        let primary_language_pct = primary.map_or(0.0, |l| l.percentage);

        TechDistributionReport {
            language_count: languages.len(),
            total_files,
            primary_language,
            primary_language_pct,
            languages,
        }
    }
}

/// Maps a file extension (lowercase, no dot) to a language/technology category.
///
/// Exposed publicly so other modules (e.g., `tech_expertise`) can reuse the
/// same mapping without duplicating the table.
#[must_use]
pub fn classify_ext(ext: &str) -> &'static str {
    classify_extension(ext)
}

/// Maps a file extension to a language/technology category.
fn classify_extension(ext: &str) -> &'static str {
    match ext {
        // Systems programming
        "rs" => "Rust",
        "c" | "h" => "C",
        "cpp" | "cxx" | "cc" | "hpp" | "hxx" | "hh" => "C++",
        "go" => "Go",
        "zig" => "Zig",
        "asm" | "s" => "Assembly",

        // JVM
        "java" => "Java",
        "kt" | "kts" => "Kotlin",
        "scala" => "Scala",
        "groovy" => "Groovy",
        "clj" | "cljs" | "cljc" => "Clojure",

        // .NET
        "cs" => "C#",
        "fs" | "fsx" => "F#",
        "vb" => "Visual Basic",

        // Web frontend
        "js" | "mjs" | "cjs" => "JavaScript",
        "ts" | "mts" | "cts" => "TypeScript",
        "jsx" => "JavaScript (React)",
        "tsx" => "TypeScript (React)",
        "vue" => "Vue",
        "svelte" => "Svelte",

        // Web markup & style
        "html" | "htm" => "HTML",
        "css" => "CSS",
        "scss" | "sass" => "Sass/SCSS",
        "less" => "Less",

        // Scripting
        "py" | "pyi" | "pyw" => "Python",
        "rb" | "rake" => "Ruby",
        "php" => "PHP",
        "pl" | "pm" => "Perl",
        "lua" => "Lua",
        "r" | "rmd" => "R",
        "jl" => "Julia",

        // Shell
        "sh" | "bash" | "zsh" => "Shell",
        "ps1" | "psm1" | "psd1" => "PowerShell",
        "bat" | "cmd" => "Batch",

        // Functional
        "hs" | "lhs" => "Haskell",
        "ml" | "mli" => "OCaml",
        "ex" | "exs" => "Elixir",
        "erl" | "hrl" => "Erlang",
        "elm" => "Elm",

        // Mobile
        "swift" => "Swift",
        "m" | "mm" => "Objective-C",
        "dart" => "Dart",

        // Data & config
        "json" => "JSON",
        "yaml" | "yml" => "YAML",
        "toml" => "TOML",
        "xml" | "xsl" | "xsd" => "XML",
        "ini" | "cfg" | "conf" | "env" => "Config",

        // Documentation
        "md" | "mdx" => "Markdown",
        "rst" => "reStructuredText",
        "txt" => "Text",
        "adoc" => "AsciiDoc",
        "tex" | "latex" => "LaTeX",

        // Database
        "sql" => "SQL",
        "prisma" => "Prisma",

        // DevOps & CI
        "dockerfile" => "Docker",
        "tf" | "tfvars" => "Terraform",
        "nix" => "Nix",

        // Proof / Verification
        "v" => "Coq",
        "lean" => "Lean",

        // Build
        "cmake" => "CMake",
        "makefile" | "mk" => "Make",
        "gradle" => "Gradle",

        // Binary / media (typically not in repos)
        "png" | "jpg" | "jpeg" | "gif" | "svg" | "ico" | "webp" => "Images",
        "woff" | "woff2" | "ttf" | "otf" | "eot" => "Fonts",

        // Fallback
        _ => "Other",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let acc = TechDistributionAccumulator::new();
        let report = acc.finalize();
        assert!(report.languages.is_empty());
        assert_eq!(report.total_files, 0);
    }

    #[test]
    fn test_default_impl() {
        let acc = TechDistributionAccumulator::default();
        let report = acc.finalize();
        assert!(report.languages.is_empty());
    }

    #[test]
    fn test_single_language() {
        let mut acc = TechDistributionAccumulator::new();
        acc.record_file("src/main.rs", FileActionKind::Create);
        acc.record_file("src/lib.rs", FileActionKind::Create);
        let report = acc.finalize();
        assert_eq!(report.primary_language, "Rust");
        assert_eq!(report.total_files, 2);
        assert!((report.primary_language_pct - 100.0).abs() < 0.01);
    }

    #[test]
    fn test_multiple_languages() {
        let mut acc = TechDistributionAccumulator::new();
        acc.record_file("src/main.rs", FileActionKind::Create);
        acc.record_file("src/lib.rs", FileActionKind::Create);
        acc.record_file("web/app.js", FileActionKind::Create);
        acc.record_file("web/style.css", FileActionKind::Create);
        let report = acc.finalize();
        assert_eq!(report.language_count, 3); // Rust, JavaScript, CSS
        assert_eq!(report.primary_language, "Rust"); // 2 files
    }

    #[test]
    fn test_deleted_files_excluded() {
        let mut acc = TechDistributionAccumulator::new();
        acc.record_file("old.py", FileActionKind::Create);
        acc.record_file("main.rs", FileActionKind::Create);
        acc.record_file("old.py", FileActionKind::Delete);
        let report = acc.finalize();
        assert_eq!(report.total_files, 1);
        assert_eq!(report.primary_language, "Rust");
    }

    #[test]
    fn test_extension_classification() {
        assert_eq!(classify_extension("rs"), "Rust");
        assert_eq!(classify_extension("js"), "JavaScript");
        assert_eq!(classify_extension("py"), "Python");
        assert_eq!(classify_extension("ts"), "TypeScript");
        assert_eq!(classify_extension("html"), "HTML");
        assert_eq!(classify_extension("css"), "CSS");
        assert_eq!(classify_extension("go"), "Go");
        assert_eq!(classify_extension(""), "Other");
        assert_eq!(classify_extension("xyz"), "Other");
    }

    #[test]
    fn test_percentages_sum_to_100() {
        let mut acc = TechDistributionAccumulator::new();
        acc.record_file("a.rs", FileActionKind::Create);
        acc.record_file("b.js", FileActionKind::Create);
        acc.record_file("c.py", FileActionKind::Create);
        acc.record_file("d.go", FileActionKind::Create);
        let report = acc.finalize();
        let total: f64 = report.languages.iter().map(|l| l.percentage).sum();
        assert!((total - 100.0).abs() < 0.01, "percentages sum to {total}");
    }

    #[test]
    fn test_sorted_by_file_count() {
        let mut acc = TechDistributionAccumulator::new();
        for i in 0..5 {
            acc.record_file(&format!("f{i}.rs"), FileActionKind::Create);
        }
        for i in 0..3 {
            acc.record_file(&format!("f{i}.js"), FileActionKind::Create);
        }
        acc.record_file("f0.py", FileActionKind::Create);
        let report = acc.finalize();
        for w in report.languages.windows(2) {
            assert!(
                w[0].file_count >= w[1].file_count,
                "not sorted: {} < {}",
                w[0].file_count,
                w[1].file_count
            );
        }
    }
}
