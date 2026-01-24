// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Deterministic instruction-count benchmarks for VCS parsing.
//!
//! These benchmarks use iai-callgrind to measure CPU instructions,
//! which is deterministic and ideal for CI regression detection.

#![allow(missing_docs)]

use iai_callgrind::{library_benchmark, library_benchmark_group, main};
use rource_vcs::parser::{CustomParser, GitParser, Parser};
use rource_vcs::stream::StreamingCommitLoader;
use rource_vcs::{detect_format, parse_auto, StringInterner};
use std::fmt::Write;
use std::hint::black_box;
use std::io::{BufReader, Cursor};

// ============================================================================
// Test Data Generation (not measured)
// ============================================================================

fn generate_custom_log(num_commits: usize, files_per_commit: usize) -> String {
    let mut log = String::with_capacity(num_commits * files_per_commit * 60);
    let authors = ["Alice", "Bob", "Charlie", "Diana", "Eve"];
    let actions = ["A", "M", "D"];
    let extensions = ["rs", "ts", "py", "go", "java"];

    let mut timestamp = 1_609_459_200_i64;

    for commit_idx in 0..num_commits {
        let author = authors[commit_idx % authors.len()];

        for file_idx in 0..files_per_commit {
            let action = actions[(commit_idx + file_idx) % 3];
            let ext = extensions[(commit_idx + file_idx) % extensions.len()];
            let dir_depth = (file_idx % 3) + 1;

            let mut path = String::new();
            for d in 0..dir_depth {
                let _ = write!(path, "dir{}/", (commit_idx + d) % 30);
            }
            let _ = write!(path, "file_{file_idx}.{ext}");

            let _ = writeln!(log, "{timestamp}|{author}|{action}|{path}");
        }

        timestamp += 3600;
    }

    log
}

fn generate_git_log(num_commits: usize, files_per_commit: usize) -> String {
    let mut log = String::with_capacity(num_commits * files_per_commit * 80);
    let authors = [
        ("Alice Smith", "alice@example.com"),
        ("Bob Jones", "bob@example.com"),
    ];
    let extensions = ["rs", "ts", "py"];

    let mut timestamp = 1_609_459_200_i64;

    for commit_idx in 0..num_commits {
        let (author_name, author_email) = authors[commit_idx % authors.len()];

        let _ = writeln!(
            log,
            "commit {commit_idx:07x}{timestamp:07x}{commit_idx:06x}"
        );
        let _ = writeln!(log, "Author: {author_name} <{author_email}>");
        let _ = writeln!(log, "Date:   {timestamp}");
        log.push_str("\n    Commit message\n\n");

        for file_idx in 0..files_per_commit {
            let ext = extensions[(commit_idx + file_idx) % extensions.len()];
            let action = if (commit_idx + file_idx) % 2 == 0 {
                "A"
            } else {
                "M"
            };
            let _ = writeln!(
                log,
                "{action}\tsrc/module{}/file_{file_idx}.{ext}",
                commit_idx % 10
            );
        }

        log.push('\n');
        timestamp += 3600;
    }

    log
}

// ============================================================================
// Custom Parser Benchmarks
// ============================================================================

// Parse 100 commits × 5 files = 500 entries (small repo)
#[library_benchmark]
fn bench_custom_parse_500() -> usize {
    let log = generate_custom_log(100, 5);
    let parser = CustomParser::new();
    let commits = parser.parse_str(black_box(&log)).unwrap();
    commits.len()
}

// Parse 1000 commits × 10 files = 10,000 entries (medium repo)
#[library_benchmark]
fn bench_custom_parse_10000() -> usize {
    let log = generate_custom_log(1000, 10);
    let parser = CustomParser::new();
    let commits = parser.parse_str(black_box(&log)).unwrap();
    commits.len()
}

// Parse 5000 commits × 10 files = 50,000 entries (large repo)
#[library_benchmark]
fn bench_custom_parse_50000() -> usize {
    let log = generate_custom_log(5000, 10);
    let parser = CustomParser::new();
    let commits = parser.parse_str(black_box(&log)).unwrap();
    commits.len()
}

library_benchmark_group!(
    name = custom_parser_group;
    benchmarks = bench_custom_parse_500, bench_custom_parse_10000, bench_custom_parse_50000
);

// ============================================================================
// Git Parser Benchmarks
// ============================================================================

// Parse 100 git commits × 5 files = 500 entries
#[library_benchmark]
fn bench_git_parse_500() -> usize {
    let log = generate_git_log(100, 5);
    let parser = GitParser::new();
    let commits = parser.parse_str(black_box(&log)).unwrap();
    commits.len()
}

// Parse 1000 git commits × 10 files = 10,000 entries
#[library_benchmark]
fn bench_git_parse_10000() -> usize {
    let log = generate_git_log(1000, 10);
    let parser = GitParser::new();
    let commits = parser.parse_str(black_box(&log)).unwrap();
    commits.len()
}

library_benchmark_group!(
    name = git_parser_group;
    benchmarks = bench_git_parse_500, bench_git_parse_10000
);

// ============================================================================
// Format Detection Benchmarks
// ============================================================================

// Detect custom format
#[library_benchmark]
fn bench_detect_custom() -> bool {
    let log = generate_custom_log(10, 5);
    let format = detect_format(black_box(&log));
    matches!(format, Some(rource_vcs::LogFormat::Custom))
}

// Detect git format
#[library_benchmark]
fn bench_detect_git() -> bool {
    let log = generate_git_log(10, 5);
    let format = detect_format(black_box(&log));
    matches!(format, Some(rource_vcs::LogFormat::Git))
}

library_benchmark_group!(
    name = format_detection_group;
    benchmarks = bench_detect_custom, bench_detect_git
);

// ============================================================================
// String Interning Benchmarks
// ============================================================================

// Intern 1000 strings with high duplication (author names)
#[library_benchmark]
fn bench_intern_high_duplication() -> usize {
    let authors = ["Alice", "Bob", "Charlie", "Diana", "Eve"];
    let mut interner = StringInterner::new();

    for i in 0..1000 {
        interner.intern(black_box(authors[i % authors.len()]));
    }

    interner.len()
}

// Intern 1000 unique strings (file paths)
#[library_benchmark]
fn bench_intern_low_duplication() -> usize {
    let mut interner = StringInterner::new();

    for i in 0..1000 {
        let path = format!("src/dir{}/file_{}.rs", i / 100, i);
        interner.intern(black_box(&path));
    }

    interner.len()
}

library_benchmark_group!(
    name = interning_group;
    benchmarks = bench_intern_high_duplication, bench_intern_low_duplication
);

// ============================================================================
// Streaming Loader Benchmarks
// ============================================================================

// Stream parse 1000 commits
#[library_benchmark]
fn bench_streaming_1000() -> usize {
    let log = generate_custom_log(1000, 5);
    let cursor = Cursor::new(log.into_bytes());
    let reader = BufReader::new(cursor);
    let loader = StreamingCommitLoader::new(reader);
    let store = loader.load_all();
    store.commit_count()
}

// Stream parse 5000 commits
#[library_benchmark]
fn bench_streaming_5000() -> usize {
    let log = generate_custom_log(5000, 5);
    let cursor = Cursor::new(log.into_bytes());
    let reader = BufReader::new(cursor);
    let loader = StreamingCommitLoader::new(reader);
    let store = loader.load_all();
    store.commit_count()
}

library_benchmark_group!(
    name = streaming_group;
    benchmarks = bench_streaming_1000, bench_streaming_5000
);

// ============================================================================
// Auto-Parse Benchmarks (detection + parsing)
// ============================================================================

// Auto-detect and parse 1000 custom commits
#[library_benchmark]
fn bench_parse_auto_custom_1000() -> usize {
    let log = generate_custom_log(1000, 5);
    let (_, commits) = parse_auto(black_box(&log)).unwrap();
    commits.len()
}

// Auto-detect and parse 1000 git commits
#[library_benchmark]
fn bench_parse_auto_git_1000() -> usize {
    let log = generate_git_log(1000, 5);
    let (_, commits) = parse_auto(black_box(&log)).unwrap();
    commits.len()
}

library_benchmark_group!(
    name = parse_auto_group;
    benchmarks = bench_parse_auto_custom_1000, bench_parse_auto_git_1000
);

// ============================================================================
// Main
// ============================================================================

main!(
    library_benchmark_groups = custom_parser_group,
    git_parser_group,
    format_detection_group,
    interning_group,
    streaming_group,
    parse_auto_group
);
