// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Performance benchmarks for VCS log parsing.
//!
//! These benchmarks measure the performance of commit log parsing,
//! which is critical for handling large repositories like Home Assistant Core
//! (103,533 commits, 533,366 file changes).

#![allow(missing_docs)]

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rource_vcs::parser::{CustomParser, GitParser, Parser};
use rource_vcs::stream::StreamingCommitLoader;
use rource_vcs::{detect_format, parse_auto, StringInterner};
use std::fmt::Write;
use std::hint::black_box;
use std::io::{BufReader, Cursor};

// ============================================================================
// Test Data Generation
// ============================================================================

/// Generate custom format log entries.
fn generate_custom_log(num_commits: usize, files_per_commit: usize) -> String {
    let mut log = String::with_capacity(num_commits * files_per_commit * 60);
    let authors = ["Alice", "Bob", "Charlie", "Diana", "Eve"];
    let actions = ["A", "M", "D"];
    let extensions = ["rs", "ts", "py", "go", "java", "cpp", "js"];

    let mut timestamp = 1_609_459_200_i64; // 2021-01-01

    for commit_idx in 0..num_commits {
        let author = authors[commit_idx % authors.len()];

        for file_idx in 0..files_per_commit {
            let action = actions[(commit_idx + file_idx) % 3];
            let ext = extensions[(commit_idx + file_idx) % extensions.len()];
            let dir_depth = (file_idx % 4) + 1;

            // Build path with varying depth
            let mut path = String::new();
            for d in 0..dir_depth {
                let _ = write!(path, "dir{}/", (commit_idx + d) % 50);
            }
            let _ = write!(path, "file_{file_idx}.{ext}");

            let _ = writeln!(log, "{timestamp}|{author}|{action}|{path}");
        }

        timestamp += 3600; // 1 hour between commits
    }

    log
}

/// Generate git log format entries.
fn generate_git_log(num_commits: usize, files_per_commit: usize) -> String {
    let mut log = String::with_capacity(num_commits * files_per_commit * 80);
    let authors = [
        ("Alice Smith", "alice@example.com"),
        ("Bob Jones", "bob@example.com"),
        ("Charlie Brown", "charlie@example.com"),
    ];
    let extensions = ["rs", "ts", "py", "go"];

    let mut timestamp = 1_609_459_200_i64;

    for commit_idx in 0..num_commits {
        let (author_name, author_email) = authors[commit_idx % authors.len()];

        let _ = writeln!(
            log,
            "commit {commit_idx:07x}{timestamp:07x}{commit_idx:06x}"
        );
        let _ = writeln!(log, "Author: {author_name} <{author_email}>");
        let _ = writeln!(log, "Date:   {timestamp}");
        log.push_str("\n    Commit message for commit\n\n");

        for file_idx in 0..files_per_commit {
            let ext = extensions[(commit_idx + file_idx) % extensions.len()];
            let action = if (commit_idx + file_idx) % 3 == 0 {
                "A"
            } else if (commit_idx + file_idx) % 3 == 1 {
                "M"
            } else {
                "D"
            };

            let _ = writeln!(
                log,
                "{action}\tsrc/module{}/file_{file_idx}.{ext}",
                commit_idx % 20
            );
        }

        log.push('\n');
        timestamp += 3600;
    }

    log
}

// ============================================================================
// Custom Format Parsing Benchmarks
// ============================================================================

fn bench_custom_parser(c: &mut Criterion) {
    let mut group = c.benchmark_group("custom_parser");

    for (commits, files) in [(100, 5), (1000, 10), (10000, 5)] {
        let total_entries = commits * files;
        let log = generate_custom_log(commits, files);

        group.throughput(Throughput::Elements(total_entries as u64));

        group.bench_with_input(
            BenchmarkId::new("entries", total_entries),
            &log,
            |b, log| {
                let parser = CustomParser::new();
                b.iter(|| {
                    let commits = parser.parse_str(black_box(log)).unwrap();
                    black_box(commits.len())
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Git Format Parsing Benchmarks
// ============================================================================

fn bench_git_parser(c: &mut Criterion) {
    let mut group = c.benchmark_group("git_parser");

    for (commits, files) in [(100, 5), (1000, 10), (5000, 5)] {
        let total_entries = commits * files;
        let log = generate_git_log(commits, files);

        group.throughput(Throughput::Elements(total_entries as u64));

        group.bench_with_input(
            BenchmarkId::new("entries", total_entries),
            &log,
            |b, log| {
                let parser = GitParser::new();
                b.iter(|| {
                    let commits = parser.parse_str(black_box(log)).unwrap();
                    black_box(commits.len())
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Format Detection Benchmarks
// ============================================================================

fn bench_format_detection(c: &mut Criterion) {
    let mut group = c.benchmark_group("format_detection");

    // Custom format sample
    let custom_log = generate_custom_log(10, 5);
    group.bench_function("custom_format", |b| {
        b.iter(|| {
            let format = detect_format(black_box(&custom_log));
            black_box(format)
        });
    });

    // Git format sample
    let git_log = generate_git_log(10, 5);
    group.bench_function("git_format", |b| {
        b.iter(|| {
            let format = detect_format(black_box(&git_log));
            black_box(format)
        });
    });

    group.finish();
}

// ============================================================================
// Auto-Detection + Parsing Benchmarks
// ============================================================================

fn bench_parse_auto(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse_auto");

    for (commits, files) in [(100, 5), (1000, 10)] {
        let total_entries = commits * files;
        let log = generate_custom_log(commits, files);

        group.throughput(Throughput::Elements(total_entries as u64));

        group.bench_with_input(
            BenchmarkId::new("custom_entries", total_entries),
            &log,
            |b, log| {
                b.iter(|| {
                    let (format, commits) = parse_auto(black_box(log)).unwrap();
                    black_box((format, commits.len()))
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// String Interning Benchmarks
// ============================================================================

fn bench_string_interning(c: &mut Criterion) {
    let mut group = c.benchmark_group("string_interning");

    // Generate strings with varying duplication rates
    let mut strings: Vec<String> = Vec::with_capacity(10000);
    let unique_authors = ["Alice", "Bob", "Charlie", "Diana", "Eve"];

    for i in 0..10000 {
        // High duplication (author names)
        strings.push(unique_authors[i % unique_authors.len()].to_string());
    }

    group.throughput(Throughput::Elements(strings.len() as u64));

    group.bench_function("intern_high_duplication", |b| {
        b.iter(|| {
            let mut interner = StringInterner::new();
            for s in &strings {
                interner.intern(black_box(s));
            }
            black_box(interner.len())
        });
    });

    // Low duplication (file paths)
    let mut unique_paths: Vec<String> = Vec::with_capacity(10000);
    for i in 0..10000 {
        unique_paths.push(format!("src/dir{}/file_{}.rs", i / 100, i));
    }

    group.bench_function("intern_low_duplication", |b| {
        b.iter(|| {
            let mut interner = StringInterner::new();
            for s in &unique_paths {
                interner.intern(black_box(s));
            }
            black_box(interner.len())
        });
    });

    group.finish();
}

// ============================================================================
// Streaming Parser Benchmarks
// ============================================================================

fn bench_streaming_loader(c: &mut Criterion) {
    let mut group = c.benchmark_group("streaming_loader");

    for (commits, files) in [(1000, 10), (10000, 5)] {
        let total_entries = commits * files;
        let log = generate_custom_log(commits, files);
        let log_bytes = log.into_bytes();

        group.throughput(Throughput::Elements(total_entries as u64));

        group.bench_with_input(
            BenchmarkId::new("entries", total_entries),
            &log_bytes,
            |b, log_bytes| {
                b.iter(|| {
                    let cursor = Cursor::new(log_bytes.as_slice());
                    let reader = BufReader::new(cursor);
                    let loader = StreamingCommitLoader::new(reader);
                    let store = loader.load_all();
                    black_box(store.commit_count())
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Compact Storage Benchmarks
// ============================================================================

fn bench_compact_storage(c: &mut Criterion) {
    let mut group = c.benchmark_group("compact_storage");

    for (commits, files) in [(1000, 10), (10000, 5)] {
        let total_entries = commits * files;
        let log = generate_custom_log(commits, files);
        let log_bytes = log.into_bytes();

        group.throughput(Throughput::Elements(total_entries as u64));

        // Measure memory after loading
        group.bench_with_input(
            BenchmarkId::new("load_and_query", total_entries),
            &log_bytes,
            |b, log_bytes| {
                b.iter(|| {
                    let cursor = Cursor::new(log_bytes.as_slice());
                    let reader = BufReader::new(cursor);
                    let loader = StreamingCommitLoader::new(reader);
                    let store = loader.load_all();

                    // Query all commits and files
                    let mut total_files = 0usize;
                    for (_id, commit) in store.commits() {
                        let files = store.file_changes(commit);
                        total_files += files.len();
                    }
                    black_box(total_files)
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Main
// ============================================================================

criterion_group!(
    benches,
    bench_custom_parser,
    bench_git_parser,
    bench_format_detection,
    bench_parse_auto,
    bench_string_interning,
    bench_streaming_loader,
    bench_compact_storage,
);

criterion_main!(benches);
