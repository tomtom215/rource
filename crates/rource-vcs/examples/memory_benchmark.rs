//! Memory usage benchmark for commit parsing.
//!
//! Run with:
//!   cargo run --release --example memory_benchmark -- /path/to/repo
//!
//! Or with a pre-generated log file:
//!   git log --pretty=format:"%at|%an|%H" --numstat > git.log
//!   cargo run --release --example memory_benchmark -- --log git.log

use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::process::{Command, Stdio};
use std::time::Instant;

use rource_vcs::compact::{estimate_standard_memory, CommitStore};
use rource_vcs::parser::{GitParser, Parser};
use rource_vcs::stream::StreamingCommitLoader;
use rource_vcs::Commit;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} [--log <logfile>] <repo-path>", args[0]);
        eprintln!();
        eprintln!("Options:");
        eprintln!("  --log <file>  Use a pre-generated git log file");
        eprintln!("  <repo-path>   Path to a git repository");
        std::process::exit(1);
    }

    let (log_source, repo_name) = if args.len() >= 3 && args[1] == "--log" {
        (LogSource::File(args[2].clone()), args[2].clone())
    } else {
        (LogSource::Repo(args[1].clone()), args[1].clone())
    };

    println!("=== Memory Benchmark for: {} ===\n", repo_name);

    // First, count commits to estimate size
    let commit_count = count_commits(&log_source);
    println!("Repository has approximately {} commits\n", commit_count);

    // Benchmark standard parsing
    println!("--- Standard Parsing ---");
    let (std_commits, std_duration) = benchmark_standard_parsing(&log_source);
    let std_estimate = estimate_standard_memory(&std_commits);
    println!("Time: {:.2}s", std_duration.as_secs_f64());
    println!("{}", std_estimate.display());
    println!();

    // Benchmark compact streaming parsing
    println!("--- Compact Streaming Parsing ---");
    let (compact_store, compact_duration) = benchmark_compact_streaming(&log_source);
    let compact_stats = compact_store.stats();
    println!("Time: {:.2}s", compact_duration.as_secs_f64());
    println!("{}", compact_stats.display());
    println!();

    // Calculate estimated standard memory
    // Each Commit struct: ~72 bytes + string data
    // Each FileChange struct: ~32 bytes + string data
    let commit_struct_size = 72;
    let file_struct_size = 32;
    let avg_hash_len = 40;
    let avg_author_len = 15;
    let avg_path_len = 45;

    let estimated_std_total = compact_stats.commit_count * (commit_struct_size + avg_hash_len + avg_author_len)
        + compact_stats.file_change_count * (file_struct_size + avg_path_len);

    // Print comparison
    println!("=== Memory Comparison ===");
    let compact_total = compact_stats.total_bytes();

    println!(
        "Estimated Standard: {:.2} MB",
        estimated_std_total as f64 / 1024.0 / 1024.0
    );
    println!(
        "Compact Storage:    {:.2} MB",
        compact_total as f64 / 1024.0 / 1024.0
    );

    let savings = estimated_std_total.saturating_sub(compact_total);
    let savings_pct = (savings as f64 / estimated_std_total as f64) * 100.0;
    println!(
        "Memory Savings:     {:.2} MB ({:.1}%)",
        savings as f64 / 1024.0 / 1024.0,
        savings_pct
    );
    println!();

    // Deduplication stats
    println!("=== Deduplication Stats ===");
    println!("Unique authors: {} (vs {} commits)", compact_stats.unique_authors, compact_stats.commit_count);
    println!(
        "Unique paths: {} ({} segments) vs {} file changes",
        compact_stats.unique_paths,
        compact_stats.unique_path_segments,
        compact_stats.file_change_count
    );

    if compact_stats.file_change_count > 0 {
        let path_reuse = compact_stats.file_change_count as f64 / compact_stats.unique_paths as f64;
        println!("Path reuse factor: {:.1}x", path_reuse);
    }
}

enum LogSource {
    File(String),
    Repo(String),
}

fn count_commits(source: &LogSource) -> usize {
    match source {
        LogSource::File(path) => {
            let file = File::open(path).expect("Failed to open log file");
            let reader = BufReader::new(file);
            reader.lines().filter(|l| l.as_ref().map(|s| s.contains('|')).unwrap_or(false)).count()
        }
        LogSource::Repo(path) => {
            let output = Command::new("git")
                .args(["rev-list", "--count", "HEAD"])
                .current_dir(path)
                .output()
                .expect("Failed to run git rev-list");
            String::from_utf8_lossy(&output.stdout)
                .trim()
                .parse()
                .unwrap_or(0)
        }
    }
}

fn get_git_log(source: &LogSource) -> Box<dyn BufRead> {
    match source {
        LogSource::File(path) => {
            let file = File::open(path).expect("Failed to open log file");
            Box::new(BufReader::new(file))
        }
        LogSource::Repo(path) => {
            let child = Command::new("git")
                .args([
                    "log",
                    "--pretty=format:%at|%an|%H",
                    "--numstat",
                    "--date=unix",
                ])
                .current_dir(path)
                .stdout(Stdio::piped())
                .spawn()
                .expect("Failed to run git log");

            Box::new(BufReader::new(child.stdout.expect("No stdout")))
        }
    }
}

fn benchmark_standard_parsing(source: &LogSource) -> (Vec<Commit>, std::time::Duration) {
    let start = Instant::now();

    // Read entire log into memory
    let mut log_content = String::new();
    let mut reader = get_git_log(source);
    std::io::Read::read_to_string(&mut reader, &mut log_content)
        .expect("Failed to read log");

    // Parse with standard parser
    let parser = GitParser::new();
    let commits = parser.parse_str(&log_content).unwrap_or_default();

    (commits, start.elapsed())
}

fn benchmark_compact_streaming(source: &LogSource) -> (CommitStore, std::time::Duration) {
    let start = Instant::now();

    let reader = get_git_log(source);
    let buf_reader = BufReader::new(StreamingReader(reader));

    let loader = StreamingCommitLoader::new(buf_reader);
    let store = loader.load_with_progress(|commits, files| {
        if commits % 10000 == 0 {
            eprint!("\r  Loading... {} commits, {} files", commits, files);
        }
    });
    eprintln!();

    (store, start.elapsed())
}

// Wrapper to convert Box<dyn BufRead> to Read
struct StreamingReader(Box<dyn BufRead>);

impl std::io::Read for StreamingReader {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.0.read(buf)
    }
}
