// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! # rource-vcs
//!
//! Version control system log parsing for Rource.
//!
//! This crate provides parsers for various VCS log formats:
//! - Git (standard and raw formats)
//! - Custom pipe-delimited format (Gource-compatible)
//!
//! ## Quick Start
//!
//! ```
//! use rource_vcs::{detect::parse_auto, Commit};
//!
//! // Parse with auto-detection
//! let log = "1234567890|John Doe|A|src/main.rs\n";
//! let (format, commits) = parse_auto(log).unwrap();
//! println!("Detected format: {}", format);
//! println!("Parsed {} commits", commits.len());
//! ```
//!
//! ## Using Specific Parsers
//!
//! ```
//! use rource_vcs::parser::{CustomParser, GitParser, Parser};
//!
//! // Custom format
//! let parser = CustomParser::new();
//! let commits = parser.parse_str("1234567890|John|A|file.txt\n").unwrap();
//!
//! // Git format
//! let parser = GitParser::new();
//! let log = "commit abc1234567\nAuthor: John <j@test.com>\nDate: 1234567890\nA\tfile.txt\n";
//! let commits = parser.parse_str(log).unwrap();
//! ```
//!
//! ## Custom Format Specification
//!
//! The custom format is pipe-delimited with the following fields:
//!
//! ```text
//! timestamp|username|action|filepath[|color]
//! ```
//!
//! - `timestamp`: Unix timestamp (seconds since epoch)
//! - `username`: Author/contributor name
//! - `action`: A (add), M (modify), D (delete)
//! - `filepath`: Path relative to repository root
//! - `color`: Optional hex color (e.g., "FF0000")
//!
//! ## Error Handling
//!
//! All parsing functions return [`ParseResult`], which
//! wraps either the parsed data or a [`ParseError`] with
//! detailed information about what went wrong.

// Lints are configured in workspace Cargo.toml

pub mod commit;
pub mod compact;
pub mod detect;
pub mod error;
pub mod intern;
pub mod parser;
pub mod stream;

// Re-exports for convenience
pub use commit::{Commit, FileAction, FileChange};
pub use compact::{CommitId, CommitStore, CommitStoreStats, CompactCommit, CompactFileChange};
pub use detect::{detect_format, parse_auto, LogFormat};
pub use error::{ParseError, ParseResult};
pub use intern::{InternedPath, InternedString, PathInterner, StringInterner};
pub use parser::{CustomParser, GitParser, ParseOptions, Parser};
pub use stream::{CustomLogGrouper, CustomLogStream, GitLogStream, StreamingCommitLoader};
