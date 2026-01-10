//! # rource-vcs
//!
//! Version control system log parsing for Rource.
//!
//! This crate provides parsers for various VCS log formats:
//! - Git (standard and raw formats)
//! - SVN (XML format)
//! - Mercurial
//! - Bazaar
//! - Custom pipe-delimited format
//!
//! ## Usage
//!
//! ```ignore
//! use rource_vcs::{Commit, CommitParser, GitParser};
//!
//! let parser = GitParser::new();
//! for commit in parser.parse_file("repo.git")? {
//!     println!("{}: {}", commit.hash, commit.author);
//! }
//! ```

// Lints are configured in workspace Cargo.toml

pub mod commit;

pub use commit::{Commit, FileAction, FileChange};
