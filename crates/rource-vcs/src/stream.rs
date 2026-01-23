// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Streaming commit parsing for large repositories.
//!
//! This module provides streaming parsers that process commits one at a time
//! without loading the entire log file into memory.
//!
//! # Example
//!
//! ```no_run
//! use std::fs::File;
//! use std::io::BufReader;
//! use rource_vcs::stream::GitLogStream;
//!
//! let file = File::open("git.log").unwrap();
//! let reader = BufReader::new(file);
//! let stream = GitLogStream::new(reader);
//!
//! for commit in stream {
//!     println!("Commit: {} by {}", commit.short_hash(), commit.author);
//! }
//! ```

use std::io::{BufRead, BufReader, Read};

use crate::commit::{Commit, FileAction, FileChange};
use crate::compact::CommitStore;

/// A streaming parser for git log output.
///
/// Parses commits one at a time from a buffered reader, minimizing
/// memory usage for large repositories.
pub struct GitLogStream<R: Read> {
    reader: BufReader<R>,
    line_buffer: String,
    current_commit: Option<CommitBuilder>,
    finished: bool,
}

struct CommitBuilder {
    hash: String,
    timestamp: i64,
    author: String,
    files: Vec<FileChange>,
}

impl<R: Read> GitLogStream<R> {
    /// Creates a new streaming parser from a reader.
    pub fn new(reader: BufReader<R>) -> Self {
        Self {
            reader,
            line_buffer: String::with_capacity(256),
            current_commit: None,
            finished: false,
        }
    }

    /// Creates a streaming parser from any Read source.
    pub fn from_read(source: R) -> Self {
        Self::new(BufReader::new(source))
    }

    fn read_line(&mut self) -> Option<&str> {
        self.line_buffer.clear();
        match self.reader.read_line(&mut self.line_buffer) {
            Ok(0) | Err(_) => None, // EOF or error
            Ok(_) => Some(self.line_buffer.trim_end()),
        }
    }

    fn parse_commit_line(line: &str) -> Option<(String, i64, String)> {
        // Expected format: "timestamp|author|hash"
        let parts: Vec<&str> = line.split('|').collect();
        if parts.len() >= 3 {
            let timestamp = parts[0].parse().ok()?;
            let author = parts[1].to_string();
            let hash = parts[2].to_string();
            Some((hash, timestamp, author))
        } else {
            None
        }
    }

    fn parse_numstat_line(line: &str) -> Option<FileChange> {
        // Format: "added\tremoved\tpath" or "-\t-\tpath" for binary
        let parts: Vec<&str> = line.split('\t').collect();
        if parts.len() >= 3 {
            let path = parts[2];
            // Determine action based on added/removed counts
            let action = match (parts[0], parts[1]) {
                ("0", _) if parts[1] != "0" => FileAction::Delete,
                (_, "0") if parts[0] != "0" => FileAction::Create,
                _ => FileAction::Modify, // Binary files ("-", "-") and others
            };
            Some(FileChange::new(path, action))
        } else {
            None
        }
    }

    fn finalize_current(&mut self) -> Option<Commit> {
        self.current_commit.take().map(|builder| Commit {
            hash: builder.hash,
            timestamp: builder.timestamp,
            author: builder.author,
            email: None,
            files: builder.files,
        })
    }
}

impl<R: Read> Iterator for GitLogStream<R> {
    type Item = Commit;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        loop {
            // Try to read the next line
            let Some(l) = self.read_line() else {
                self.finished = true;
                return self.finalize_current();
            };
            let line = l.to_string();

            // Skip empty lines
            if line.is_empty() {
                continue;
            }

            // Try to parse as commit header
            if let Some((hash, timestamp, author)) = Self::parse_commit_line(&line) {
                // Finalize previous commit if any
                let prev = self.finalize_current();

                // Start new commit
                self.current_commit = Some(CommitBuilder {
                    hash,
                    timestamp,
                    author,
                    files: Vec::new(),
                });

                if prev.is_some() {
                    return prev;
                }
                continue;
            }

            // Try to parse as numstat line
            if let Some(file_change) = Self::parse_numstat_line(&line) {
                if let Some(ref mut builder) = self.current_commit {
                    builder.files.push(file_change);
                }
            }
        }
    }
}

/// A streaming parser that stores commits directly in a `CommitStore`.
///
/// This is the most memory-efficient way to parse large repositories.
pub struct StreamingCommitLoader<R: Read> {
    stream: GitLogStream<R>,
    store: CommitStore,
}

impl<R: Read> StreamingCommitLoader<R> {
    /// Creates a new streaming loader.
    pub fn new(reader: BufReader<R>) -> Self {
        Self {
            stream: GitLogStream::new(reader),
            store: CommitStore::new(),
        }
    }

    /// Creates a streaming loader with pre-allocated capacity.
    pub fn with_capacity(reader: BufReader<R>, commits: usize, files: usize) -> Self {
        Self {
            stream: GitLogStream::new(reader),
            store: CommitStore::with_capacity(commits, files),
        }
    }

    /// Loads all commits into the store.
    ///
    /// Returns the store containing all parsed commits.
    pub fn load_all(mut self) -> CommitStore {
        for commit in &mut self.stream {
            let id = self
                .store
                .add_commit(commit.timestamp, &commit.author, Some(&commit.hash));
            for file in commit.files {
                let path_str = file.path.to_string_lossy();
                self.store.add_file_change(id, &path_str, file.action);
            }
        }
        self.store
    }

    /// Loads commits with a callback for progress reporting.
    pub fn load_with_progress<F>(mut self, mut progress: F) -> CommitStore
    where
        F: FnMut(usize, usize), // (commits_loaded, files_loaded)
    {
        let mut commit_count = 0;
        let mut file_count = 0;

        for commit in &mut self.stream {
            let file_changes_count = commit.files.len();
            let id = self
                .store
                .add_commit(commit.timestamp, &commit.author, Some(&commit.hash));
            for file in commit.files {
                let path_str = file.path.to_string_lossy();
                self.store.add_file_change(id, &path_str, file.action);
            }
            commit_count += 1;
            file_count += file_changes_count;

            if commit_count % 1000 == 0 {
                progress(commit_count, file_count);
            }
        }

        progress(commit_count, file_count);
        self.store
    }
}

/// A streaming parser for custom format logs.
pub struct CustomLogStream<R: Read> {
    reader: BufReader<R>,
    line_buffer: String,
    finished: bool,
}

impl<R: Read> CustomLogStream<R> {
    /// Creates a new streaming parser from a reader.
    pub fn new(reader: BufReader<R>) -> Self {
        Self {
            reader,
            line_buffer: String::with_capacity(256),
            finished: false,
        }
    }

    fn read_line(&mut self) -> Option<&str> {
        self.line_buffer.clear();
        match self.reader.read_line(&mut self.line_buffer) {
            Ok(0) | Err(_) => None,
            Ok(_) => Some(self.line_buffer.trim_end()),
        }
    }
}

/// A single entry from a custom format log.
///
/// Unlike Git commits which group multiple files, custom format
/// has one file per line, so we need to group them.
#[derive(Debug, Clone)]
pub struct CustomLogEntry {
    /// Unix timestamp.
    pub timestamp: i64,
    /// Author name.
    pub author: String,
    /// File path.
    pub path: String,
    /// Action performed.
    pub action: FileAction,
}

impl<R: Read> Iterator for CustomLogStream<R> {
    type Item = CustomLogEntry;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        loop {
            let Some(l) = self.read_line() else {
                self.finished = true;
                return None;
            };
            let line = l.to_string();

            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            // Parse: timestamp|author|action|path
            let parts: Vec<&str> = line.split('|').collect();
            if parts.len() >= 4 {
                let timestamp = parts[0].parse().ok()?;
                let author = parts[1].to_string();
                let action = FileAction::from_char(parts[2].chars().next()?)?;
                let path = parts[3].to_string();

                return Some(CustomLogEntry {
                    timestamp,
                    author,
                    path,
                    action,
                });
            }
        }
    }
}

/// Groups custom log entries into commits by timestamp and author.
pub struct CustomLogGrouper<R: Read> {
    stream: CustomLogStream<R>,
    pending: Option<CustomLogEntry>,
}

impl<R: Read> CustomLogGrouper<R> {
    /// Creates a new grouper from a custom log stream.
    pub fn new(reader: BufReader<R>) -> Self {
        Self {
            stream: CustomLogStream::new(reader),
            pending: None,
        }
    }
}

impl<R: Read> Iterator for CustomLogGrouper<R> {
    type Item = Commit;

    fn next(&mut self) -> Option<Self::Item> {
        // Get first entry for this commit
        let first = self.pending.take().or_else(|| self.stream.next())?;

        let mut commit = Commit::new(
            format!("{}-{}", first.timestamp, first.author),
            first.timestamp,
            first.author.clone(),
        )
        .with_file(FileChange::new(&first.path, first.action));

        // Collect all entries with same timestamp and author
        loop {
            match self.stream.next() {
                Some(entry)
                    if entry.timestamp == first.timestamp && entry.author == first.author =>
                {
                    commit
                        .files
                        .push(FileChange::new(&entry.path, entry.action));
                }
                Some(entry) => {
                    // Different commit, save for next iteration
                    self.pending = Some(entry);
                    break;
                }
                None => break,
            }
        }

        Some(commit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn test_git_log_stream() {
        let log = "1234567890|Alice|abc123\n\
                   10\t5\tsrc/main.rs\n\
                   20\t10\tsrc/lib.rs\n\
                   \n\
                   1234567900|Bob|def456\n\
                   5\t0\tnew_file.txt\n";

        let reader = BufReader::new(Cursor::new(log));
        let stream = GitLogStream::new(reader);
        let commits: Vec<_> = stream.collect();

        assert_eq!(commits.len(), 2);

        assert_eq!(commits[0].author, "Alice");
        assert_eq!(commits[0].timestamp, 1_234_567_890);
        assert_eq!(commits[0].files.len(), 2);

        assert_eq!(commits[1].author, "Bob");
        assert_eq!(commits[1].files.len(), 1);
    }

    #[test]
    fn test_streaming_commit_loader() {
        let log = "1234567890|Alice|abc123\n\
                   10\t5\tsrc/main.rs\n\
                   \n\
                   1234567900|Alice|def456\n\
                   5\t0\tsrc/lib.rs\n";

        let reader = BufReader::new(Cursor::new(log));
        let loader = StreamingCommitLoader::new(reader);
        let store = loader.load_all();

        assert_eq!(store.commit_count(), 2);
        assert_eq!(store.file_change_count(), 2);

        // Author should be deduplicated
        let stats = store.stats();
        assert_eq!(stats.unique_authors, 1);
    }

    #[test]
    fn test_custom_log_stream() {
        let log = "1234567890|Alice|A|src/main.rs\n\
                   1234567890|Alice|M|src/lib.rs\n\
                   1234567900|Bob|D|old.txt\n";

        let reader = BufReader::new(Cursor::new(log));
        let stream = CustomLogStream::new(reader);
        let entries: Vec<_> = stream.collect();

        assert_eq!(entries.len(), 3);
        assert_eq!(entries[0].author, "Alice");
        assert_eq!(entries[0].action, FileAction::Create);
    }

    #[test]
    fn test_custom_log_grouper() {
        let log = "1234567890|Alice|A|src/main.rs\n\
                   1234567890|Alice|M|src/lib.rs\n\
                   1234567900|Bob|D|old.txt\n";

        let reader = BufReader::new(Cursor::new(log));
        let grouper = CustomLogGrouper::new(reader);
        let commits: Vec<_> = grouper.collect();

        assert_eq!(commits.len(), 2);
        assert_eq!(commits[0].author, "Alice");
        assert_eq!(commits[0].files.len(), 2);
        assert_eq!(commits[1].author, "Bob");
        assert_eq!(commits[1].files.len(), 1);
    }
}
