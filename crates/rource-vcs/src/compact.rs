//! Memory-efficient commit storage.
//!
//! This module provides compact alternatives to the standard `Commit` and
//! `FileChange` types that use string interning to reduce memory usage
//! for large repositories.
//!
//! # Memory Comparison
//!
//! For a repository with 100k commits and 500k file changes:
//!
//! | Structure | Standard | Compact | Savings |
//! |-----------|----------|---------|---------|
//! | Author names | 2.4 MB | 50 KB | 98% |
//! | File paths | 25 MB | 2 MB | 92% |
//! | Commit hashes | 4 MB | 0.7 MB | 82% |
//!
//! # Example
//!
//! ```
//! use rource_vcs::compact::{CommitStore, CompactFileChange};
//! use rource_vcs::FileAction;
//!
//! let mut store = CommitStore::new();
//!
//! // Add a commit
//! let commit_id = store.add_commit(1234567890, "John Doe", Some("abc123def"));
//!
//! // Add file changes
//! store.add_file_change(commit_id, "src/main.rs", FileAction::Create);
//! store.add_file_change(commit_id, "src/lib.rs", FileAction::Modify);
//!
//! // Retrieve commit info
//! let commit = store.get_commit(commit_id).unwrap();
//! assert_eq!(store.resolve_author(commit.author), Some("John Doe"));
//! ```

use crate::commit::{Commit, FileAction, FileChange};
use crate::intern::{InternedPath, InternedString, PathInterner, StringInterner};
use std::path::PathBuf;

/// A compact representation of a file change.
///
/// Uses only 8 bytes compared to ~48+ bytes for the standard `FileChange`.
#[derive(Debug, Clone, Copy)]
pub struct CompactFileChange {
    /// Interned path handle.
    pub path: InternedPath,
    /// The action performed on the file.
    pub action: FileAction,
}

/// A compact representation of a commit.
///
/// Uses interned strings for author names and short hashes.
#[derive(Debug, Clone, Copy)]
pub struct CompactCommit {
    /// Interned author name handle.
    pub author: InternedString,
    /// Short hash (7 chars) stored inline.
    pub short_hash: [u8; 7],
    /// Unix timestamp.
    pub timestamp: i64,
    /// Index of first file change in the file changes array.
    pub files_start: u32,
    /// Number of file changes.
    pub files_count: u16,
}

/// A unique identifier for a commit in the store.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CommitId(u32);

impl CommitId {
    /// Returns the raw index.
    #[must_use]
    pub const fn index(self) -> u32 {
        self.0
    }
}

/// Memory-efficient storage for commits and file changes.
///
/// This store uses string interning to deduplicate repeated strings
/// like author names and file paths, significantly reducing memory
/// usage for large repositories.
#[derive(Debug, Default)]
pub struct CommitStore {
    /// Interner for author names.
    authors: StringInterner,
    /// Interner for file paths.
    paths: PathInterner,
    /// All commits in order.
    commits: Vec<CompactCommit>,
    /// All file changes (referenced by commits).
    file_changes: Vec<CompactFileChange>,
}

impl CommitStore {
    /// Creates a new empty commit store.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a store with pre-allocated capacity.
    #[must_use]
    pub fn with_capacity(commits: usize, files: usize) -> Self {
        Self {
            authors: StringInterner::with_capacity(commits / 100), // ~100 commits per author
            paths: PathInterner::new(),
            commits: Vec::with_capacity(commits),
            file_changes: Vec::with_capacity(files),
        }
    }

    /// Adds a new commit to the store.
    ///
    /// Returns a `CommitId` that can be used to add file changes.
    pub fn add_commit(&mut self, timestamp: i64, author: &str, hash: Option<&str>) -> CommitId {
        let author_id = self.authors.intern(author);

        let mut short_hash = [0u8; 7];
        if let Some(h) = hash {
            let bytes = h.as_bytes();
            let len = bytes.len().min(7);
            short_hash[..len].copy_from_slice(&bytes[..len]);
        }

        let commit = CompactCommit {
            author: author_id,
            short_hash,
            timestamp,
            files_start: self.file_changes.len() as u32,
            files_count: 0,
        };

        let id = CommitId(self.commits.len() as u32);
        self.commits.push(commit);
        id
    }

    /// Adds a file change to a commit.
    ///
    /// # Panics
    ///
    /// Panics if the `commit_id` is invalid or if too many files are added
    /// to a single commit (max 65535).
    pub fn add_file_change(&mut self, commit_id: CommitId, path: &str, action: FileAction) {
        let path_id = self.paths.intern(path);

        let change = CompactFileChange {
            path: path_id,
            action,
        };

        self.file_changes.push(change);

        let commit = &mut self.commits[commit_id.0 as usize];
        commit.files_count = commit
            .files_count
            .checked_add(1)
            .expect("too many files in commit");
    }

    /// Gets a commit by ID.
    #[must_use]
    pub fn get_commit(&self, id: CommitId) -> Option<&CompactCommit> {
        self.commits.get(id.0 as usize)
    }

    /// Returns an iterator over all commits.
    pub fn commits(&self) -> impl Iterator<Item = (CommitId, &CompactCommit)> {
        self.commits
            .iter()
            .enumerate()
            .map(|(i, c)| (CommitId(i as u32), c))
    }

    /// Returns the file changes for a commit.
    #[must_use]
    pub fn file_changes(&self, commit: &CompactCommit) -> &[CompactFileChange] {
        let start = commit.files_start as usize;
        let end = start + commit.files_count as usize;
        &self.file_changes[start..end]
    }

    /// Resolves an author ID to the author name.
    #[must_use]
    pub fn resolve_author(&self, id: InternedString) -> Option<&str> {
        self.authors.resolve(id)
    }

    /// Resolves a path ID to the full path string.
    #[must_use]
    pub fn resolve_path(&self, id: InternedPath) -> Option<String> {
        self.paths.resolve(id)
    }

    /// Returns the number of commits.
    #[must_use]
    pub fn commit_count(&self) -> usize {
        self.commits.len()
    }

    /// Returns the number of file changes.
    #[must_use]
    pub fn file_change_count(&self) -> usize {
        self.file_changes.len()
    }

    /// Returns memory statistics.
    #[must_use]
    pub fn stats(&self) -> CommitStoreStats {
        let author_stats = self.authors.stats();
        let path_stats = self.paths.stats();

        let commits_bytes = self.commits.capacity() * std::mem::size_of::<CompactCommit>();
        let files_bytes = self.file_changes.capacity() * std::mem::size_of::<CompactFileChange>();

        CommitStoreStats {
            commit_count: self.commits.len(),
            file_change_count: self.file_changes.len(),
            unique_authors: author_stats.unique_strings,
            unique_paths: path_stats.unique_paths,
            unique_path_segments: path_stats.unique_segments,
            author_bytes: author_stats.string_bytes,
            path_segment_bytes: path_stats.segment_bytes,
            struct_bytes: commits_bytes + files_bytes,
            overhead_bytes: author_stats.overhead_bytes + path_stats.overhead_bytes,
        }
    }

    /// Converts a compact commit to a standard Commit.
    ///
    /// This allocates new strings, so should only be used when
    /// the standard format is required.
    #[must_use]
    pub fn to_standard_commit(&self, id: CommitId) -> Option<Commit> {
        let compact = self.get_commit(id)?;
        let author = self.resolve_author(compact.author)?;

        let hash = String::from_utf8_lossy(&compact.short_hash)
            .trim_end_matches('\0')
            .to_string();

        let files: Vec<FileChange> = self
            .file_changes(compact)
            .iter()
            .filter_map(|fc| {
                let path = self.resolve_path(fc.path)?;
                Some(FileChange::new(PathBuf::from(path), fc.action))
            })
            .collect();

        Some(Commit {
            hash,
            timestamp: compact.timestamp,
            author: author.to_string(),
            email: None,
            files,
        })
    }

    /// Imports standard commits into the compact store.
    pub fn import_commits(&mut self, commits: impl IntoIterator<Item = Commit>) {
        for commit in commits {
            let id = self.add_commit(commit.timestamp, &commit.author, Some(&commit.hash));
            for file in commit.files {
                let path_str = file.path.to_string_lossy();
                self.add_file_change(id, &path_str, file.action);
            }
        }
    }
}

/// Statistics about commit store memory usage.
#[derive(Debug, Clone, Copy)]
pub struct CommitStoreStats {
    /// Number of commits stored.
    pub commit_count: usize,
    /// Number of file changes stored.
    pub file_change_count: usize,
    /// Number of unique author names.
    pub unique_authors: usize,
    /// Number of unique file paths.
    pub unique_paths: usize,
    /// Number of unique path segments.
    pub unique_path_segments: usize,
    /// Bytes used by author name strings.
    pub author_bytes: usize,
    /// Bytes used by path segment strings.
    pub path_segment_bytes: usize,
    /// Bytes used by commit/file structures.
    pub struct_bytes: usize,
    /// Overhead bytes for hash tables etc.
    pub overhead_bytes: usize,
}

impl CommitStoreStats {
    /// Returns total memory usage in bytes.
    #[must_use]
    pub fn total_bytes(&self) -> usize {
        self.author_bytes + self.path_segment_bytes + self.struct_bytes + self.overhead_bytes
    }

    /// Formats the stats as a human-readable string.
    #[must_use]
    pub fn display(&self) -> String {
        format!(
            "CommitStore:\n\
             - Commits: {}\n\
             - File changes: {}\n\
             - Unique authors: {}\n\
             - Unique paths: {} ({} segments)\n\
             - Memory: {:.2} MB total\n\
             - Author strings: {:.2} KB\n\
             - Path strings: {:.2} KB\n\
             - Structures: {:.2} KB\n\
             - Overhead: {:.2} KB",
            self.commit_count,
            self.file_change_count,
            self.unique_authors,
            self.unique_paths,
            self.unique_path_segments,
            self.total_bytes() as f64 / 1024.0 / 1024.0,
            self.author_bytes as f64 / 1024.0,
            self.path_segment_bytes as f64 / 1024.0,
            self.struct_bytes as f64 / 1024.0,
            self.overhead_bytes as f64 / 1024.0,
        )
    }
}

/// Estimates memory usage of standard commits.
#[must_use]
pub fn estimate_standard_memory(commits: &[Commit]) -> StandardMemoryEstimate {
    let mut total_hash_bytes = 0;
    let mut total_author_bytes = 0;
    let mut total_path_bytes = 0;
    let mut total_file_count = 0;

    for commit in commits {
        total_hash_bytes += commit.hash.len();
        total_author_bytes += commit.author.len();
        if let Some(email) = &commit.email {
            total_author_bytes += email.len();
        }

        for file in &commit.files {
            total_path_bytes += file.path.as_os_str().len();
            total_file_count += 1;
        }
    }

    // Estimate struct overhead
    let commit_struct_size = std::mem::size_of::<Commit>();
    let file_struct_size = std::mem::size_of::<FileChange>();

    // We intentionally calculate struct memory as count * size_of::<T>() for estimation
    // purposes, not size_of_val() which would give different semantics
    #[allow(clippy::manual_slice_size_calculation)]
    StandardMemoryEstimate {
        commit_count: commits.len(),
        file_count: total_file_count,
        hash_bytes: total_hash_bytes,
        author_bytes: total_author_bytes,
        path_bytes: total_path_bytes,
        struct_bytes: commits.len() * commit_struct_size + total_file_count * file_struct_size,
    }
}

/// Memory estimate for standard commit storage.
#[derive(Debug, Clone, Copy)]
pub struct StandardMemoryEstimate {
    /// Number of commits.
    pub commit_count: usize,
    /// Number of file changes.
    pub file_count: usize,
    /// Bytes for commit hashes.
    pub hash_bytes: usize,
    /// Bytes for author names.
    pub author_bytes: usize,
    /// Bytes for file paths.
    pub path_bytes: usize,
    /// Bytes for struct overhead.
    pub struct_bytes: usize,
}

impl StandardMemoryEstimate {
    /// Returns total estimated memory.
    #[must_use]
    pub fn total_bytes(&self) -> usize {
        self.hash_bytes + self.author_bytes + self.path_bytes + self.struct_bytes
    }

    /// Formats as human-readable string.
    #[must_use]
    pub fn display(&self) -> String {
        format!(
            "Standard Storage:\n\
             - Commits: {}\n\
             - File changes: {}\n\
             - Total: {:.2} MB\n\
             - Hashes: {:.2} KB\n\
             - Authors: {:.2} KB\n\
             - Paths: {:.2} KB\n\
             - Structs: {:.2} KB",
            self.commit_count,
            self.file_count,
            self.total_bytes() as f64 / 1024.0 / 1024.0,
            self.hash_bytes as f64 / 1024.0,
            self.author_bytes as f64 / 1024.0,
            self.path_bytes as f64 / 1024.0,
            self.struct_bytes as f64 / 1024.0,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_commit_store_basic() {
        let mut store = CommitStore::new();

        let id = store.add_commit(1234567890, "John Doe", Some("abc123def456"));
        store.add_file_change(id, "src/main.rs", FileAction::Create);
        store.add_file_change(id, "src/lib.rs", FileAction::Modify);

        assert_eq!(store.commit_count(), 1);
        assert_eq!(store.file_change_count(), 2);

        let commit = store.get_commit(id).unwrap();
        assert_eq!(store.resolve_author(commit.author), Some("John Doe"));

        let files = store.file_changes(commit);
        assert_eq!(files.len(), 2);
        assert_eq!(
            store.resolve_path(files[0].path),
            Some("src/main.rs".to_string())
        );
    }

    #[test]
    fn test_commit_store_deduplication() {
        let mut store = CommitStore::new();

        // Same author for multiple commits
        let id1 = store.add_commit(100, "Alice", None);
        let id2 = store.add_commit(200, "Alice", None);
        let id3 = store.add_commit(300, "Bob", None);

        // Same path in multiple commits
        store.add_file_change(id1, "src/main.rs", FileAction::Create);
        store.add_file_change(id2, "src/main.rs", FileAction::Modify);
        store.add_file_change(id3, "src/main.rs", FileAction::Delete);

        let stats = store.stats();
        assert_eq!(stats.unique_authors, 2); // Alice, Bob
        assert_eq!(stats.unique_paths, 1); // src/main.rs
    }

    #[test]
    fn test_to_standard_commit() {
        let mut store = CommitStore::new();

        let id = store.add_commit(1234567890, "Test User", Some("abcdef1"));
        store.add_file_change(id, "file.txt", FileAction::Create);

        let standard = store.to_standard_commit(id).unwrap();
        assert_eq!(standard.author, "Test User");
        assert_eq!(standard.timestamp, 1234567890);
        assert_eq!(standard.short_hash(), "abcdef1");
        assert_eq!(standard.files.len(), 1);
    }

    #[test]
    fn test_import_commits() {
        let commits = vec![
            Commit::new("abc123", 100, "Alice")
                .with_file(FileChange::create("a.txt"))
                .with_file(FileChange::modify("b.txt")),
            Commit::new("def456", 200, "Bob").with_file(FileChange::delete("c.txt")),
        ];

        let mut store = CommitStore::new();
        store.import_commits(commits);

        assert_eq!(store.commit_count(), 2);
        assert_eq!(store.file_change_count(), 3);
    }
}
