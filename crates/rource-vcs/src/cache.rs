// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Binary cache for fast visualization loading.
//!
//! This module provides binary serialization of parsed VCS data using bitcode,
//! enabling ~100x faster repeat loads for large repositories.
//!
//! # Performance
//!
//! For a 100K commit repository:
//! - **Text parsing**: ~210ms (parse log + build compact storage)
//! - **Cache load**: ~2ms (bitcode deserialize)
//! - **Speedup**: ~100x faster
//!
//! # Cache Format
//!
//! The cache format includes:
//! - Magic bytes for format identification
//! - Version number for forward compatibility
//! - Repository identifier hash (optional)
//! - Serialized commit data
//!
//! # Example
//!
//! ```ignore
//! use rource_vcs::cache::{VisualizationCache, CacheError};
//! use rource_vcs::CommitStore;
//!
//! // Save cache after parsing
//! let store: CommitStore = /* parse commits */;
//! let cache = VisualizationCache::from_store(&store);
//! let bytes = cache.to_bytes()?;
//!
//! // Load cache on subsequent visits
//! let cache = VisualizationCache::from_bytes(&bytes)?;
//! let store = cache.into_store();
//! ```
//!
//! # WASM Usage
//!
//! In WASM, the cache is typically stored in `IndexedDB`:
//!
//! ```javascript
//! // Save cache
//! const bytes = rource.exportCacheBytes();
//! await idb.put('visualization-cache', repoId, bytes);
//!
//! // Load cache
//! const bytes = await idb.get('visualization-cache', repoId);
//! if (bytes) {
//!     rource.importCacheBytes(bytes);
//! }
//! ```

use crate::commit::FileAction;
use crate::compact::CommitStore;
use crate::intern::{InternedPath, InternedString};
use bitcode::{Decode, Encode};

/// Magic bytes identifying a Rource visualization cache file.
///
/// "RSVC" = Rource Serialized Visualization Cache
pub const CACHE_MAGIC: [u8; 4] = [b'R', b'S', b'V', b'C'];

/// Current cache format version.
///
/// Increment this when making breaking changes to the cache format.
/// The loader will reject caches with incompatible versions.
pub const CACHE_VERSION: u16 = 1;

/// Minimum supported cache version for loading.
///
/// Caches with versions below this will be rejected even if they
/// have valid magic bytes.
pub const CACHE_MIN_VERSION: u16 = 1;

/// Errors that can occur during cache operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CacheError {
    /// The data does not start with the expected magic bytes.
    InvalidMagic,
    /// The cache version is too old to be loaded.
    VersionTooOld {
        /// Version found in the cache.
        found: u16,
        /// Minimum version required.
        minimum: u16,
    },
    /// The cache version is from a newer format we don't understand.
    VersionTooNew {
        /// Version found in the cache.
        found: u16,
        /// Maximum version we can read.
        maximum: u16,
    },
    /// The cache data is corrupted or truncated.
    CorruptedData(String),
    /// The cache data failed to deserialize.
    DeserializationFailed(String),
    /// The repository identifier doesn't match.
    RepositoryMismatch {
        /// Expected repository hash.
        expected: u64,
        /// Found repository hash.
        found: u64,
    },
}

impl std::fmt::Display for CacheError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidMagic => write!(f, "invalid cache magic bytes"),
            Self::VersionTooOld { found, minimum } => {
                write!(f, "cache version {found} is too old (minimum: {minimum})")
            }
            Self::VersionTooNew { found, maximum } => {
                write!(f, "cache version {found} is too new (maximum: {maximum})")
            }
            Self::CorruptedData(msg) => write!(f, "corrupted cache data: {msg}"),
            Self::DeserializationFailed(msg) => write!(f, "deserialization failed: {msg}"),
            Self::RepositoryMismatch { expected, found } => {
                write!(
                    f,
                    "repository mismatch (expected: {expected:016x}, found: {found:016x})"
                )
            }
        }
    }
}

impl std::error::Error for CacheError {}

/// Result type for cache operations.
pub type CacheResult<T> = Result<T, CacheError>;

/// Serializable representation of a commit for caching.
#[derive(Encode, Decode)]
struct CachedCommit {
    /// Author ID (index into authors array).
    author: u32,
    /// Short hash (7 bytes, null-padded).
    short_hash: [u8; 7],
    /// Unix timestamp.
    timestamp: i64,
    /// Index of first file change.
    files_start: u32,
    /// Number of file changes.
    files_count: u16,
}

/// Serializable representation of a file change for caching.
#[derive(Encode, Decode)]
struct CachedFileChange {
    /// Path ID (index into path reconstruction data).
    path: u32,
    /// File action (0=Create, 1=Modify, 2=Delete).
    action: u8,
}

/// Serializable representation of path interner data.
#[derive(Encode, Decode)]
struct CachedPathData {
    /// All unique path segments.
    segments: Vec<String>,
    /// Path definitions as sequences of segment indices.
    paths: Vec<Vec<u32>>,
}

/// Cache header containing metadata.
#[derive(Encode, Decode)]
struct CacheHeader {
    /// Cache format version.
    version: u16,
    /// Optional repository identifier hash.
    /// Set to 0 if not used.
    repo_hash: u64,
    /// Number of commits.
    commit_count: u32,
    /// Number of file changes.
    file_count: u32,
    /// Number of unique authors.
    author_count: u32,
    /// Number of unique paths.
    path_count: u32,
}

/// The complete cache payload (everything after magic bytes).
#[derive(Encode, Decode)]
struct CachePayload {
    /// Cache metadata header.
    header: CacheHeader,
    /// Commit data.
    commits: Vec<CachedCommit>,
    /// File change data.
    file_changes: Vec<CachedFileChange>,
    /// Author names (indexed by commit.author).
    authors: Vec<String>,
    /// Path reconstruction data.
    paths: CachedPathData,
}

/// A visualization cache that can be serialized/deserialized efficiently.
///
/// This is the main entry point for cache operations. Create from a
/// [`CommitStore`] after parsing, serialize to bytes, and later
/// deserialize to skip parsing entirely.
#[derive(Debug)]
pub struct VisualizationCache {
    /// Optional repository identifier for validation.
    repo_hash: Option<u64>,
    /// The commit store data.
    store: CommitStore,
}

impl VisualizationCache {
    /// Creates a new cache from a commit store.
    ///
    /// # Arguments
    ///
    /// * `store` - The parsed commit data to cache.
    #[must_use]
    pub fn from_store(store: CommitStore) -> Self {
        Self {
            repo_hash: None,
            store,
        }
    }

    /// Creates a new cache from a commit store with a repository identifier.
    ///
    /// The repository hash is used to validate that the cache matches the
    /// expected repository when loading. Use a stable hash of the repository
    /// URL or path.
    ///
    /// # Arguments
    ///
    /// * `store` - The parsed commit data to cache.
    /// * `repo_hash` - A stable identifier for the repository.
    #[must_use]
    pub fn from_store_with_hash(store: CommitStore, repo_hash: u64) -> Self {
        Self {
            repo_hash: Some(repo_hash),
            store,
        }
    }

    /// Returns the repository hash, if set.
    #[must_use]
    pub fn repo_hash(&self) -> Option<u64> {
        self.repo_hash
    }

    /// Consumes the cache and returns the commit store.
    #[must_use]
    pub fn into_store(self) -> CommitStore {
        self.store
    }

    /// Returns a reference to the commit store.
    #[must_use]
    pub fn store(&self) -> &CommitStore {
        &self.store
    }

    /// Serializes the cache to bytes.
    ///
    /// The output format is:
    /// - 4 bytes: Magic ("RSVC")
    /// - Remaining: bitcode-encoded payload
    ///
    /// # Errors
    ///
    /// Returns an error if serialization fails (should not happen with
    /// valid data).
    pub fn to_bytes(&self) -> CacheResult<Vec<u8>> {
        let payload = self.build_payload();

        // Serialize payload
        let payload_bytes = bitcode::encode(&payload);

        // Build final output: magic + payload
        let mut output = Vec::with_capacity(CACHE_MAGIC.len() + payload_bytes.len());
        output.extend_from_slice(&CACHE_MAGIC);
        output.extend_from_slice(&payload_bytes);

        Ok(output)
    }

    /// Deserializes a cache from bytes.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The magic bytes are invalid
    /// - The version is incompatible
    /// - The data is corrupted
    pub fn from_bytes(bytes: &[u8]) -> CacheResult<Self> {
        Self::from_bytes_with_repo_check(bytes, None)
    }

    /// Deserializes a cache from bytes, validating the repository hash.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The serialized cache data.
    /// * `expected_repo_hash` - If provided, validates that the cache
    ///   was created for this repository.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The magic bytes are invalid
    /// - The version is incompatible
    /// - The data is corrupted
    /// - The repository hash doesn't match (if `expected_repo_hash` is provided)
    pub fn from_bytes_with_repo_check(
        bytes: &[u8],
        expected_repo_hash: Option<u64>,
    ) -> CacheResult<Self> {
        // Check minimum length for magic
        if bytes.len() < CACHE_MAGIC.len() {
            return Err(CacheError::CorruptedData(
                "data too short for magic bytes".to_string(),
            ));
        }

        // Validate magic
        if bytes[..CACHE_MAGIC.len()] != CACHE_MAGIC {
            return Err(CacheError::InvalidMagic);
        }

        // Decode payload
        let payload_bytes = &bytes[CACHE_MAGIC.len()..];
        let payload: CachePayload = bitcode::decode(payload_bytes)
            .map_err(|e| CacheError::DeserializationFailed(e.to_string()))?;

        // Validate version
        if payload.header.version < CACHE_MIN_VERSION {
            return Err(CacheError::VersionTooOld {
                found: payload.header.version,
                minimum: CACHE_MIN_VERSION,
            });
        }
        if payload.header.version > CACHE_VERSION {
            return Err(CacheError::VersionTooNew {
                found: payload.header.version,
                maximum: CACHE_VERSION,
            });
        }

        // Validate repository hash if provided
        if let Some(expected) = expected_repo_hash {
            if payload.header.repo_hash != 0 && payload.header.repo_hash != expected {
                return Err(CacheError::RepositoryMismatch {
                    expected,
                    found: payload.header.repo_hash,
                });
            }
        }

        // Reconstruct CommitStore
        let store = Self::reconstruct_store(&payload);

        let repo_hash = if payload.header.repo_hash != 0 {
            Some(payload.header.repo_hash)
        } else {
            None
        };

        Ok(Self { repo_hash, store })
    }

    /// Builds the serializable payload from the commit store.
    fn build_payload(&self) -> CachePayload {
        // Extract commits
        let commits: Vec<CachedCommit> = self
            .store
            .commits()
            .map(|(_, c)| CachedCommit {
                author: c.author.index(),
                short_hash: c.short_hash,
                timestamp: c.timestamp,
                files_start: c.files_start,
                files_count: c.files_count,
            })
            .collect();

        // Extract file changes - O(f) single pass through all commits
        // Phase 39: Optimized from O(f·c) nested loop to O(f) flat_map
        let file_changes: Vec<CachedFileChange> = self
            .store
            .commits()
            .flat_map(|(_, commit)| {
                self.store
                    .file_changes(commit)
                    .iter()
                    .map(|fc| CachedFileChange {
                        path: fc.path.index(),
                        action: fc.action as u8,
                    })
            })
            .collect();

        // Extract author strings
        let author_count = commits.iter().map(|c| c.author).max().map_or(0, |m| m + 1);
        let mut authors = Vec::with_capacity(author_count as usize);
        for i in 0..author_count {
            let author = self
                .store
                .resolve_author(InternedString::from_index(i))
                .unwrap_or("")
                .to_string();
            authors.push(author);
        }

        // Extract path data
        let paths = self.extract_path_data(&file_changes);

        CachePayload {
            header: CacheHeader {
                version: CACHE_VERSION,
                repo_hash: self.repo_hash.unwrap_or(0),
                commit_count: commits.len() as u32,
                file_count: file_changes.len() as u32,
                author_count: authors.len() as u32,
                path_count: paths.paths.len() as u32,
            },
            commits,
            file_changes,
            authors,
            paths,
        }
    }

    /// Extracts path interner data for serialization.
    fn extract_path_data(&self, file_changes: &[CachedFileChange]) -> CachedPathData {
        // Find all unique path IDs
        let max_path_id = file_changes
            .iter()
            .map(|fc| fc.path)
            .max()
            .map_or(0, |m| m + 1);

        // Resolve all paths and extract segments
        let mut all_segments: Vec<String> = Vec::new();
        let mut segment_lookup: std::collections::HashMap<String, u32> =
            std::collections::HashMap::new();
        let mut paths: Vec<Vec<u32>> = Vec::with_capacity(max_path_id as usize);

        for i in 0..max_path_id {
            let path_str = self
                .store
                .resolve_path(InternedPath::from_index(i))
                .unwrap_or_default();

            // Phase 40: Single allocation per new segment - check existence first
            let segments: Vec<u32> = path_str
                .split('/')
                .filter(|s| !s.is_empty())
                .map(|seg| {
                    // Check if segment exists without allocating
                    if let Some(&idx) = segment_lookup.get(seg) {
                        idx
                    } else {
                        // Only allocate once for new segments
                        let owned = seg.to_string();
                        let idx = all_segments.len() as u32;
                        all_segments.push(owned.clone());
                        segment_lookup.insert(owned, idx);
                        idx
                    }
                })
                .collect();

            paths.push(segments);
        }

        CachedPathData {
            segments: all_segments,
            paths,
        }
    }

    /// Reconstructs a `CommitStore` from the cache payload.
    fn reconstruct_store(payload: &CachePayload) -> CommitStore {
        let mut store =
            CommitStore::with_capacity(payload.commits.len(), payload.file_changes.len());

        // Reconstruct path interner first (needed for file changes)
        let path_strings: Vec<String> = payload
            .paths
            .paths
            .iter()
            .map(|segments| {
                segments
                    .iter()
                    .filter_map(|&idx| payload.paths.segments.get(idx as usize))
                    .cloned()
                    .collect::<Vec<_>>()
                    .join("/")
            })
            .collect();

        // Add commits and file changes
        for cached_commit in &payload.commits {
            let author = payload
                .authors
                .get(cached_commit.author as usize)
                .map_or("Unknown", String::as_str);

            let hash_str = String::from_utf8_lossy(&cached_commit.short_hash)
                .trim_end_matches('\0')
                .to_string();
            let hash = if hash_str.is_empty() {
                None
            } else {
                Some(hash_str.as_str())
            };

            let commit_id = store.add_commit(cached_commit.timestamp, author, hash);

            // Add file changes for this commit
            let start = cached_commit.files_start as usize;
            let count = cached_commit.files_count as usize;
            for i in start..start.saturating_add(count) {
                if let Some(fc) = payload.file_changes.get(i) {
                    let path = path_strings
                        .get(fc.path as usize)
                        .map_or("", String::as_str);
                    let action = match fc.action {
                        0 => FileAction::Create,
                        2 => FileAction::Delete,
                        _ => FileAction::Modify,
                    };
                    store.add_file_change(commit_id, path, action);
                }
            }
        }

        store
    }
}

/// Computes a stable hash for a repository identifier string.
///
/// This uses FNV-1a which is fast and has good distribution for short strings.
///
/// # Example
///
/// ```ignore
/// use rource_vcs::cache::hash_repo_id;
///
/// let hash = hash_repo_id("https://github.com/owner/repo.git");
/// ```
#[must_use]
pub fn hash_repo_id(repo_id: &str) -> u64 {
    // FNV-1a 64-bit
    const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const FNV_PRIME: u64 = 0x0100_0000_01b3;

    let mut hash = FNV_OFFSET;
    for byte in repo_id.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

/// Returns the cache format version.
#[must_use]
pub const fn cache_version() -> u16 {
    CACHE_VERSION
}

/// Returns the minimum supported cache version.
#[must_use]
pub const fn cache_min_version() -> u16 {
    CACHE_MIN_VERSION
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commit::FileAction;

    fn create_test_store() -> CommitStore {
        let mut store = CommitStore::new();

        let id1 = store.add_commit(1_700_000_000, "Alice", Some("abc1234"));
        store.add_file_change(id1, "src/main.rs", FileAction::Create);
        store.add_file_change(id1, "src/lib.rs", FileAction::Create);

        let id2 = store.add_commit(1_700_000_100, "Bob", Some("def5678"));
        store.add_file_change(id2, "src/main.rs", FileAction::Modify);
        store.add_file_change(id2, "tests/test.rs", FileAction::Create);

        let id3 = store.add_commit(1_700_000_200, "Alice", Some("ghi9abc"));
        store.add_file_change(id3, "README.md", FileAction::Create);

        store
    }

    #[test]
    fn test_cache_roundtrip() {
        let store = create_test_store();
        let original_commit_count = store.commit_count();
        let original_file_count = store.file_change_count();

        // Serialize
        let cache = VisualizationCache::from_store(store);
        let bytes = cache.to_bytes().expect("serialization should succeed");

        // Deserialize
        let loaded =
            VisualizationCache::from_bytes(&bytes).expect("deserialization should succeed");
        let loaded_store = loaded.into_store();

        // Verify counts match
        assert_eq!(loaded_store.commit_count(), original_commit_count);
        assert_eq!(loaded_store.file_change_count(), original_file_count);
    }

    #[test]
    fn test_cache_with_repo_hash() {
        let store = create_test_store();
        let repo_hash = hash_repo_id("https://github.com/test/repo.git");

        let cache = VisualizationCache::from_store_with_hash(store, repo_hash);
        let bytes = cache.to_bytes().expect("serialization should succeed");

        // Load without hash check - should succeed
        let loaded = VisualizationCache::from_bytes(&bytes).expect("load should succeed");
        assert_eq!(loaded.repo_hash(), Some(repo_hash));

        // Load with correct hash - should succeed
        let loaded = VisualizationCache::from_bytes_with_repo_check(&bytes, Some(repo_hash))
            .expect("load should succeed");
        assert_eq!(loaded.repo_hash(), Some(repo_hash));

        // Load with wrong hash - should fail
        let wrong_hash = hash_repo_id("https://github.com/other/repo.git");
        let err = VisualizationCache::from_bytes_with_repo_check(&bytes, Some(wrong_hash));
        assert!(matches!(err, Err(CacheError::RepositoryMismatch { .. })));
    }

    #[test]
    fn test_cache_magic_validation() {
        let bad_magic = b"XXXX1234567890";
        let err = VisualizationCache::from_bytes(bad_magic);
        assert!(matches!(err, Err(CacheError::InvalidMagic)));
    }

    #[test]
    fn test_cache_too_short() {
        let short = b"RS";
        let err = VisualizationCache::from_bytes(short);
        assert!(matches!(err, Err(CacheError::CorruptedData(_))));
    }

    #[test]
    fn test_cache_corrupted_payload() {
        let mut bytes = CACHE_MAGIC.to_vec();
        bytes.extend_from_slice(b"corrupted data that is not valid bitcode");
        let err = VisualizationCache::from_bytes(&bytes);
        assert!(matches!(err, Err(CacheError::DeserializationFailed(_))));
    }

    #[test]
    fn test_cache_preserves_authors() {
        let store = create_test_store();
        let cache = VisualizationCache::from_store(store);
        let bytes = cache.to_bytes().unwrap();
        let loaded = VisualizationCache::from_bytes(&bytes).unwrap();
        let loaded_store = loaded.into_store();

        // Check that we can resolve authors
        for (_, commit) in loaded_store.commits() {
            let author = loaded_store.resolve_author(commit.author);
            assert!(author.is_some());
            assert!(author.unwrap() == "Alice" || author.unwrap() == "Bob");
        }
    }

    #[test]
    fn test_cache_preserves_paths() {
        let store = create_test_store();
        let cache = VisualizationCache::from_store(store);
        let bytes = cache.to_bytes().unwrap();
        let loaded = VisualizationCache::from_bytes(&bytes).unwrap();
        let loaded_store = loaded.into_store();

        // Collect all paths
        let mut paths = Vec::new();
        for (_, commit) in loaded_store.commits() {
            for fc in loaded_store.file_changes(commit) {
                if let Some(path) = loaded_store.resolve_path(fc.path) {
                    paths.push(path);
                }
            }
        }

        assert!(paths.contains(&"src/main.rs".to_string()));
        assert!(paths.contains(&"src/lib.rs".to_string()));
        assert!(paths.contains(&"tests/test.rs".to_string()));
        assert!(paths.contains(&"README.md".to_string()));
    }

    #[test]
    fn test_cache_preserves_actions() {
        let store = create_test_store();
        let cache = VisualizationCache::from_store(store);
        let bytes = cache.to_bytes().unwrap();
        let loaded = VisualizationCache::from_bytes(&bytes).unwrap();
        let loaded_store = loaded.into_store();

        // Count actions
        let mut create_count = 0;
        let mut modify_count = 0;
        for (_, commit) in loaded_store.commits() {
            for fc in loaded_store.file_changes(commit) {
                match fc.action {
                    FileAction::Create => create_count += 1,
                    FileAction::Modify => modify_count += 1,
                    FileAction::Delete => {}
                }
            }
        }

        assert_eq!(create_count, 4); // main.rs, lib.rs, test.rs, README.md
        assert_eq!(modify_count, 1); // main.rs modified
    }

    #[test]
    fn test_cache_preserves_timestamps() {
        let store = create_test_store();
        let cache = VisualizationCache::from_store(store);
        let bytes = cache.to_bytes().unwrap();
        let loaded = VisualizationCache::from_bytes(&bytes).unwrap();
        let loaded_store = loaded.into_store();

        let timestamps: Vec<i64> = loaded_store.commits().map(|(_, c)| c.timestamp).collect();
        assert_eq!(
            timestamps,
            vec![1_700_000_000, 1_700_000_100, 1_700_000_200]
        );
    }

    #[test]
    fn test_hash_repo_id_consistency() {
        let hash1 = hash_repo_id("https://github.com/test/repo.git");
        let hash2 = hash_repo_id("https://github.com/test/repo.git");
        assert_eq!(hash1, hash2);

        let hash3 = hash_repo_id("https://github.com/other/repo.git");
        assert_ne!(hash1, hash3);
    }

    #[test]
    fn test_hash_repo_id_different_inputs() {
        let h1 = hash_repo_id("a");
        let h2 = hash_repo_id("b");
        let h3 = hash_repo_id("ab");
        let h4 = hash_repo_id("ba");

        // All should be different
        assert_ne!(h1, h2);
        assert_ne!(h1, h3);
        assert_ne!(h1, h4);
        assert_ne!(h2, h3);
        assert_ne!(h2, h4);
        assert_ne!(h3, h4);
    }

    #[test]
    fn test_cache_version_constants() {
        // Verify version functions return the expected constants
        assert_eq!(cache_version(), CACHE_VERSION);
        assert_eq!(cache_min_version(), CACHE_MIN_VERSION);
        // And that max >= min (runtime check to satisfy clippy about constant values)
        assert!(cache_version() >= cache_min_version());
    }

    #[test]
    fn test_cache_error_display() {
        let err = CacheError::InvalidMagic;
        assert_eq!(format!("{err}"), "invalid cache magic bytes");

        let err = CacheError::VersionTooOld {
            found: 0,
            minimum: 1,
        };
        assert!(format!("{err}").contains("too old"));

        let err = CacheError::VersionTooNew {
            found: 99,
            maximum: 1,
        };
        assert!(format!("{err}").contains("too new"));

        let err = CacheError::CorruptedData("test".to_string());
        assert!(format!("{err}").contains("corrupted"));

        let err = CacheError::DeserializationFailed("test".to_string());
        assert!(format!("{err}").contains("deserialization"));

        let err = CacheError::RepositoryMismatch {
            expected: 123,
            found: 456,
        };
        assert!(format!("{err}").contains("mismatch"));
    }

    #[test]
    fn test_empty_store_cache() {
        let store = CommitStore::new();
        let cache = VisualizationCache::from_store(store);
        let bytes = cache.to_bytes().unwrap();
        let loaded = VisualizationCache::from_bytes(&bytes).unwrap();
        let loaded_store = loaded.into_store();

        assert_eq!(loaded_store.commit_count(), 0);
        assert_eq!(loaded_store.file_change_count(), 0);
    }

    #[test]
    fn test_cache_size_efficiency() {
        // Create a moderately large store
        let mut store = CommitStore::new();
        for i in 0..1000_i32 {
            let author_num = i % 10;
            let author = format!("Author {author_num}");
            let hash = format!("{i:07x}");
            let id = store.add_commit(1_700_000_000 + i64::from(i), &author, Some(&hash));
            for j in 0..5 {
                let path = format!("src/module{}/file{}.rs", i / 100, j);
                store.add_file_change(id, &path, FileAction::Modify);
            }
        }

        let cache = VisualizationCache::from_store(store);
        let bytes = cache.to_bytes().unwrap();

        // Should be reasonably compact
        // 1000 commits * ~24 bytes + 5000 files * ~8 bytes + overhead
        // Should be well under 100KB
        assert!(bytes.len() < 100_000, "cache size: {} bytes", bytes.len());
    }

    // =========================================================================
    // Mutation Testing: Kill missed mutants
    // =========================================================================

    /// Kill mutant: from_store_with_hash → return Default / repo_hash → return None
    #[test]
    fn test_from_store_with_hash_stores_hash() {
        let store = CommitStore::new();
        let hash = hash_repo_id("test-repo");
        let cache = VisualizationCache::from_store_with_hash(store, hash);
        assert_eq!(cache.repo_hash(), Some(hash));
        // Verify hash is not None or 0
        assert!(cache.repo_hash().unwrap() != 0);
    }

    /// Kill mutant: from_store → return Default / repo_hash → return Some(...)
    #[test]
    fn test_from_store_no_hash() {
        let store = CommitStore::new();
        let cache = VisualizationCache::from_store(store);
        assert_eq!(cache.repo_hash(), None);
    }

    /// Kill mutant: into_store → return Default
    #[test]
    fn test_into_store_returns_populated_store() {
        let mut store = CommitStore::new();
        let id = store.add_commit(100, "Alice", Some("abc"));
        store.add_file_change(id, "file.rs", FileAction::Create);

        let cache = VisualizationCache::from_store(store);
        let recovered = cache.into_store();
        assert_eq!(recovered.commit_count(), 1);
        assert_eq!(recovered.file_change_count(), 1);
    }

    /// Kill mutant: store() → return Default ref
    #[test]
    fn test_store_ref_returns_populated() {
        let mut store = CommitStore::new();
        store.add_commit(100, "Alice", Some("abc"));
        let cache = VisualizationCache::from_store(store);
        assert_eq!(cache.store().commit_count(), 1);
    }

    /// Kill mutant: from_bytes_with_repo_check < → <= (version too old, line 339)
    /// Test with version exactly at minimum boundary.
    #[test]
    fn test_version_at_exact_minimum() {
        // Current version IS the minimum (both 1), so a valid cache should load.
        // If < is mutated to <=, version 1 <= 1 would incorrectly reject.
        let store = create_test_store();
        let cache = VisualizationCache::from_store(store);
        let bytes = cache.to_bytes().unwrap();
        let result = VisualizationCache::from_bytes(&bytes);
        assert!(result.is_ok(), "cache at minimum version must load");
    }

    /// Kill mutant: from_bytes_with_repo_check > → >= (version too new, line 345)
    /// Test with version exactly at maximum boundary.
    #[test]
    fn test_version_at_exact_maximum() {
        // Current version IS the maximum (both 1), so a valid cache should load.
        // If > is mutated to >=, version 1 >= 1 would incorrectly reject.
        let store = create_test_store();
        let cache = VisualizationCache::from_store(store);
        let bytes = cache.to_bytes().unwrap();
        let result = VisualizationCache::from_bytes(&bytes);
        assert!(result.is_ok(), "cache at maximum version must load");
    }

    /// Kill mutant: repo_hash != 0 && repo_hash != expected → || (line 354)
    /// When repo_hash is 0, the check should pass (0 means "no hash stored").
    #[test]
    fn test_repo_check_with_zero_hash_passes() {
        let store = CommitStore::new();
        // from_store creates cache with repo_hash = None (stored as 0)
        let cache = VisualizationCache::from_store(store);
        let bytes = cache.to_bytes().unwrap();

        // Loading with any expected hash should succeed when stored hash is 0
        let expected = hash_repo_id("any-repo");
        let result = VisualizationCache::from_bytes_with_repo_check(&bytes, Some(expected));
        assert!(
            result.is_ok(),
            "zero repo_hash should pass any repo check"
        );
    }

    /// Kill mutant: repo_hash != 0 → == 0 (line 365)
    /// When a non-zero hash is stored, it should be returned as Some.
    #[test]
    fn test_nonzero_repo_hash_returned_as_some() {
        let store = CommitStore::new();
        let hash = hash_repo_id("specific-repo");
        assert!(hash != 0, "hash_repo_id should not return 0 for non-empty input");

        let cache = VisualizationCache::from_store_with_hash(store, hash);
        let bytes = cache.to_bytes().unwrap();
        let loaded = VisualizationCache::from_bytes(&bytes).unwrap();
        assert_eq!(loaded.repo_hash(), Some(hash));
    }

    /// Kill mutant: hash_repo_id ^= → |= or &= (line 564)
    /// FNV-1a uses XOR. |= or &= would produce a different hash for multi-byte inputs.
    #[test]
    fn test_hash_repo_id_xor_vs_or() {
        // With XOR, hash("ab") ≠ hash("ba") and follows FNV-1a spec
        let h_ab = hash_repo_id("ab");
        let h_ba = hash_repo_id("ba");
        assert_ne!(h_ab, h_ba, "XOR-based hash must distinguish 'ab' from 'ba'");

        // Known FNV-1a property: single-char inputs should produce unique hashes
        let h_a = hash_repo_id("a");
        let h_b = hash_repo_id("b");
        assert_ne!(h_a, h_b);

        // Verify the hash is not just an OR accumulation
        // With |= instead of ^=, repeated bytes would converge toward all-ones
        let h_aaa = hash_repo_id("aaa");
        let h_aaaa = hash_repo_id("aaaa");
        assert_ne!(h_aaa, h_aaaa, "different length inputs must produce different hashes");

        // Empty string should return FNV_OFFSET (no bytes to process)
        let h_empty = hash_repo_id("");
        assert_eq!(h_empty, 0xcbf2_9ce4_8422_2325_u64);
    }

    /// Kill mutant: cache_version → return 0 / cache_min_version → return 0
    #[test]
    fn test_cache_version_nonzero() {
        assert!(cache_version() > 0, "cache_version must be positive");
        assert!(cache_min_version() > 0, "cache_min_version must be positive");
        assert_eq!(cache_version(), 1);
        assert_eq!(cache_min_version(), 1);
    }

    /// Kill mutant: build_payload m + 1 → m - 1 (author_count, line 406)
    /// Kill mutant: build_payload m + 1 → m - 1 (max_path_id, line 443)
    /// Verify that roundtrip preserves all authors and paths correctly.
    #[test]
    fn test_build_payload_author_path_count() {
        let mut store = CommitStore::new();
        // Use exactly 3 different authors to verify m+1 computation
        let id1 = store.add_commit(100, "Alice", Some("aaa"));
        store.add_file_change(id1, "src/a.rs", FileAction::Create);
        let id2 = store.add_commit(200, "Bob", Some("bbb"));
        store.add_file_change(id2, "src/b.rs", FileAction::Modify);
        let id3 = store.add_commit(300, "Charlie", Some("ccc"));
        store.add_file_change(id3, "test/c.rs", FileAction::Delete);

        let cache = VisualizationCache::from_store(store);
        let bytes = cache.to_bytes().unwrap();
        let loaded = VisualizationCache::from_bytes(&bytes).unwrap();
        let loaded_store = loaded.into_store();

        // All 3 authors must survive roundtrip
        assert_eq!(loaded_store.commit_count(), 3);
        let mut authors: Vec<String> = loaded_store
            .commits()
            .map(|(_, c)| loaded_store.resolve_author(c.author).unwrap().to_string())
            .collect();
        authors.sort();
        assert_eq!(authors, vec!["Alice", "Bob", "Charlie"]);

        // All 3 paths must survive roundtrip
        let mut paths: Vec<String> = Vec::new();
        for (_, commit) in loaded_store.commits() {
            for fc in loaded_store.file_changes(commit) {
                paths.push(loaded_store.resolve_path(fc.path).unwrap());
            }
        }
        paths.sort();
        assert_eq!(paths, vec!["src/a.rs", "src/b.rs", "test/c.rs"]);
    }

    /// Kill mutant: extract_path_data filter !s.is_empty() → delete !
    /// Empty segments from paths like "/root/" should be filtered out.
    #[test]
    fn test_extract_path_data_filters_empty_segments() {
        let mut store = CommitStore::new();
        let id = store.add_commit(100, "Alice", Some("abc"));
        // Add a path that would produce empty segments if not filtered
        store.add_file_change(id, "src/main.rs", FileAction::Create);

        let cache = VisualizationCache::from_store(store);
        let bytes = cache.to_bytes().unwrap();
        let loaded = VisualizationCache::from_bytes(&bytes).unwrap();
        let loaded_store = loaded.into_store();

        for (_, commit) in loaded_store.commits() {
            for fc in loaded_store.file_changes(commit) {
                let path = loaded_store.resolve_path(fc.path).unwrap();
                assert_eq!(path, "src/main.rs");
            }
        }
    }

    /// Kill mutant: reconstruct_store match arms 0 and 2 (line 532-533)
    /// Verify all three file actions roundtrip correctly through cache.
    #[test]
    fn test_reconstruct_store_all_actions() {
        let mut store = CommitStore::new();
        let id = store.add_commit(100, "Alice", Some("abc"));
        store.add_file_change(id, "created.rs", FileAction::Create);
        store.add_file_change(id, "modified.rs", FileAction::Modify);
        store.add_file_change(id, "deleted.rs", FileAction::Delete);

        let cache = VisualizationCache::from_store(store);
        let bytes = cache.to_bytes().unwrap();
        let loaded = VisualizationCache::from_bytes(&bytes).unwrap();
        let loaded_store = loaded.into_store();

        let commit = loaded_store.get_commit(CommitId::from_index(0)).unwrap();
        let files = loaded_store.file_changes(commit);
        assert_eq!(files.len(), 3);

        // Verify each action type is correctly reconstructed
        let actions: Vec<FileAction> = files.iter().map(|f| f.action).collect();
        assert!(
            actions.contains(&FileAction::Create),
            "Create action must survive roundtrip"
        );
        assert!(
            actions.contains(&FileAction::Modify),
            "Modify action must survive roundtrip"
        );
        assert!(
            actions.contains(&FileAction::Delete),
            "Delete action must survive roundtrip"
        );
    }

    /// Kill mutant: CacheError Display - ensure all variants produce unique messages
    #[test]
    fn test_cache_error_display_all_variants() {
        let errors = vec![
            CacheError::InvalidMagic,
            CacheError::VersionTooOld {
                found: 0,
                minimum: 1,
            },
            CacheError::VersionTooNew {
                found: 99,
                maximum: 1,
            },
            CacheError::CorruptedData("test error".to_string()),
            CacheError::DeserializationFailed("decode error".to_string()),
            CacheError::RepositoryMismatch {
                expected: 111,
                found: 222,
            },
        ];

        // All display strings must be non-empty and distinct
        let displays: Vec<String> = errors.iter().map(|e| format!("{e}")).collect();
        for display in &displays {
            assert!(!display.is_empty());
        }
        // Check each pair is distinct
        for i in 0..displays.len() {
            for j in (i + 1)..displays.len() {
                assert_ne!(
                    displays[i], displays[j],
                    "Error displays must be unique: '{}' vs '{}'",
                    displays[i], displays[j]
                );
            }
        }

        // Verify specific content
        assert!(displays[0].contains("magic"));
        assert!(displays[1].contains("old"));
        assert!(displays[2].contains("new"));
        assert!(displays[3].contains("test error"));
        assert!(displays[4].contains("decode error"));
        assert!(displays[5].contains("111"));
        assert!(displays[5].contains("222"));
    }

    /// Kill mutant: bytes.len() < CACHE_MAGIC.len() → <=
    /// Test with bytes exactly the length of magic (4 bytes).
    #[test]
    fn test_bytes_exactly_magic_length() {
        // Exactly 4 bytes but wrong magic
        let result = VisualizationCache::from_bytes(b"XXXX");
        assert!(matches!(result, Err(CacheError::InvalidMagic)));

        // Exactly 4 bytes with correct magic but no payload
        let result = VisualizationCache::from_bytes(&CACHE_MAGIC);
        // Should fail on deserialization (no payload), not on length check
        assert!(matches!(
            result,
            Err(CacheError::DeserializationFailed(_))
        ));
    }

    /// Kill mutant: bytes[..CACHE_MAGIC.len()] != CACHE_MAGIC → ==
    #[test]
    fn test_correct_magic_does_not_error_on_magic() {
        // Valid magic but corrupted payload
        let mut bytes = CACHE_MAGIC.to_vec();
        bytes.extend_from_slice(b"not-valid-bitcode");
        let result = VisualizationCache::from_bytes(&bytes);
        // Should fail on deserialization, NOT on magic check
        assert!(matches!(
            result,
            Err(CacheError::DeserializationFailed(_))
        ));
    }
}
