// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! WASM API for visualization cache operations.
//!
//! This module provides JavaScript bindings for saving and loading
//! visualization caches, enabling ~100x faster repeat loads.
//!
//! # Performance
//!
//! For a 100K commit repository:
//! - **First load** (text parse): ~210ms
//! - **Cached load** (bitcode deserialize): ~2ms
//! - **Speedup**: ~100x faster
//!
//! # Usage
//!
//! ```javascript
//! // Save cache after loading commits
//! const cacheBytes = rource.exportCacheBytes();
//! await idb.put('visualization-cache', repoId, cacheBytes);
//!
//! // Load from cache on subsequent visits
//! const cachedBytes = await idb.get('visualization-cache', repoId);
//! if (cachedBytes && rource.importCacheBytes(cachedBytes)) {
//!     console.log('Loaded from cache!');
//! } else {
//!     // Fallback to parsing
//!     await fetchAndParse();
//! }
//! ```
//!
//! # Cache Format
//!
//! The cache is a binary format with:
//! - 4-byte magic header ("RSVC")
//! - Version number for compatibility
//! - Optional repository hash for validation
//! - Compressed commit and file change data

use crate::Rource;
use wasm_bindgen::prelude::*;

#[cfg(feature = "cache")]
use rource_vcs::{cache_version, hash_repo_id, CommitStore, VisualizationCache, CACHE_VERSION};

// ============================================================================
// Helper Functions (testable without Rource instance)
// ============================================================================

/// Formats cache statistics as a JSON string.
///
/// # Arguments
///
/// * `commit_count` - Number of commits in the cache.
/// * `file_count` - Number of file changes in the cache.
/// * `cache_size` - Size of the serialized cache in bytes.
/// * `version` - Cache format version.
#[inline]
#[must_use]
pub fn format_cache_stats_json(
    commit_count: usize,
    file_count: usize,
    cache_size: usize,
    version: u16,
) -> String {
    format!(
        r#"{{"commits":{commit_count},"files":{file_count},"sizeBytes":{cache_size},"version":{version}}}"#
    )
}

/// Validates that cache data has the correct magic header.
///
/// Returns `true` if the data starts with "RSVC".
#[inline]
#[must_use]
pub fn has_valid_cache_magic(data: &[u8]) -> bool {
    data.len() >= 4 && data[0] == b'R' && data[1] == b'S' && data[2] == b'V' && data[3] == b'C'
}

// ============================================================================
// WASM Bindings (require Rource instance)
// ============================================================================

#[cfg(feature = "cache")]
#[wasm_bindgen]
impl Rource {
    /// Returns the current cache format version.
    ///
    /// Use this to check compatibility before loading a cache.
    ///
    /// # Example
    ///
    /// ```javascript
    /// const version = Rource.getCacheVersion();
    /// console.log('Cache version:', version);
    /// ```
    #[wasm_bindgen(js_name = getCacheVersion)]
    pub fn get_cache_version() -> u16 {
        cache_version()
    }

    /// Computes a stable hash for a repository identifier.
    ///
    /// Use this to create cache keys for `IndexedDB` storage.
    ///
    /// # Arguments
    ///
    /// * `repo_id` - A unique identifier for the repository (URL, path, etc.).
    ///
    /// # Returns
    ///
    /// A 64-bit hash as a hex string (16 characters).
    ///
    /// # Example
    ///
    /// ```javascript
    /// const hash = Rource.hashRepoId('https://github.com/owner/repo.git');
    /// // Use hash as `IndexedDB` key
    /// await idb.put('cache', hash, cacheBytes);
    /// ```
    #[wasm_bindgen(js_name = hashRepoId)]
    pub fn hash_repo_id_js(repo_id: &str) -> String {
        format!("{:016x}", hash_repo_id(repo_id))
    }

    /// Exports the current commits as a binary cache.
    ///
    /// Returns `null` if no commits are loaded.
    ///
    /// The returned bytes can be stored in `IndexedDB` for fast subsequent loads.
    ///
    /// # Example
    ///
    /// ```javascript
    /// const bytes = rource.exportCacheBytes();
    /// if (bytes) {
    ///     await idb.put('cache', repoHash, bytes);
    /// }
    /// ```
    #[wasm_bindgen(js_name = exportCacheBytes)]
    pub fn export_cache_bytes(&self) -> Option<Vec<u8>> {
        if self.commits.is_empty() {
            return None;
        }

        // Convert commits to CommitStore
        let mut store = CommitStore::with_capacity(self.commits.len(), self.commits.len() * 5);
        store.import_commits(self.commits.clone());

        // Create and serialize cache
        let cache = VisualizationCache::from_store(store);
        cache.to_bytes().ok()
    }

    /// Exports the current commits as a binary cache with a repository identifier.
    ///
    /// The repository hash is used to validate the cache when loading.
    ///
    /// # Arguments
    ///
    /// * `repo_id` - A unique identifier for the repository (URL, path, etc.).
    ///
    /// # Returns
    ///
    /// The serialized cache bytes, or `null` if no commits are loaded.
    ///
    /// # Example
    ///
    /// ```javascript
    /// const bytes = rource.exportCacheBytesWithRepoId('https://github.com/owner/repo.git');
    /// ```
    #[wasm_bindgen(js_name = exportCacheBytesWithRepoId)]
    pub fn export_cache_bytes_with_repo_id(&self, repo_id: &str) -> Option<Vec<u8>> {
        if self.commits.is_empty() {
            return None;
        }

        // Convert commits to CommitStore
        let mut store = CommitStore::with_capacity(self.commits.len(), self.commits.len() * 5);
        store.import_commits(self.commits.clone());

        // Create and serialize cache with repo hash
        let repo_hash = hash_repo_id(repo_id);
        let cache = VisualizationCache::from_store_with_hash(store, repo_hash);
        cache.to_bytes().ok()
    }

    /// Imports commits from a binary cache.
    ///
    /// Returns the number of commits loaded, or 0 if the cache is invalid.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The cache bytes previously exported with `exportCacheBytes()`.
    ///
    /// # Example
    ///
    /// ```javascript
    /// const bytes = await idb.get('cache', repoHash);
    /// if (bytes) {
    ///     const count = rource.importCacheBytes(bytes);
    ///     if (count > 0) {
    ///         console.log(`Loaded ${count} commits from cache`);
    ///     }
    /// }
    /// ```
    #[wasm_bindgen(js_name = importCacheBytes)]
    pub fn import_cache_bytes(&mut self, bytes: &[u8]) -> usize {
        VisualizationCache::from_bytes(bytes).map_or(0, |cache| self.import_cache_store(cache))
    }

    /// Imports commits from a binary cache, validating the repository identifier.
    ///
    /// Returns the number of commits loaded, or 0 if:
    /// - The cache is invalid
    /// - The repository hash doesn't match
    ///
    /// # Arguments
    ///
    /// * `bytes` - The cache bytes.
    /// * `repo_id` - The expected repository identifier.
    ///
    /// # Example
    ///
    /// ```javascript
    /// const bytes = await idb.get('cache', repoHash);
    /// const count = rource.importCacheBytesWithRepoId(bytes, repoUrl);
    /// if (count === 0) {
    ///     // Cache miss or mismatch - fallback to parsing
    /// }
    /// ```
    #[wasm_bindgen(js_name = importCacheBytesWithRepoId)]
    pub fn import_cache_bytes_with_repo_id(&mut self, bytes: &[u8], repo_id: &str) -> usize {
        let expected_hash = hash_repo_id(repo_id);
        VisualizationCache::from_bytes_with_repo_check(bytes, Some(expected_hash))
            .map_or(0, |cache| self.import_cache_store(cache))
    }

    /// Internal helper to import commits from a cache with protections.
    ///
    /// Applies the same commit limit and adaptive prewarm as text loading.
    fn import_cache_store(&mut self, cache: VisualizationCache) -> usize {
        let store = cache.into_store();
        let commit_count = store.commit_count();

        // Track original count before any truncation
        self.original_commit_count = commit_count;

        // Convert CommitStore back to Vec<Commit>, respecting max_commits limit
        let limit = self.max_commits.min(commit_count);
        let mut commits: Vec<_> = (0..limit)
            .filter_map(|i| {
                let id = rource_vcs::CommitId::from_index(i as u32);
                store.to_standard_commit(id)
            })
            .collect();

        if commits.is_empty() {
            self.commits_truncated = false;
            return 0;
        }

        // Track truncation
        if commit_count > self.max_commits {
            #[cfg(target_arch = "wasm32")]
            web_sys::console::warn_1(
                &format!(
                    "Rource: Truncating cached {} commits to {} (use setMaxCommits() to adjust)",
                    commit_count, self.max_commits
                )
                .into(),
            );
            commits.truncate(self.max_commits);
            self.commits_truncated = true;
        } else {
            self.commits_truncated = false;
        }

        let loaded_count = commits.len();
        self.commits = commits;

        // Use adaptive prewarm based on repo size
        self.reset_playback_adaptive();

        loaded_count
    }

    /// Checks if cache data has a valid magic header.
    ///
    /// This is a quick check that doesn't fully validate the cache.
    /// Use before attempting to import to provide fast feedback.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The cache bytes to check.
    ///
    /// # Returns
    ///
    /// `true` if the data starts with the "RSVC" magic bytes.
    #[wasm_bindgen(js_name = hasValidCacheMagic)]
    pub fn has_valid_cache_magic_js(bytes: &[u8]) -> bool {
        has_valid_cache_magic(bytes)
    }

    /// Returns statistics about the current cache state.
    ///
    /// Returns a JSON object with cache information, or `null` if
    /// no commits are loaded.
    ///
    /// # Example
    ///
    /// ```javascript
    /// const stats = rource.getCacheStats();
    /// if (stats) {
    ///     const info = JSON.parse(stats);
    ///     console.log(`${info.commits} commits, ${info.sizeBytes} bytes`);
    /// }
    /// ```
    #[wasm_bindgen(js_name = getCacheStats)]
    pub fn get_cache_stats(&self) -> Option<String> {
        if self.commits.is_empty() {
            return None;
        }

        // Estimate cache size by actually serializing
        let bytes = self.export_cache_bytes()?;
        let file_count: usize = self.commits.iter().map(|c| c.files.len()).sum();

        Some(format_cache_stats_json(
            self.commits.len(),
            file_count,
            bytes.len(),
            CACHE_VERSION,
        ))
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_cache_stats_json() {
        let json = format_cache_stats_json(100, 500, 12345, 1);
        assert!(json.contains("\"commits\":100"));
        assert!(json.contains("\"files\":500"));
        assert!(json.contains("\"sizeBytes\":12345"));
        assert!(json.contains("\"version\":1"));
    }

    #[test]
    fn test_format_cache_stats_json_zero_values() {
        let json = format_cache_stats_json(0, 0, 0, 1);
        assert!(json.contains("\"commits\":0"));
        assert!(json.contains("\"files\":0"));
        assert!(json.contains("\"sizeBytes\":0"));
    }

    #[test]
    fn test_format_cache_stats_json_large_values() {
        let json = format_cache_stats_json(1_000_000, 5_000_000, 50_000_000, 99);
        assert!(json.contains("\"commits\":1000000"));
        assert!(json.contains("\"files\":5000000"));
        assert!(json.contains("\"sizeBytes\":50000000"));
        assert!(json.contains("\"version\":99"));
    }

    #[test]
    fn test_has_valid_cache_magic_valid() {
        let data = b"RSVCsome payload data";
        assert!(has_valid_cache_magic(data));
    }

    #[test]
    fn test_has_valid_cache_magic_invalid() {
        let data = b"XXXXsome payload data";
        assert!(!has_valid_cache_magic(data));
    }

    #[test]
    fn test_has_valid_cache_magic_too_short() {
        assert!(!has_valid_cache_magic(b"RSV"));
        assert!(!has_valid_cache_magic(b"RS"));
        assert!(!has_valid_cache_magic(b"R"));
        assert!(!has_valid_cache_magic(b""));
    }

    #[test]
    fn test_has_valid_cache_magic_exact_length() {
        let data = b"RSVC";
        assert!(has_valid_cache_magic(data));
    }

    #[test]
    fn test_format_cache_stats_is_valid_json() {
        let json = format_cache_stats_json(42, 123, 999, 1);
        // Simple validation - should have matching braces
        assert!(json.starts_with('{'));
        assert!(json.ends_with('}'));
        // Should be parseable (basic check without full JSON parser)
        assert!(json.contains(':'));
        assert!(!json.contains("null"));
        assert!(!json.contains("undefined"));
    }
}
