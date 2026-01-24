// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! String interning for memory-efficient storage.
//!
//! This module provides a string interner that deduplicates strings by storing
//! each unique string only once and returning handles to the stored strings.
//!
//! # Example
//!
//! ```
//! use rource_vcs::intern::StringInterner;
//!
//! let mut interner = StringInterner::new();
//!
//! // First insertion allocates
//! let id1 = interner.intern("homeassistant/components/sensor");
//!
//! // Second insertion reuses the same string
//! let id2 = interner.intern("homeassistant/components/sensor");
//!
//! assert_eq!(id1, id2);
//! assert_eq!(interner.resolve(id1), Some("homeassistant/components/sensor"));
//! ```

use std::collections::HashMap;

/// A handle to an interned string.
///
/// This is a compact 32-bit identifier that can be used to retrieve
/// the original string from the interner.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InternedString(u32);

impl InternedString {
    /// Returns the raw index of this interned string.
    #[must_use]
    pub const fn index(self) -> u32 {
        self.0
    }

    /// Creates an `InternedString` from a raw index.
    ///
    /// # Safety
    ///
    /// This is safe but the caller must ensure the index is valid
    /// for the interner it will be used with. Using an invalid index
    /// will cause `resolve()` to return `None`.
    #[must_use]
    pub(crate) const fn from_index(index: u32) -> Self {
        Self(index)
    }
}

/// A string interner that stores unique strings and returns handles.
///
/// This is used to deduplicate repeated strings like file paths and
/// author names in large repositories.
#[derive(Debug, Default)]
pub struct StringInterner {
    /// Map from string to its index in the storage.
    lookup: HashMap<String, u32>,
    /// Storage for interned strings.
    strings: Vec<String>,
}

impl StringInterner {
    /// Creates a new empty interner.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an interner with pre-allocated capacity.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            lookup: HashMap::with_capacity(capacity),
            strings: Vec::with_capacity(capacity),
        }
    }

    /// Interns a string, returning a handle to it.
    ///
    /// If the string has been interned before, returns the existing handle.
    /// Otherwise, stores the string and returns a new handle.
    ///
    /// # Panics
    ///
    /// Panics if more than `u32::MAX` (4 billion) unique strings are interned.
    /// This is effectively impossible in practice as it would require hundreds
    /// of GB of memory.
    pub fn intern(&mut self, s: &str) -> InternedString {
        if let Some(&idx) = self.lookup.get(s) {
            return InternedString(idx);
        }

        // Phase 40: Single allocation - owned string is cloned once for the two containers
        let idx = u32::try_from(self.strings.len())
            .expect("string interner capacity exceeded (>4 billion unique strings)");
        let owned = s.to_owned();
        self.lookup.insert(owned.clone(), idx);
        self.strings.push(owned);
        InternedString(idx)
    }

    /// Interns an owned string, avoiding allocation if possible.
    ///
    /// # Panics
    ///
    /// Panics if more than `u32::MAX` (4 billion) unique strings are interned.
    pub fn intern_owned(&mut self, s: String) -> InternedString {
        if let Some(&idx) = self.lookup.get(&s) {
            return InternedString(idx);
        }

        // Phase 40: Clone for lookup, move original to storage
        let idx = u32::try_from(self.strings.len())
            .expect("string interner capacity exceeded (>4 billion unique strings)");
        self.lookup.insert(s.clone(), idx);
        self.strings.push(s);
        InternedString(idx)
    }

    /// Resolves an interned string handle back to the string.
    #[must_use]
    pub fn resolve(&self, id: InternedString) -> Option<&str> {
        self.strings.get(id.0 as usize).map(String::as_str)
    }

    /// Returns the number of unique strings stored.
    #[must_use]
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Returns true if the interner contains no strings.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }

    /// Returns the total bytes used by interned strings.
    #[must_use]
    pub fn total_bytes(&self) -> usize {
        self.strings.iter().map(String::len).sum()
    }

    /// Returns memory statistics for the interner.
    #[must_use]
    pub fn stats(&self) -> InternerStats {
        let string_bytes: usize = self.strings.iter().map(String::len).sum();
        let overhead = self.strings.capacity() * std::mem::size_of::<String>()
            + self.lookup.capacity() * (std::mem::size_of::<String>() + std::mem::size_of::<u32>());

        InternerStats {
            unique_strings: self.strings.len(),
            string_bytes,
            overhead_bytes: overhead,
        }
    }

    /// Clears all interned strings.
    pub fn clear(&mut self) {
        self.lookup.clear();
        self.strings.clear();
    }
}

/// Statistics about interned string storage.
#[derive(Debug, Clone, Copy)]
pub struct InternerStats {
    /// Number of unique strings stored.
    pub unique_strings: usize,
    /// Total bytes used by the string content.
    pub string_bytes: usize,
    /// Approximate overhead bytes for data structures.
    pub overhead_bytes: usize,
}

impl InternerStats {
    /// Returns total memory usage in bytes.
    #[must_use]
    pub fn total_bytes(&self) -> usize {
        self.string_bytes + self.overhead_bytes
    }
}

/// A path interner optimized for file paths.
///
/// This interner stores path segments separately and reconstructs
/// full paths when needed, saving memory for deeply nested paths.
#[derive(Debug, Default)]
pub struct PathInterner {
    /// Interner for individual path segments.
    segments: StringInterner,
    /// Full paths stored as sequences of segment IDs.
    paths: Vec<Vec<InternedString>>,
    /// Lookup from full path string to path index.
    lookup: HashMap<String, u32>,
}

/// A handle to an interned path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InternedPath(u32);

impl InternedPath {
    /// Returns the raw index of this interned path.
    #[must_use]
    pub const fn index(self) -> u32 {
        self.0
    }

    /// Creates an `InternedPath` from a raw index.
    ///
    /// # Safety
    ///
    /// This is safe but the caller must ensure the index is valid
    /// for the interner it will be used with. Using an invalid index
    /// will cause `resolve()` to return `None`.
    #[must_use]
    pub(crate) const fn from_index(index: u32) -> Self {
        Self(index)
    }
}

impl PathInterner {
    /// Creates a new empty path interner.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Interns a path, returning a handle to it.
    ///
    /// # Panics
    ///
    /// Panics if more than `u32::MAX` (4 billion) unique paths are interned.
    pub fn intern(&mut self, path: &str) -> InternedPath {
        // Check if we've seen this exact path before
        if let Some(&idx) = self.lookup.get(path) {
            return InternedPath(idx);
        }

        // Split into segments and intern each
        let segments: Vec<InternedString> = path
            .split('/')
            .filter(|s| !s.is_empty())
            .map(|seg| self.segments.intern(seg))
            .collect();

        let idx = u32::try_from(self.paths.len())
            .expect("path interner capacity exceeded (>4 billion unique paths)");
        self.paths.push(segments);
        self.lookup.insert(path.to_owned(), idx);
        InternedPath(idx)
    }

    /// Resolves an interned path handle back to the full path string.
    #[must_use]
    pub fn resolve(&self, id: InternedPath) -> Option<String> {
        let segments = self.paths.get(id.0 as usize)?;
        let parts: Vec<&str> = segments
            .iter()
            .filter_map(|&seg| self.segments.resolve(seg))
            .collect();
        Some(parts.join("/"))
    }

    /// Returns the number of unique paths stored.
    #[must_use]
    pub fn len(&self) -> usize {
        self.paths.len()
    }

    /// Returns true if the interner contains no paths.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.paths.is_empty()
    }

    /// Returns the number of unique path segments.
    #[must_use]
    pub fn segment_count(&self) -> usize {
        self.segments.len()
    }

    /// Returns memory statistics.
    #[must_use]
    pub fn stats(&self) -> PathInternerStats {
        let segment_stats = self.segments.stats();
        let path_overhead = self.paths.iter().map(|p| p.capacity() * 4).sum::<usize>()
            + self.paths.capacity() * std::mem::size_of::<Vec<InternedString>>();

        PathInternerStats {
            unique_paths: self.paths.len(),
            unique_segments: segment_stats.unique_strings,
            segment_bytes: segment_stats.string_bytes,
            overhead_bytes: segment_stats.overhead_bytes + path_overhead,
        }
    }
}

/// Statistics about path interning.
#[derive(Debug, Clone, Copy)]
pub struct PathInternerStats {
    /// Number of unique full paths.
    pub unique_paths: usize,
    /// Number of unique path segments.
    pub unique_segments: usize,
    /// Bytes used by segment strings.
    pub segment_bytes: usize,
    /// Overhead bytes for data structures.
    pub overhead_bytes: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_interner_basic() {
        let mut interner = StringInterner::new();

        let id1 = interner.intern("hello");
        let id2 = interner.intern("world");
        let id3 = interner.intern("hello"); // duplicate

        assert_eq!(id1, id3); // Same string, same ID
        assert_ne!(id1, id2); // Different strings, different IDs

        assert_eq!(interner.resolve(id1), Some("hello"));
        assert_eq!(interner.resolve(id2), Some("world"));
        assert_eq!(interner.len(), 2);
    }

    #[test]
    fn test_string_interner_owned() {
        let mut interner = StringInterner::new();

        let id1 = interner.intern_owned("owned".to_string());
        let id2 = interner.intern("owned");

        assert_eq!(id1, id2);
    }

    #[test]
    fn test_path_interner_basic() {
        let mut interner = PathInterner::new();

        let id1 = interner.intern("src/main.rs");
        let id2 = interner.intern("src/lib.rs");
        let id3 = interner.intern("src/main.rs"); // duplicate

        assert_eq!(id1, id3);
        assert_ne!(id1, id2);

        assert_eq!(interner.resolve(id1), Some("src/main.rs".to_string()));
        assert_eq!(interner.resolve(id2), Some("src/lib.rs".to_string()));

        // Both paths share the "src" segment
        assert_eq!(interner.segment_count(), 3); // "src", "main.rs", "lib.rs"
    }

    #[test]
    fn test_path_interner_deep_paths() {
        let mut interner = PathInterner::new();

        interner.intern("homeassistant/components/sensor/config_flow.py");
        interner.intern("homeassistant/components/sensor/manifest.json");
        interner.intern("homeassistant/components/switch/config_flow.py");

        // Should share common segments
        let stats = interner.stats();
        assert_eq!(stats.unique_paths, 3);
        // Segments: homeassistant, components, sensor, switch, config_flow.py, manifest.json
        assert!(stats.unique_segments <= 6);
    }

    #[test]
    fn test_interner_stats() {
        let mut interner = StringInterner::new();
        interner.intern("test");
        interner.intern("hello");
        interner.intern("test"); // duplicate

        let stats = interner.stats();
        assert_eq!(stats.unique_strings, 2);
        assert_eq!(stats.string_bytes, 9); // "test" (4) + "hello" (5)
    }

    #[test]
    fn test_string_interner_with_capacity() {
        let interner = StringInterner::with_capacity(100);
        assert!(interner.is_empty());
        assert_eq!(interner.len(), 0);
    }

    #[test]
    fn test_string_interner_clear() {
        let mut interner = StringInterner::new();
        interner.intern("one");
        interner.intern("two");
        assert_eq!(interner.len(), 2);

        interner.clear();
        assert!(interner.is_empty());
        assert_eq!(interner.len(), 0);
    }

    #[test]
    fn test_string_interner_total_bytes() {
        let mut interner = StringInterner::new();
        interner.intern("abc"); // 3 bytes
        interner.intern("defgh"); // 5 bytes
        assert_eq!(interner.total_bytes(), 8);
    }

    #[test]
    fn test_interned_string_index() {
        let mut interner = StringInterner::new();
        let id1 = interner.intern("first");
        let id2 = interner.intern("second");

        assert_eq!(id1.index(), 0);
        assert_eq!(id2.index(), 1);
    }

    #[test]
    fn test_string_interner_resolve_invalid() {
        let interner = StringInterner::new();
        let invalid_id = InternedString(999);
        assert!(interner.resolve(invalid_id).is_none());
    }

    #[test]
    fn test_path_interner_empty() {
        let interner = PathInterner::new();
        assert!(interner.is_empty());
        assert_eq!(interner.len(), 0);
        assert_eq!(interner.segment_count(), 0);
    }

    #[test]
    fn test_path_interner_new() {
        let interner = PathInterner::new();
        assert!(interner.is_empty());
        assert_eq!(interner.len(), 0);
    }

    #[test]
    fn test_path_interner_resolve_invalid() {
        let interner = PathInterner::new();
        let invalid_id = InternedPath(999);
        // Resolving an invalid ID should return None
        assert!(interner.resolve(invalid_id).is_none());
    }

    #[test]
    fn test_path_interner_single_segment() {
        let mut interner = PathInterner::new();
        let id = interner.intern("file.txt");

        assert_eq!(interner.resolve(id), Some("file.txt".to_string()));
        assert_eq!(interner.len(), 1);
        assert_eq!(interner.segment_count(), 1);
    }

    #[test]
    fn test_path_interner_segment_stats() {
        let mut interner = PathInterner::new();
        interner.intern("a/b/c"); // segments: a, b, c = 3 bytes

        let stats = interner.stats();
        assert_eq!(stats.segment_bytes, 3);
    }

    #[test]
    fn test_interned_path_index() {
        let mut interner = PathInterner::new();
        let id1 = interner.intern("one/two");
        let id2 = interner.intern("three/four");

        assert_eq!(id1.index(), 0);
        assert_eq!(id2.index(), 1);
    }

    #[test]
    fn test_path_interner_stats_comprehensive() {
        let mut interner = PathInterner::new();
        interner.intern("src/main.rs");
        interner.intern("src/lib.rs");
        interner.intern("tests/test.rs");

        let stats = interner.stats();
        assert_eq!(stats.unique_paths, 3);
        // Segments: src, main.rs, lib.rs, tests, test.rs = 5
        assert!(stats.unique_segments <= 5);
        assert!(stats.segment_bytes > 0);
    }
}
