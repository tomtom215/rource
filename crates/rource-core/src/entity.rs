// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Entity ID types for the visualization.
//!
//! All entities in the scene are identified by typed IDs to prevent
//! mixing different entity types. IDs are lightweight (just a u32)
//! and use a generation counter for safety.

use std::fmt;

/// A generation counter used for entity ID validation.
///
/// Generations allow detecting use of stale IDs after an entity
/// has been removed and its slot reused.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Generation(u32);

impl Generation {
    /// Creates the first generation.
    #[inline]
    #[must_use]
    pub const fn first() -> Self {
        Self(1)
    }

    /// Increments the generation counter.
    #[inline]
    pub fn increment(&mut self) {
        self.0 = self.0.wrapping_add(1);
        if self.0 == 0 {
            self.0 = 1; // Skip 0 to keep NonZero optimization possible
        }
    }

    /// Returns the raw generation value.
    #[inline]
    #[must_use]
    pub const fn value(self) -> u32 {
        self.0
    }
}

impl fmt::Debug for Generation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Gen({})", self.0)
    }
}

/// Base entity ID structure with index and generation.
///
/// This is not used directly; instead use the typed ID wrappers.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct RawEntityId {
    /// The index into the entity storage.
    index: u32,
    /// The generation at which this ID was created.
    generation: Generation,
}

impl RawEntityId {
    /// Creates a new entity ID.
    #[inline]
    #[must_use]
    pub const fn new(index: u32, generation: Generation) -> Self {
        Self { index, generation }
    }

    /// Returns the index component.
    #[inline]
    #[must_use]
    pub const fn index(self) -> u32 {
        self.index
    }

    /// Returns the generation component.
    #[inline]
    #[must_use]
    pub const fn generation(self) -> Generation {
        self.generation
    }

    /// Returns the index as a usize for array indexing.
    #[inline]
    #[must_use]
    pub const fn index_usize(self) -> usize {
        self.index as usize
    }
}

impl fmt::Debug for RawEntityId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Entity({}, {:?})", self.index, self.generation)
    }
}

/// Macro to define a typed entity ID.
macro_rules! define_entity_id {
    (
        $(#[$meta:meta])*
        $name:ident, $display_name:literal
    ) => {
        $(#[$meta])*
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name(RawEntityId);

        impl $name {
            /// Creates a new ID from an index and generation.
            #[inline]
            #[must_use]
            pub const fn new(index: u32, generation: Generation) -> Self {
                Self(RawEntityId::new(index, generation))
            }

            /// Creates an ID from just an index (generation = 1).
            ///
            /// Useful for testing and simple cases.
            #[inline]
            #[must_use]
            pub const fn from_index(index: u32) -> Self {
                Self(RawEntityId::new(index, Generation::first()))
            }

            /// Returns the underlying raw ID.
            #[inline]
            #[must_use]
            pub const fn raw(self) -> RawEntityId {
                self.0
            }

            /// Returns the index component.
            #[inline]
            #[must_use]
            pub const fn index(self) -> u32 {
                self.0.index()
            }

            /// Returns the generation component.
            #[inline]
            #[must_use]
            pub const fn generation(self) -> Generation {
                self.0.generation()
            }

            /// Returns the index as a usize for array indexing.
            #[inline]
            #[must_use]
            pub const fn index_usize(self) -> usize {
                self.0.index_usize()
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(
                    f,
                    "{}({}, {:?})",
                    $display_name,
                    self.0.index,
                    self.0.generation
                )
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}#{}", $display_name, self.0.index)
            }
        }
    };
}

define_entity_id!(
    /// A unique identifier for any entity in the scene.
    EntityId, "Entity"
);

define_entity_id!(
    /// A unique identifier for a user/contributor entity.
    UserId, "User"
);

define_entity_id!(
    /// A unique identifier for a file entity.
    FileId, "File"
);

define_entity_id!(
    /// A unique identifier for a directory node.
    DirId, "Dir"
);

define_entity_id!(
    /// A unique identifier for an action (user→file beam).
    ActionId, "Action"
);

/// An ID allocator that manages entity ID creation and recycling.
///
/// This allocator maintains a free list of recycled indices and
/// tracks generations to detect stale ID usage.
#[derive(Debug, Clone)]
pub struct IdAllocator {
    /// Next index to allocate if free list is empty.
    next_index: u32,
    /// Free list of recycled indices with their current generation.
    free_list: Vec<(u32, Generation)>,
    /// Maximum number of entities ever allocated.
    high_water_mark: u32,
}

impl IdAllocator {
    /// Creates a new empty allocator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            next_index: 0,
            free_list: Vec::new(),
            high_water_mark: 0,
        }
    }

    /// Creates an allocator with pre-allocated capacity.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            next_index: 0,
            free_list: Vec::with_capacity(capacity / 4), // Assume some recycling
            high_water_mark: 0,
        }
    }

    /// Allocates a new entity ID.
    #[must_use]
    pub fn allocate(&mut self) -> RawEntityId {
        if let Some((index, generation)) = self.free_list.pop() {
            RawEntityId::new(index, generation)
        } else {
            let index = self.next_index;
            self.next_index = self.next_index.checked_add(1).expect("Entity ID overflow");
            self.high_water_mark = self.high_water_mark.max(self.next_index);
            RawEntityId::new(index, Generation::first())
        }
    }

    /// Frees an entity ID for later reuse.
    ///
    /// The generation is incremented so stale references can be detected.
    pub fn free(&mut self, id: RawEntityId) {
        let mut generation = id.generation();
        generation.increment();
        self.free_list.push((id.index(), generation));
    }

    /// Returns the number of currently allocated entities.
    #[must_use]
    pub fn len(&self) -> usize {
        (self.next_index as usize) - self.free_list.len()
    }

    /// Returns true if no entities are allocated.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the high water mark (max entities ever allocated).
    #[must_use]
    pub fn high_water_mark(&self) -> u32 {
        self.high_water_mark
    }

    /// Clears all allocations, resetting the allocator.
    pub fn clear(&mut self) {
        self.next_index = 0;
        self.free_list.clear();
        // Note: high_water_mark is intentionally not reset
    }
}

impl Default for IdAllocator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generation() {
        let mut gen = Generation::first();
        assert_eq!(gen.value(), 1);

        gen.increment();
        assert_eq!(gen.value(), 2);
    }

    #[test]
    fn test_generation_wrap() {
        let mut gen = Generation(u32::MAX);
        gen.increment();
        // Should wrap to 1, not 0
        assert_eq!(gen.value(), 1);
    }

    #[test]
    fn test_raw_entity_id() {
        let id = RawEntityId::new(42, Generation::first());
        assert_eq!(id.index(), 42);
        assert_eq!(id.generation().value(), 1);
        assert_eq!(id.index_usize(), 42);
    }

    #[test]
    fn test_typed_ids() {
        let user_id = UserId::from_index(1);
        let file_id = FileId::from_index(1);

        // Same index but different types
        assert_eq!(user_id.index(), file_id.index());

        // Display formatting
        assert_eq!(format!("{user_id}"), "User#1");
        assert_eq!(format!("{file_id}"), "File#1");
    }

    #[test]
    fn test_id_allocator() {
        let mut alloc = IdAllocator::new();

        let id1 = alloc.allocate();
        let id2 = alloc.allocate();

        assert_eq!(id1.index(), 0);
        assert_eq!(id2.index(), 1);
        assert_eq!(alloc.len(), 2);

        // Free and reallocate
        alloc.free(id1);
        assert_eq!(alloc.len(), 1);

        let id3 = alloc.allocate();
        assert_eq!(id3.index(), 0); // Reused index
        assert_eq!(id3.generation().value(), 2); // Incremented generation
        assert_eq!(alloc.len(), 2);
    }

    #[test]
    fn test_id_allocator_high_water_mark() {
        let mut alloc = IdAllocator::new();

        for _ in 0..10 {
            let _ = alloc.allocate();
        }
        assert_eq!(alloc.high_water_mark(), 10);

        // Free some
        alloc.free(RawEntityId::new(5, Generation::first()));
        alloc.free(RawEntityId::new(6, Generation::first()));

        // High water mark unchanged
        assert_eq!(alloc.high_water_mark(), 10);

        // Clear doesn't reset high water mark
        alloc.clear();
        assert_eq!(alloc.high_water_mark(), 10);
        assert!(alloc.is_empty());
    }

    #[test]
    fn test_id_allocator_with_capacity() {
        let alloc = IdAllocator::with_capacity(100);
        assert!(alloc.is_empty());
    }

    // =========================================================================
    // Extended Coverage Tests
    // =========================================================================

    #[test]
    fn test_generation_default() {
        let gen = Generation::default();
        assert_eq!(gen.value(), 0);
    }

    #[test]
    fn test_generation_debug_format() {
        let gen = Generation::first();
        let debug = format!("{gen:?}");
        assert!(debug.contains("Gen(1)"));
    }

    #[test]
    fn test_generation_equality() {
        let gen1 = Generation::first();
        let gen2 = Generation::first();
        assert_eq!(gen1, gen2);

        let mut gen3 = Generation::first();
        gen3.increment();
        assert_ne!(gen1, gen3);
    }

    #[test]
    fn test_generation_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(Generation::first());
        set.insert(Generation::first());
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_raw_entity_id_debug_format() {
        let id = RawEntityId::new(42, Generation::first());
        let debug = format!("{id:?}");
        assert!(debug.contains("Entity(42"));
    }

    #[test]
    fn test_raw_entity_id_equality() {
        let id1 = RawEntityId::new(1, Generation::first());
        let id2 = RawEntityId::new(1, Generation::first());
        let id3 = RawEntityId::new(2, Generation::first());
        assert_eq!(id1, id2);
        assert_ne!(id1, id3);
    }

    #[test]
    fn test_raw_entity_id_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(RawEntityId::new(1, Generation::first()));
        set.insert(RawEntityId::new(1, Generation::first()));
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_typed_id_new() {
        let gen = Generation::first();
        let user_id = UserId::new(5, gen);
        assert_eq!(user_id.index(), 5);
        assert_eq!(user_id.generation().value(), 1);
    }

    #[test]
    fn test_typed_id_raw() {
        let user_id = UserId::from_index(10);
        let raw = user_id.raw();
        assert_eq!(raw.index(), 10);
    }

    #[test]
    fn test_typed_id_index_usize() {
        let file_id = FileId::from_index(100);
        assert_eq!(file_id.index_usize(), 100);
    }

    #[test]
    fn test_typed_id_debug_format() {
        let dir_id = DirId::from_index(7);
        let debug = format!("{dir_id:?}");
        assert!(debug.contains("Dir(7"));
    }

    #[test]
    fn test_typed_id_display_format() {
        let action_id = ActionId::from_index(3);
        let display = format!("{action_id}");
        assert_eq!(display, "Action#3");
    }

    #[test]
    fn test_typed_id_equality() {
        let id1 = EntityId::from_index(1);
        let id2 = EntityId::from_index(1);
        let id3 = EntityId::from_index(2);
        assert_eq!(id1, id2);
        assert_ne!(id1, id3);
    }

    #[test]
    fn test_typed_id_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(FileId::from_index(1));
        set.insert(FileId::from_index(1));
        set.insert(FileId::from_index(2));
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_id_allocator_default() {
        let alloc = IdAllocator::default();
        assert!(alloc.is_empty());
        assert_eq!(alloc.high_water_mark(), 0);
    }

    #[test]
    fn test_id_allocator_debug() {
        let alloc = IdAllocator::new();
        let debug = format!("{alloc:?}");
        assert!(debug.contains("IdAllocator"));
    }

    #[test]
    fn test_id_allocator_multiple_free_reuse() {
        let mut alloc = IdAllocator::new();

        // Allocate several IDs
        let ids: Vec<_> = (0..5).map(|_| alloc.allocate()).collect();
        assert_eq!(alloc.len(), 5);

        // Free all
        for id in &ids {
            alloc.free(*id);
        }
        assert_eq!(alloc.len(), 0);

        // Reallocate - should reuse in LIFO order
        let new_id = alloc.allocate();
        assert_eq!(new_id.index(), 4); // Last freed
        assert_eq!(new_id.generation().value(), 2); // Incremented
    }
}
