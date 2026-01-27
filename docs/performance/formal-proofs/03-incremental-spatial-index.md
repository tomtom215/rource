# 3. Incremental Spatial Index Maintenance

**Implementation**: `crates/rource-core/src/scene/spatial_methods.rs`

**Category**: Spatial Data Structures

---

## 3.1 Theorem: Incremental Update Advantage

**Claim**: For k entity position changes per frame out of n total entities, incremental maintenance achieves O(k log n) vs O(n log n) full rebuild.

**Proof**:

**Full Rebuild**:
- Clear tree: O(1)
- Insert all n entities: n × O(log n) = O(n log n)

**Incremental Update**:
- Remove k changed entities: k × O(log n)
- Re-insert k changed entities: k × O(log n)
- Total: O(k log n)

**Speedup Ratio**: n/k

**Practical Impact** (n = 10,000, k = 100):
- Full rebuild: ~130,000 operations
- Incremental: ~1,300 operations
- Speedup: **100x**. ∎

---

## 3.2 Implementation Strategy

Current implementation uses throttled full rebuild every 5 frames for simplicity. Incremental updates are a planned optimization for Phase 61.

**Trade-off Analysis**:

| Approach | Complexity | Cache Locality | Implementation |
|----------|-----------|----------------|----------------|
| Full Rebuild | O(n log n) | Excellent | Simple |
| Incremental | O(k log n) | Good | Complex (tombstones) |
| Hybrid (throttled) | O(n log n / 5) | Excellent | Simple |

---

## 3.3 Implementation

### Source Code

Located in: `crates/rource-core/src/scene/spatial_methods.rs`

#### Full Rebuild (lines 16-34)

```rust
/// Rebuilds the spatial index with current entity positions.
pub fn rebuild_spatial_index(&mut self) {
    self.spatial.clear();

    // Add directories
    for dir in self.directories.iter() {
        self.spatial
            .insert(dir.position(), EntityType::Directory(dir.id()));
    }

    // Add files
    for (id, file) in &self.files {
        self.spatial.insert(file.position(), EntityType::File(*id));
    }

    // Add users
    for (id, user) in &self.users {
        self.spatial.insert(user.position(), EntityType::User(*id));
    }
}
```

#### Zero-Allocation Visibility Query (lines 152-169)

```rust
/// Zero-allocation version of `visible_entities` that reuses existing buffers.
#[inline]
pub fn visible_entities_into(
    &self,
    bounds: &Bounds,
    dirs: &mut Vec<DirId>,
    files: &mut Vec<FileId>,
    users: &mut Vec<UserId>,
) {
    dirs.clear();
    files.clear();
    users.clear();

    // Use zero-allocation visitor pattern - no intermediate Vec allocation
    self.spatial.query_for_each(bounds, |entity| match entity {
        EntityType::Directory(id) => dirs.push(*id),
        EntityType::File(id) => files.push(*id),
        EntityType::User(id) => users.push(*id),
    });
}
```

### Mathematical-Code Correspondence

| Theorem/Equation | Code Location | Line(s) | Verification |
|------------------|---------------|---------|--------------|
| Theorem 3.1: Full rebuild O(n log n) | `rebuild_spatial_index` | 16-34 | ✓ Clears tree, inserts all n entities |
| Incremental O(k log n) | Not yet implemented | - | ⏳ Planned for Phase 61 |
| Zero-allocation query | `visible_entities_into` | 152-169 | ✓ Uses visitor pattern with reusable buffers |
| Throttled rebuild (n/5) | Scene::update() | - | ✓ Rebuilds every 5 frames |

### Verification Commands

```bash
# Run spatial methods tests
cargo test -p rource-core spatial_methods --release -- --nocapture

# Run visibility query tests
cargo test -p rource-core visible_entities --release -- --nocapture

# Run buffer clearing test
cargo test -p rource-core test_visible_entities_into_clears_buffers --release -- --nocapture
```

### Validation Checklist

- [x] Full rebuild implementation matches O(n log n) claim
- [x] Zero-allocation visitor pattern implemented
- [x] Buffer clearing verified in tests
- [ ] Incremental update (planned for Phase 61)

---

*[Back to Index](./README.md)*
