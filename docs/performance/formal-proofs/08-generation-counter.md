# 8. Generation Counter Pattern

**Implementation**: `rource-wasm/src/render_phases.rs` (LabelPlacer)

**Category**: Data Structures

---

## 8.1 Problem Statement

Clearing a spatial hash grid of G cells takes O(G) time per frame. For G = 1024 cells at 60 FPS, this consumes 60 × 1024 = 61,440 operations per second.

---

## 8.2 Theorem: O(1) Amortized Clear via Generation Counter

**Claim**: Using a generation counter, grid clearing achieves O(1) time with O(n) space.

**Proof**:

**Data Structure**:
```rust
struct LabelPlacer {
    generation: u32,                    // Current generation
    cells: Vec<(u32, Vec<LabelEntry>)>, // (cell_generation, entries)
}
```

**Clear Operation**:
```rust
fn reset(&mut self) {
    self.generation = self.generation.wrapping_add(1);
    // No cell iteration required
}
```

Time: O(1) (single increment)

**Insert Operation**:
```rust
fn insert(&mut self, cell: usize, entry: LabelEntry) {
    let (cell_gen, entries) = &mut self.cells[cell];
    if *cell_gen != self.generation {
        entries.clear();      // Lazy clear on first access
        *cell_gen = self.generation;
    }
    entries.push(entry);
}
```

Time: O(1) amortized (clear happens at most once per cell per frame)

**Correctness**:
- Stale entries have generation < current generation
- On first access to stale cell, entries are cleared
- All queries see only current-generation entries

**Space**: O(G + n) where G = grid cells, n = labels per frame

**Benchmark Validation** (Phase 65):
| Operation | Before (O(G)) | After (O(1)) | Improvement |
|-----------|---------------|--------------|-------------|
| reset()   | 17,942 ns     | 198 ns       | 90× faster  |

∎

---

*[Back to Index](./README.md)*
