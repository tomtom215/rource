# 8. Generation Counter Pattern

**Implementation**: `rource-wasm/src/render_phases/label_placer.rs` (LabelPlacer)

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

## 8.3 Implementation

### Source Code Location

| Component | File | Lines |
|-----------|------|-------|
| LabelPlacer struct | `rource-wasm/src/render_phases/label_placer.rs` | — |
| reset() method | `rource-wasm/src/render_phases/label_placer.rs` | — |
| Collision check with gen | `rource-wasm/src/render_phases/label_placer.rs` | — |
| Insert with generation | `rource-wasm/src/render_phases/label_placer.rs` | — |

### Core Implementation

**LabelPlacer with Generation Counter** (`render_phases/label_placer.rs`):

```rust
pub struct LabelPlacer {
    /// All placed label rectangles.
    placed_labels: Vec<Rect>,
    /// Spatial hash grid: each cell contains `(label_index, generation)` tuples.
    /// Indexed as `grid[cy][cx]`. Entries with old generations are stale.
    grid: Vec<Vec<Vec<(usize, u32)>>>,
    /// Current generation. Incremented on `reset()` for O(1) invalidation.
    generation: u32,
    /// Count of stale entries across all cells.
    stale_entry_count: usize,
    // ... additional fields
}
```

**O(1) Reset via Generation Increment** (`render_phases/label_placer.rs`):

```rust
#[inline]
pub fn reset(&mut self, camera_zoom: f32) {
    // Track stale entries for periodic compaction
    self.stale_entry_count += self.placed_labels.len() * 2;
    self.placed_labels.clear();

    // O(1) reset: increment generation instead of clearing 1024 cells
    self.generation = self.generation.wrapping_add(1);
    self.max_labels = compute_max_labels(camera_zoom);

    // Periodic compaction to prevent unbounded growth
    // ...
}
```

**Collision Check with Generation Filtering** (`render_phases/label_placer.rs`):

```rust
let current_gen = self.generation;

// Check for collisions only with labels in overlapping cells
// Skip stale entries (from previous generations) for O(1) reset
for cy in min_cy..=max_cy {
    for cx in min_cx..=max_cx {
        for &(label_idx, gen) in &self.grid[cy][cx] {
            // Skip stale entries from previous generations
            if gen != current_gen {
                continue;
            }
            // ... collision check
        }
    }
}
```

**Insert with Current Generation** (`render_phases/label_placer.rs`):

```rust
// Store with current generation for O(1) reset support
for cy in min_cy..=max_cy {
    for cx in min_cx..=max_cx {
        self.grid[cy][cx].push((label_idx, current_gen));
    }
}
```

### Mathematical-Code Correspondence

| Theorem | Mathematical Expression | Code Location | Implementation |
|---------|------------------------|---------------|----------------|
| 8.2 | O(1) clear | `render_phases/label_placer.rs` | `self.generation.wrapping_add(1)` |
| 8.2 | Lazy cell clear | `render_phases/label_placer.rs` | `if gen != current_gen { continue; }` |
| 8.2 | Space O(G + n) | struct fields | `grid` (G cells) + `placed_labels` (n entries) |

### Verification Commands

```bash
# Run LabelPlacer reset benchmark
cargo test -p rource-wasm bench_label_placer_reset --release -- --nocapture

# Run full label placement scenario
cargo test -p rource-wasm bench_full_label_placement_scenario --release -- --nocapture

# Verify generation counter wraparound
cargo test -p rource-wasm label_placer --release -- --nocapture
```

### Validation Checklist

- [x] O(1) reset via generation increment
- [x] Stale entries skipped during collision check
- [x] wrapping_add prevents overflow issues
- [x] Periodic compaction prevents memory growth
- [x] 90× faster reset (17,942 ns → 198 ns)

---

*[Back to Index](./README.md)*
