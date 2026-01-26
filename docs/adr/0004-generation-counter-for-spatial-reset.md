# ADR 0004: Generation Counter Pattern for Spatial Grid Reset

## Status

Accepted

## Date

2025-01-20

## Context

The label placement system uses a spatial hash grid for collision detection. Each frame, the grid needs to be "reset" to track new label positions.

**Problem**: Traditional grid reset clears all cells:
```rust
// O(n) where n = grid cells (e.g., 32×32 = 1024)
for cell in &mut self.grid {
    cell.clear();
}
```

At 50,000 FPS target (20µs budget), even this simple operation is measurable:
- 1024 cells × ~1ns/clear = ~1µs overhead
- This is 5% of total frame budget

**Constraint**: Cannot eliminate collision detection entirely; it's needed for label quality.

## Decision

Use generation counter pattern to achieve O(1) amortized reset.

**Implementation**:
```rust
struct LabelPlacer {
    grid: Vec<Vec<CellEntry>>,
    generation: u32,  // Increments each frame
}

struct CellEntry {
    generation: u32,  // When this entry was written
    bounds: Rect,
}

fn reset(&mut self) {
    self.generation = self.generation.wrapping_add(1);  // O(1)
}

fn is_occupied(&self, cell_idx: usize) -> bool {
    // Only "occupied" if generation matches
    self.grid[cell_idx].iter()
        .any(|e| e.generation == self.generation)
}
```

Old entries are effectively "invisible" once generation advances.

## Consequences

### Positive

- **O(1) reset**: Just increment a counter
- **Measured improvement**: 198ns reset time (vs ~1µs for clearing)
- **Zero allocations**: No Vec::clear() means no deallocation
- **Cache friendly**: No touching all grid memory

### Negative

- **Memory overhead**: Old entries persist until overwritten
- **Complexity**: Must check generation on every access
- **Overflow handling**: Generation counter can wrap (handled with wrapping_add)
- **Debugging difficulty**: Grid contents don't reflect "logical" state

### Neutral

- Memory usage bounded by max labels ever placed (not cumulative)
- After 2^32 frames (~19 hours at 60fps), generation wraps (benign)

## Alternatives Considered

### Alternative 1: Vec::clear() Each Cell

Traditional clearing of all cell vectors.

**Rejected because**:
- O(n) in grid size
- Touches all memory (cache thrashing)
- 5x slower than generation counter

### Alternative 2: Replace Grid Each Frame

Allocate new grid, drop old one.

**Rejected because**:
- O(n) allocation
- Memory pressure from allocations
- Worse than clearing

### Alternative 3: Bitset for Occupancy

Separate bitset tracking which cells have content.

**Rejected because**:
- Still O(n) to reset bitset
- Additional data structure overhead
- More complex API

## References

- `crates/rource-render/src/label.rs` - LabelPlacer implementation
- `docs/performance/CHRONOLOGY.md` - Phase 65
- Benchmark: `cargo test -p rource-wasm bench_label_placer_reset --release -- --nocapture`
- Measured: 198ns reset time

---

*ADR created: 2025-01-20*
*Last reviewed: 2026-01-26*
