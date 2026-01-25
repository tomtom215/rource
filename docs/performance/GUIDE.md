# Performance Guide

This document covers general performance characteristics, profiling tools, and configuration
options for Rource. For the detailed optimization history, see the
[performance documentation](./performance/README.md).

---

## Table of Contents

1. [Performance Targets](#performance-targets)
2. [Profiling Quick Reference](#profiling-quick-reference)
3. [Memory Optimization](#memory-optimization)
4. [Rendering Optimization](#rendering-optimization)
5. [Physics Optimization](#physics-optimization)
6. [Parse Optimization](#parse-optimization)
7. [Configuration for Performance](#configuration-for-performance)
8. [Performance Checklist](#performance-checklist)

---

## Performance Targets

| Scenario               | Target            | Achieved |
|------------------------|-------------------|----------|
| 1k files, 60 FPS       | Native + WASM     | Yes      |
| 10k files, 60 FPS      | Native            | Yes      |
| 10k files, 30 FPS      | WASM (WebGL2)     | Yes      |
| 100k commits, <1s parse| Native            | Yes      |
| Memory < 50MB          | 100k commits      | Yes (16MB)|

---

## Profiling Quick Reference

For detailed profiling instructions, see [PROFILING.md](./PROFILING.md).

### Native

```bash
# CPU profiling with flamegraph
cargo flamegraph -- --headless --output /tmp/frames .

# Memory profiling
valgrind --tool=massif ./target/release/rource .

# Debug build with timing
RUST_LOG=debug cargo run --release -- .
```

### WASM

```javascript
// Browser Performance API
const start = performance.now();
rource.frame(timestamp);
console.log(`Frame time: ${performance.now() - start}ms`);

// Built-in metrics
console.log(`FPS: ${rource.getFps()}`);
console.log(`Frame time: ${rource.getFrameTimeMs()}ms`);
console.log(`Visible files: ${rource.getVisibleFiles()}`);
console.log(`Draw calls: ${rource.getDrawCalls()}`);
```

---

## Memory Optimization

### String Interning

Repeated strings are deduplicated using interning:

```rust
// Before: Each commit stores full author name
struct Commit {
    author: String,  // "John Doe" repeated 1000x = 9KB
}

// After: Interned handle (4 bytes)
struct CompactCommit {
    author: StringId,  // Index into interned strings
}
```

**Benchmark (Home Assistant Core)**:
- 103,533 commits
- 4,776 unique authors
- Deduplication ratio: **22x**

### Path Segment Interning

File paths are split and deduplicated at the segment level:

```
src/lib.rs     →  ["src", "lib.rs"]
src/main.rs    →  ["src", "main.rs"]
tests/lib.rs   →  ["tests", "lib.rs"]

Unique segments: 4 ("src", "tests", "lib.rs", "main.rs")
vs storing 3 full paths
```

**Benchmark**:
- 62,012 unique file paths
- 10,248 unique segments
- Reuse factor: **6x**

### Compact Commit Storage

```rust
// Standard (72+ bytes)
struct Commit {
    hash: String,              // 24 bytes
    timestamp: i64,            // 8 bytes
    author: String,            // 24 bytes
    files: Vec<FileChange>,    // 24 bytes + heap
}

// Compact (24 bytes)
struct CompactCommit {
    timestamp: i32,            // 4 bytes
    author: u32,               // 4 bytes (interned)
    hash: [u8; 7],             // 7 bytes (truncated)
    file_start: u32,           // 4 bytes
    file_count: u16,           // 2 bytes
    _padding: [u8; 3],         // 3 bytes
}
```

**Total Memory Savings**: 68% (51.65 MB → 16.43 MB for 100k commits)

---

## Rendering Optimization

### Frustum Culling

Only entities within the camera's visible bounds are processed:

```rust
// O(log n) spatial query instead of O(n) iteration
let visible_bounds = camera.visible_bounds();
let visible_entities = scene.quadtree.query(visible_bounds);
```

**Impact**: 10x speedup when zoomed into small area of large repo

### Instanced Rendering (WebGL2)

All primitives of the same type are batched into single draw calls:

```
Before (immediate mode):
  for each circle:
    gl.bindBuffer(...)
    gl.drawArrays(...)
  // 10,000 circles = 10,000 draw calls

After (instanced):
  gl.bufferData(all_circles)
  gl.drawArraysInstanced(...)
  // 10,000 circles = 1 draw call
```

**Impact**: Draw calls reduced from O(n) to O(1) per primitive type

### LOD (Level of Detail)

LOD culling skips sub-pixel entities for massive performance gains at low zoom levels:

| Constant                       | Value   | Purpose                       |
|--------------------------------|---------|-------------------------------|
| `LOD_MIN_FILE_RADIUS`          | 0.5px   | Skip files smaller than this  |
| `LOD_MIN_DIR_RADIUS`           | 0.3px   | Skip directories smaller      |
| `LOD_MIN_FILE_LABEL_RADIUS`    | 3.0px   | Skip file labels below this   |
| `LOD_MIN_DIR_LABEL_RADIUS`     | 4.0px   | Skip dir labels below this    |
| `LOD_MIN_USER_RADIUS`          | 1.0px   | Skip users smaller than this  |
| `LOD_MIN_USER_LABEL_RADIUS`    | 5.0px   | Skip user labels below this   |
| `LOD_MIN_ZOOM_FOR_FILE_BRANCHES`| 0.05   | Skip file branches below zoom |
| `LOD_MIN_ZOOM_FOR_DIR_BRANCHES` | 0.02   | Skip dir branches below zoom  |

**Impact at Scale**: At zoom=0.01 with 50,000 files, most entities are sub-pixel and skipped

---

## Physics Optimization

### Barnes-Hut Algorithm

Force calculation uses Barnes-Hut O(n log n) algorithm instead of O(n²) pairwise:

```rust
// Configuration
pub struct ForceConfig {
    pub use_barnes_hut: bool,       // Default: true
    pub barnes_hut_theta: f32,      // Default: 0.8
}
```

**Complexity Comparison**:

| Entity Count | O(n²)         | O(n log n)    | Speedup |
|--------------|---------------|---------------|---------|
| 100          | 10,000        | ~700          | 14x     |
| 1,000        | 1,000,000     | ~10,000       | 100x    |
| 10,000       | 100,000,000   | ~130,000      | 770x    |

### Spatial Hashing

For neighbor queries, spatial hashing provides O(1) average lookup:

```rust
// Build spatial hash (O(n))
let mut grid: HashMap<(i32, i32), Vec<EntityId>> = HashMap::new();
for entity in entities {
    let cell = (entity.pos.x as i32 / CELL_SIZE,
                entity.pos.y as i32 / CELL_SIZE);
    grid.entry(cell).or_default().push(entity.id);
}

// Query nearby entities (O(k) where k << n)
let nearby = get_neighbors(&grid, entity.pos, RADIUS);
```

---

## Parse Optimization

### Streaming Parser

For large repositories, streaming iteration avoids loading all commits into memory:

```rust
// Instead of: let commits = parser.parse_all(&log)?;

// Streaming approach:
let stream = GitLogStream::new(BufReader::new(file));
for commit in stream {
    store.add(commit?);  // Process incrementally
}
```

**Memory**: Constant regardless of log size

### Regex Compilation Caching

Filter patterns are compiled once and reused:

```rust
pub struct FilterSettings {
    show_users_pattern: Option<String>,
    #[serde(skip)]
    show_users_regex: OnceCell<Option<Regex>>,  // Lazily compiled
}
```

---

## Configuration for Performance

### Disable Expensive Effects

```bash
# CLI
rource --no-bloom --hide-filenames --hide-usernames .

# WASM
rource.setBloom(false);
rource.setShowLabels(false);
```

### Increase Playback Speed

```bash
# Faster = fewer frames per commit = smoother
rource --seconds-per-day 1.0 .
```

### Limit Entity Count

```bash
# Cap maximum entities
rource --max-files 1000 --max-users 50 .
```

### Use Headless Mode for Export

```bash
# No window overhead, maximum CPU utilization
rource --headless --output /tmp/frames .
```

---

## Performance Checklist

When experiencing slowness:

1. Check FPS counter (`rource.getFps()` or window title)
2. Verify using WebGL2 (`rource.getRendererType()`)
3. Check visible entity count (`rource.getVisibleFiles()`)
4. Disable bloom if enabled
5. Hide labels if zoomed out
6. Check for WebGL context loss
7. Profile with browser DevTools (WASM) or flamegraph (native)

---

## Related Documentation

- [Performance Optimization History](./performance/README.md) - 58 optimization phases
- [Algorithmic Complexity](./ALGORITHMIC_COMPLEXITY.md) - Big-O analysis
- [Profiling Guide](./PROFILING.md) - Detailed profiling tools
- [Rendering Architecture](./RENDERING.md) - Backend details

---

*Last updated: 2026-01-25*
