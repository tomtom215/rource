# Rource Performance Guide

This document covers performance characteristics, optimization techniques, and benchmarks for Rource.

## Performance Targets

| Scenario | Target | Achieved |
|----------|--------|----------|
| 1k files, 60 FPS | Native + WASM | Yes |
| 10k files, 60 FPS | Native | Yes |
| 10k files, 30 FPS | WASM (WebGL2) | Yes |
| 100k commits, <1s parse | Native | Yes |
| Memory < 50MB | 100k commits | Yes (16MB) |

## Profiling Tools

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

## Memory Optimization

### String Interning

Repeated strings are deduplicated using interning:

```rust
// Before: Each commit stores full author name
struct Commit {
    author: String,  // "John Doe" repeated 1000x = 9KB
    // ...
}

// After: Interned handle (4 bytes)
struct CompactCommit {
    author: StringId,  // Index into interned strings
    // ...
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

Unique segments: 3 ("src", "tests", "lib.rs", "main.rs")
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
    hash: String,              // 24 bytes (ptr + len + cap)
    timestamp: i64,            // 8 bytes
    author: String,            // 24 bytes
    files: Vec<FileChange>,    // 24 bytes + heap
}

// Compact (24 bytes)
struct CompactCommit {
    timestamp: i32,            // 4 bytes (seconds since epoch)
    author: u32,               // 4 bytes (interned)
    hash: [u8; 7],             // 7 bytes (truncated)
    file_start: u32,           // 4 bytes (index into file array)
    file_count: u16,           // 2 bytes
    _padding: [u8; 3],         // 3 bytes alignment
}
```

**Total Memory Savings**: 68% (51.65 MB → 16.43 MB for 100k commits)

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

### Deferred Label Rendering

Labels are expensive (many quads per character). We defer them:

```rust
// Collect label requests
let mut labels: Vec<LabelRequest> = vec![];

// During entity rendering, just record requests
if should_show_label(entity) {
    labels.push(LabelRequest { text, pos, size });
}

// Batch render all labels at once
for label in labels {
    renderer.draw_text(&label.text, label.pos, label.size);
}
```

### LOD (Level of Detail) - Planned

When zoomed out, we could:
1. Skip labels entirely (zoom < 0.3)
2. Combine nearby files into clusters (zoom < 0.1)
3. Simplify tree branches to single lines (zoom < 0.05)

## Physics Optimization

### Spatial Hashing

Repulsion force calculation is O(n²) naively. We use spatial hashing:

```rust
// Build spatial hash (O(n))
let mut grid: HashMap<(i32, i32), Vec<EntityId>> = HashMap::new();
for entity in entities {
    let cell = (entity.pos.x as i32 / CELL_SIZE, entity.pos.y as i32 / CELL_SIZE);
    grid.entry(cell).or_default().push(entity.id);
}

// Query nearby entities (O(k) where k << n)
for entity in entities {
    let nearby = get_neighbors(&grid, entity.pos, RADIUS);
    for other in nearby {
        apply_repulsion(entity, other);
    }
}
```

**Complexity**: O(n) average case vs O(n²) brute force

### Damping for Stability

Physics simulation uses damping to prevent oscillation:

```rust
const DAMPING: f32 = 0.95;  // Per-frame velocity retention

fn update_physics(&mut self, dt: f32) {
    self.position += self.velocity * dt;
    self.velocity *= DAMPING;  // Exponential decay
}
```

### Adaptive Time Step

Large dt values can cause instability. We clamp:

```rust
let dt = (timestamp - last_time).min(0.1);  // Max 100ms
```

## Parse Optimization

### Streaming Parser

For large repositories, we use streaming iteration:

```rust
// Instead of: let commits = parser.parse_all(&log)?;  // Load all into memory

// We do:
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

impl FilterSettings {
    pub fn show_users_regex(&self) -> Option<&Regex> {
        self.show_users_regex.get_or_init(|| {
            self.show_users_pattern.as_ref()
                .and_then(|p| Regex::new(p).ok())
        }).as_ref()
    }
}
```

## Benchmark Results

### Commit Parsing

| Repository | Commits | Parse Time | Memory |
|------------|---------|------------|--------|
| Small (1k commits) | 1,000 | 15ms | 0.5 MB |
| Medium (10k commits) | 10,000 | 80ms | 2.5 MB |
| Large (100k commits) | 103,533 | 650ms | 16 MB |

### Rendering (1920x1080)

| Scenario | Software FPS | WebGL2 FPS |
|----------|--------------|------------|
| 100 files | 120+ | 500+ |
| 1,000 files | 60 | 300+ |
| 10,000 files | 25 | 60+ |

### WASM Bundle Size

| Build | Size (gzip) |
|-------|-------------|
| Debug | 2.1 MB |
| Release | 412 KB |
| Release + wasm-opt | 76 KB |

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

## Performance Checklist

When experiencing slowness:

1. [ ] Check FPS counter (`rource.getFps()` or window title)
2. [ ] Verify using WebGL2 (`rource.getRendererType()`)
3. [ ] Check visible entity count (`rource.getVisibleFiles()`)
4. [ ] Disable bloom if enabled
5. [ ] Hide labels if zoomed out
6. [ ] Check for WebGL context loss
7. [ ] Profile with browser DevTools (WASM) or flamegraph (native)

## Future Optimizations

1. **GPU Physics**: Compute shaders for force calculations
2. **Worker Threads**: Off-main-thread physics (WASM)
3. **Incremental Layout**: Only recalculate changed subtrees
4. **Texture Atlas**: Batch all images into single texture
5. **WebGPU**: Modern GPU API when widely available
