# Rource Performance Benchmark Report

**Repository:** Home Assistant Core
**Commits:** 103,871 (86,742 processed)
**File Changes:** 524,869
**Unique Users:** 4,786
**Directories:** 4,836
**Date:** 2026-01-24

---

## Executive Summary

Benchmarking rource with one of the largest open-source repositories (Home Assistant Core) reveals that the **software renderer** achieves **5-6 FPS at 1080p** for extreme-scale visualizations with **35,000+ files** visible simultaneously. The primary bottlenecks are:

1. **Rendering (68-86%)**: Anti-aliased primitive drawing dominates
2. **Bloom Effects (21%)**: CPU-based post-processing
3. **Export (5-6%)**: Uncompressed PPM file writing
4. **Physics (4-5%)**: Barnes-Hut force-directed layout

---

## Benchmark Results

### Test Environment
- Platform: Linux 4.4.0
- Binary: rource 0.1.0 (release build with debug symbols)
- Renderer: Software (CPU-only)

### Benchmark 1: Full 1080p with Bloom

| Metric | Value |
|--------|-------|
| Resolution | 1920×1080 |
| Total Time | 52.31s |
| Frames | 271 |
| **FPS** | **5.2** |
| Avg Frame | 193.0ms |
| Min Frame | 51.8ms |
| Max Frame | 374.5ms |
| p50 | 163.0ms |
| p95 | 352.5ms |
| p99 | 363.4ms |

**Phase Breakdown:**
| Phase | Time | % | Per Frame |
|-------|------|---|-----------|
| Render | 35.65s | 68.1% | 131.5ms |
| Effects (Bloom) | 11.15s | 21.3% | 41.1ms |
| Export (PPM) | 2.67s | 5.1% | 9.9ms |
| Scene Update | 2.22s | 4.2% | 8.2ms |
| Commit Apply | 0.63s | 1.2% | 2.3ms |

### Benchmark 2: 1080p without Bloom

| Metric | Value | vs Bench 1 |
|--------|-------|------------|
| Resolution | 1920×1080 | - |
| Total Time | 41.88s | -20% |
| Frames | 271 | - |
| **FPS** | **6.5** | +25% |
| Avg Frame | 154.5ms | -20% |

**Bloom Impact:**
- Overhead: 10.44s (20% of total)
- Frame time reduction: 38.5ms
- FPS improvement: +1.3 (5.2 → 6.5)

### Benchmark 3: 360p without Bloom (Low Resolution)

| Metric | Value | vs 1080p |
|--------|-------|----------|
| Resolution | 640×360 | 9x fewer pixels |
| Total Time | 13.86s | -67% |
| Frames | 271 | - |
| **FPS** | **19.5** | +200% |
| Avg Frame | 51.1ms | -67% |

**Resolution Scaling Analysis:**
- Pixel ratio: 2,073,600 / 230,400 = 9.0x
- Render time ratio: 36.2s / 10.7s = 3.4x
- Indicates ~37% pixel-bound, ~63% entity-bound overhead

---

## Per-Entity Rendering Costs

Measured at Frame 200 with maximum entity count:

| Entity Type | Count | Total Time | Per Entity | Notes |
|-------------|-------|------------|------------|-------|
| Files | 35,441 | 170.48ms | **4.8µs** | draw_disc() |
| Users | 3,271 | 37.35ms | **11.4µs** | Avatar + label |
| Actions | 4,965 | 35.39ms | **7.1µs** | Beam lines |
| Directories | 3,285 | 34.39ms | **10.5µs** | Ring + label |
| Culling | - | 0.12ms | - | Quadtree query |

**Total visible entities at peak:** 46,962

---

## WASM Binary Analysis (twiggy)

**File Size:** 2.8 MB (uncompressed)

### Top Contributors by Size:
| Section | Size | % |
|---------|------|---|
| Data segment | 486 KB | 16.7% |
| Function table | 1.95 MB | 66.7% |
| Other code | ~500 KB | 16.6% |

### Dominator Tree:
- 66.7% of retained bytes from function table
- Deep call chains through rendering code
- Optimization opportunities in dead code elimination

---

## Identified Bottlenecks

### CRITICAL (>10ms/frame)

#### 1. draw_disc() - Files Rendering
```
35,441 files × 4.8µs = 170ms/frame
```
- Anti-aliased disc drawing with per-pixel sqrt()
- Already optimized in Phase 27 to skip sqrt() for inner pixels
- **Further optimization:** GPU instancing for identical discs

#### 2. Text Rendering (Labels)
- Font rasterization via fontdue
- Glyph cache helps but still significant overhead
- ~3,000+ labels rendered per frame
- **Further optimization:** Pre-render common labels, GPU text

#### 3. draw_line() - Action Beams
```
4,965 actions × 7.1µs = 35ms/frame
```
- Xiaolin Wu anti-aliased line algorithm
- **Further optimization:** Reduce action display limit

### HIGH (1-10ms/frame)

#### 4. Bloom Post-Processing (when enabled)
```
41ms/frame (already optimized O(n) blur)
```
- 3-pass: bright extract → blur H → blur V
- Uses sliding window O(n) algorithm (Phase 27)
- **Further optimization:** GPU compute shaders

#### 5. PPM Export
```
10ms/frame for 1920×1080
```
- Uncompressed RGB file writing
- 6.2 MB per frame
- **Further optimization:** Async I/O, compression

### MEDIUM (<1ms/frame)

#### 6. Scene Update (Physics)
```
8.2ms/frame with Barnes-Hut O(n log n)
```
- Force-directed layout calculation
- Already uses Barnes-Hut tree approximation
- **Further optimization:** GPU physics dispatch

#### 7. Culling/Visibility
```
0.12ms/frame
```
- Efficient quadtree-based spatial query
- ✓ Well-optimized

#### 8. Commit Apply
```
2.3ms/frame
```
- ✓ Well-optimized, uses string interning

---

## CPU Cycle Analysis

### Estimated CPU Cycles per Frame (at 3 GHz)

| Operation | Time | Cycles | % |
|-----------|------|--------|---|
| draw_disc() | 170ms | 510M | 63% |
| draw_text() | ~40ms | 120M | 15% |
| draw_line() | 35ms | 105M | 13% |
| Physics | 8ms | 24M | 4% |
| Culling | 0.12ms | 0.4M | <1% |
| Other | ~20ms | 60M | 4% |

### Per-Pixel Costs (1920×1080 = 2.07M pixels)

| Operation | Cycles/pixel |
|-----------|--------------|
| Bloom blur pass | ~30 |
| Full frame composite | ~10 |
| Background clear | ~2 |

---

## Recommendations

### Immediate Impact (No Code Changes)

1. **Use GPU Backend (wgpu/WebGL2)**
   - 10-100x faster rendering via instancing
   - Already implemented in rource

2. **Disable Bloom for Large Repos**
   - 20% immediate improvement
   - `--no-bloom` flag

3. **Lower Resolution for Preview**
   - 360p: 3x faster than 1080p
   - Good for exploration, export at full res

### Code Optimizations

#### Priority 1: Batched Disc Rendering
```rust
// Current: individual draw calls
for file in files {
    draw_disc(file.pos, file.radius, file.color);
}

// Proposed: batched instance buffer
let instances: Vec<DiscInstance> = files.map(|f| DiscInstance {
    pos: f.pos,
    radius: f.radius,
    color: f.color,
}).collect();
draw_discs_batched(&instances);
```

#### Priority 2: Aggressive LOD
```rust
// Skip entities below 1 pixel when zoomed out
if entity.screen_radius < 1.0 {
    continue;
}
```

#### Priority 3: Action Limit
```rust
// Cap visible actions at 2000
const MAX_VISIBLE_ACTIONS: usize = 2000;
```

#### Priority 4: Parallel Export
```rust
// Write frames on separate thread
let (tx, rx) = channel();
thread::spawn(move || {
    while let Ok(frame) = rx.recv() {
        write_ppm(&frame);
    }
});
```

---

## Comparison with Original Gource

| Metric | Rource | Gource |
|--------|--------|--------|
| Max Files (smooth) | ~35k (5 FPS) | ~50k (GPU) |
| Memory (HA Core) | ~16 MB compact | ~50 MB+ |
| Binary Size | 3.9 MB | ~10 MB |
| WASM Size | 2.8 MB | N/A |
| GPU Required | No (optional) | Yes |

---

## Test Data Summary

**Home Assistant Core Repository:**
- History span: 2013-2026 (12+ years)
- Total commits: 103,871
- File changes: 524,869
- Unique contributors: 4,786
- Peak visible files: 35,441
- Peak visible users: 3,271
- Peak visible directories: 3,285

---

## Appendix: Raw Benchmark JSON

### Benchmark 1 (1080p + Bloom)
```json
{"frames":271,"total_ns":52314647483,"avg_frame_ns":193042979,"min_frame_ns":51836367,"max_frame_ns":374538835,"p50_frame_ns":162985388,"p95_frame_ns":352531263,"p99_frame_ns":363419150,"phases":{"commit_apply_ns":626671466,"scene_update_ns":2217355936,"render_ns":35646406434,"effects_ns":11148472767,"export_ns":2674588150},"commits_applied":86740,"scene":{"files":31575,"users":4786,"directories":4836}}
```

### Benchmark 2 (1080p No Bloom)
```json
{"frames":271,"total_ns":41876736969,"avg_frame_ns":154526704,"min_frame_ns":12080808,"max_frame_ns":353282031,"p50_frame_ns":118816597,"p95_frame_ns":323422759,"p99_frame_ns":343964771,"phases":{"commit_apply_ns":634173040,"scene_update_ns":2299616023,"render_ns":36210069310,"effects_ns":53469,"export_ns":2731643126},"commits_applied":86740,"scene":{"files":31575,"users":4786,"directories":4836}}
```

### Benchmark 3 (360p No Bloom)
```json
{"frames":271,"total_ns":13855396129,"avg_frame_ns":51126922,"min_frame_ns":2038575,"max_frame_ns":143077810,"p50_frame_ns":45857290,"p95_frame_ns":104515380,"p99_frame_ns":115790239,"phases":{"commit_apply_ns":586028545,"scene_update_ns":2145954299,"render_ns":10690070814,"effects_ns":45353,"export_ns":432082909},"commits_applied":86740,"scene":{"files":31575,"users":4786,"directories":4836}}
```

---

*Report generated: 2026-01-24*
