# Production Telemetry Guide

**Version**: 1.0
**Last Updated**: 2026-01-27

This document describes the telemetry infrastructure for Rource, including performance metrics, error tracking, and tracing spans.

---

## Overview

Rource provides comprehensive telemetry for monitoring and debugging:

| Component | Purpose | Location |
|-----------|---------|----------|
| **Performance Metrics** | FPS, frame time, entity counts | `rource-wasm/src/metrics.rs` |
| **Error Tracking** | Categorized error counting and rates | `rource-wasm/src/metrics.rs` |
| **Frame Profiler** | Phase-level timing breakdown | `rource-wasm/src/profiler.rs` |
| **Tracing Spans** | Function-level execution tracing | `rource-wasm/src/render_phases/` |

---

## Performance Metrics

### Metrics Collected

| Metric | Type | Description |
|--------|------|-------------|
| `fps` | Gauge | Current frames per second |
| `fps_uncapped` | Gauge | FPS without frame limiting |
| `frame_time_ms` | Histogram | Time per frame in milliseconds |
| `uptime_seconds` | Counter | Total seconds since start |
| `visible_files` | Gauge | Files currently on screen |
| `visible_users` | Gauge | Users currently on screen |
| `visible_dirs` | Gauge | Directories currently on screen |
| `draw_calls` | Counter | GPU draw calls per frame |
| `total_entities` | Gauge | Total entities in scene |

### JavaScript API

```javascript
// Get current performance metrics
const metrics = JSON.parse(rource.getFrameStats());
console.log(`FPS: ${metrics.fps.toFixed(1)}`);
console.log(`Frame time: ${metrics.avgFrameTimeMs.toFixed(2)}ms`);
console.log(`Visible files: ${metrics.visibleFiles}`);

// Get render statistics
const stats = JSON.parse(rource.getRenderStats());
console.log(`Draw calls: ${stats.drawCalls}`);
console.log(`Culled entities: ${stats.culledCount}`);
```

### Browser Performance API Integration

When the `profiling` feature is enabled, Rource creates Performance marks/measures visible in Chrome DevTools:

```javascript
// In Chrome DevTools Performance tab, look for:
// - rource:frame_start / rource:frame_end
// - rource:scene_update_start / rource:scene_update_end
// - rource:render_start / rource:render_end
```

---

## Error Tracking

### Error Categories

| Category | SLO Target | Description |
|----------|------------|-------------|
| `Parse` | < 0.5% | VCS log parsing errors |
| `Render` | < 0.1% | Rendering pipeline errors |
| `WebGL` | < 0.1% | WebGL/WebGPU context errors |
| `Config` | < 0.01% | Configuration validation errors |
| `Asset` | < 0.1% | Font/texture loading errors |
| `Io` | < 0.2% | File/network I/O errors |

### JavaScript API

```javascript
// Record an error
rource.recordError('render', 'WebGL context lost');

// Get error counts by category
const errors = JSON.parse(rource.getErrorCounts());
console.log(`Parse errors: ${errors.parse}`);
console.log(`Render errors: ${errors.render}`);

// Get error rate
const rate = rource.getErrorRate();
console.log(`Total error rate: ${(rate * 100).toFixed(2)}%`);

// Check if under SLO threshold
const healthy = rource.isErrorRateHealthy();
console.log(`System healthy: ${healthy}`);

// Reset error counters
rource.resetErrors();
```

### Alerting Thresholds

| Severity | Threshold | Action |
|----------|-----------|--------|
| Warning | > 0.5% total | Log to console |
| Error | > 1% total | Show user notification |
| Critical | > 5% total | Pause playback, show recovery dialog |

---

## Frame Profiler

### Phase Breakdown

The frame profiler tracks time spent in each rendering phase:

| Phase | Description |
|-------|-------------|
| `scene_update` | Commit processing, physics simulation |
| `render` | Draw call submission |
| `gpu_wait` | Time waiting for GPU (WebGPU only) |
| `effects` | Post-processing (bloom, shadows) |

### JavaScript API

```javascript
// Get detailed frame statistics
const frameStats = JSON.parse(rource.getDetailedFrameStats());

console.log('Current frame:');
console.log(`  Scene update: ${frameStats.sceneUpdateMs.toFixed(2)}ms`);
console.log(`  Render: ${frameStats.renderMs.toFixed(2)}ms`);
console.log(`  GPU wait: ${frameStats.gpuWaitMs.toFixed(2)}ms`);
console.log(`  Effects: ${frameStats.effectsMs.toFixed(2)}ms`);
console.log(`  Total: ${frameStats.totalMs.toFixed(2)}ms`);

console.log('Rolling average (60 frames):');
console.log(`  Scene update: ${frameStats.avgSceneUpdateMs.toFixed(2)}ms`);
console.log(`  Render: ${frameStats.avgRenderMs.toFixed(2)}ms`);
console.log(`  Total: ${frameStats.avgTotalMs.toFixed(2)}ms`);

console.log(`WASM heap: ${(frameStats.wasmHeapBytes / 1024 / 1024).toFixed(1)}MB`);
```

---

## Tracing Spans

### Enabling Tracing

Build with the `tracing` feature flag:

```bash
# WASM build with tracing
cd rource-wasm
wasm-pack build --target web --release -- --features tracing

# Or during development
wasm-pack build --target web --dev -- --features tracing
```

### Instrumented Functions

When tracing is enabled, the following functions emit spans:

| Function | Span Name | Fields |
|----------|-----------|--------|
| `render_directories` | `render_directories` | `count` |
| `render_directory_labels` | `render_directory_labels` | - |
| `render_files` | `render_files` | `count` |
| `render_actions` | `render_actions` | - |
| `render_users` | `render_users` | `count` |
| `render_user_labels` | `render_user_labels` | - |
| `render_file_labels` | `render_file_labels` | - |

### Viewing Traces

Traces are output to the browser console when `tracing` feature is enabled:

```
[INFO  rource_wasm::render_phases] render_directories: count=1234
[INFO  rource_wasm::render_phases] render_files: count=5678
[INFO  rource_wasm::render_phases] render_users: count=56
```

---

## Memory Monitoring

### WASM Heap Statistics

```javascript
// Get WASM memory usage
const stats = JSON.parse(rource.getDetailedFrameStats());
const heapMB = stats.wasmHeapBytes / 1024 / 1024;
console.log(`WASM heap: ${heapMB.toFixed(1)}MB`);

// Monitor for memory leaks (heap should stabilize after warmup)
setInterval(() => {
    const stats = JSON.parse(rource.getDetailedFrameStats());
    const heapMB = stats.wasmHeapBytes / 1024 / 1024;
    if (heapMB > 500) {
        console.warn('High memory usage detected:', heapMB, 'MB');
    }
}, 10000);
```

### Memory Budgets

| Component | Budget | Description |
|-----------|--------|-------------|
| WASM heap | 256MB typical | Grows with repository size |
| Texture cache | 64MB | Avatar and font textures |
| Geometry buffers | 32MB | Vertex/index buffers |

---

## Performance Overlay

The built-in performance overlay shows real-time metrics:

```javascript
// Toggle performance overlay
document.addEventListener('keydown', (e) => {
    if (e.key === 'p') {
        const overlay = document.getElementById('perfOverlay');
        overlay.classList.toggle('hidden');
    }
});
```

### Overlay Metrics

- **FPS**: Current and 60-frame average
- **Frame time**: Current and average in milliseconds
- **Entity counts**: Files, users, directories visible
- **Memory**: WASM heap usage

---

## Integration with Browser DevTools

### Chrome DevTools Performance Tab

1. Open DevTools (F12)
2. Go to Performance tab
3. Click Record
4. Interact with visualization
5. Click Stop
6. Look for `rource:*` markers in the timeline

### Performance Marks (with `profiling` feature)

```
rource:frame_start → rource:frame_end
rource:scene_update → rource:scene_update_end
rource:render → rource:render_end
```

### Memory Tab

Monitor WASM memory growth:
1. Go to Memory tab
2. Take heap snapshot
3. Interact with visualization
4. Take another snapshot
5. Compare for retained objects

---

## Best Practices

### 1. Performance Monitoring

```javascript
// Monitor for frame drops
let lastFps = 60;
setInterval(() => {
    const metrics = JSON.parse(rource.getFrameStats());
    if (metrics.fps < 30 && lastFps >= 30) {
        console.warn('FPS dropped below 30:', metrics.fps);
    }
    lastFps = metrics.fps;
}, 1000);
```

### 2. Error Handling

```javascript
// Check health before critical operations
if (!rource.isErrorRateHealthy()) {
    console.error('High error rate detected, consider pausing');
}
```

### 3. Memory Leaks

```javascript
// Track memory over time
const memoryHistory = [];
setInterval(() => {
    const stats = JSON.parse(rource.getDetailedFrameStats());
    memoryHistory.push(stats.wasmHeapBytes);

    // Check for continuous growth (leak indicator)
    if (memoryHistory.length > 60) {
        const growth = memoryHistory[59] - memoryHistory[0];
        if (growth > 50 * 1024 * 1024) { // 50MB growth in 10 min
            console.warn('Possible memory leak detected');
        }
        memoryHistory.shift();
    }
}, 10000);
```

---

## SLO Targets

| Metric | Target | Measurement |
|--------|--------|-------------|
| FPS | ≥ 30 | P95 over 5 minutes |
| Frame time | ≤ 33ms | P99 over 5 minutes |
| Error rate | < 0.1% | Rolling 1-hour window |
| Memory growth | < 5% | After 30-minute session |
| Parse latency | < 100ms | P99 for 10k commits |

See `docs/operations/SLO.md` for complete SLO definitions.

---

## Troubleshooting

### High Frame Time

1. Check `scene_update_ms` vs `render_ms` to identify bottleneck
2. If scene_update high: reduce `seconds_per_day`, enable LOD
3. If render high: check entity counts, reduce quality settings

### Memory Growth

1. Check for context lost events (WebGL recreation)
2. Monitor label placer allocations
3. Verify texture cache isn't growing unbounded

### Errors Increasing

1. Check error category to identify source
2. Review browser console for stack traces
3. Check `docs/operations/RUNBOOK.md` for recovery procedures

---

*Last Updated: 2026-01-27*
