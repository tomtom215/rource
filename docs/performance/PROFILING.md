# Rource Profiling Guide

This guide covers all profiling tools and techniques for finding performance bottlenecks in Rource at the microsecond/nanosecond level.

## Quick Start

```bash
# Install all profiling tools
source scripts/setup-profilers.sh

# Check what's installed
source scripts/setup-profilers.sh --check

# Run quick benchmark
cargo bench --workspace -- --noplot
```

## Profiling Tool Matrix

### Native Profiling

| Tool | Type | Overhead | Precision | Best For | Platform |
|------|------|----------|-----------|----------|----------|
| perf | CPU | Low | High | General CPU profiling | Linux |
| cargo-flamegraph | CPU | Low | High | Quick flamegraph generation | Linux/macOS |
| samply | CPU | Low | High | Interactive analysis | Linux/macOS |
| Tracy | Multi | Low | Nanosec | Real-time tracing | All |
| DHAT | Memory | Medium | High | Allocation tracking | Linux |
| jemalloc-pprof | Memory | Very Low | High | Continuous profiling | Linux |
| Cachegrind | Cache | High | Very High | Cache miss analysis | Linux |
| iai-callgrind | Instructions | Medium | Very High | CI benchmarking | Linux |
| Hotspot | CPU (GUI) | Low | High | perf data visualization | Linux |
| Coz | CPU | Low | Medium | Causal profiling | Linux |

### WASM Profiling

| Tool | Type | Overhead | Precision | Best For | Platform |
|------|------|----------|-----------|----------|----------|
| Chrome DevTools | Multi | Low | ~5μs | General WASM profiling | All |
| Firefox Profiler | CPU | Low | ~5μs | WASM stack analysis | All |
| `--features profiling` | Phase | Minimal | ~5μs | Performance marks in DevTools | All |
| `--features tracing` | Tracing | Low | ~5μs | Console span logging | All |
| `getDetailedFrameStats()` | Stats | None | ~5μs | Phase breakdown, memory | All |
| Lighthouse | Web | Medium | N/A | Overall web performance | All |
| wasmtime jitdump | CPU | Low | High | Standalone WASM profiling | Linux |

## CPU Profiling

### cargo-flamegraph (Recommended for Quick Analysis)

Generates interactive SVG flamegraphs showing where CPU time is spent.

```bash
# Install
cargo install flamegraph

# Profile headless rendering (Linux - uses perf)
cargo flamegraph --profile profiling -- --headless --output /tmp/frames .

# Profile with specific benchmark
cargo flamegraph --profile profiling --bench scene_perf

# macOS (uses dtrace)
sudo cargo flamegraph --profile profiling -- --headless --output /tmp/frames .
```

Output: `flamegraph.svg` in current directory.

### samply (Interactive Analysis)

Samply captures profiling data and opens it in Firefox Profiler for interactive analysis.

```bash
# Install
cargo install samply

# Build with profiling symbols
cargo build --profile profiling

# Profile (opens browser automatically)
samply record ./target/profiling/rource --headless --output /tmp/frames .

# Profile specific benchmark
samply record cargo bench --bench scene_perf -- --profile-time 10
```

Features:
- Call tree visualization
- Timeline view
- Source code integration
- Marker events

### perf (Linux Hardware Counters)

Direct access to CPU performance counters for detailed analysis.

```bash
# Basic CPU profiling
perf record -g ./target/profiling/rource --headless --output /tmp/frames .
perf report

# Hardware counter analysis
perf stat -e cycles,instructions,cache-misses,branch-misses \
    ./target/profiling/rource --headless --output /tmp/frames .

# Generate flamegraph from perf data
perf script | stackcollapse-perf.pl | flamegraph.pl > perf-flamegraph.svg
```

### Hotspot (GUI Visualization)

GUI for viewing perf data with source code integration.

```bash
# Record data
perf record -g ./target/profiling/rource --headless --output /tmp/frames .

# Open in Hotspot
hotspot perf.data
```

## Memory Profiling

### DHAT (Detailed Heap Analysis)

DHAT tracks every heap allocation with full stack traces.

```bash
# Build with DHAT feature
cargo build --profile dhat --features dhat

# Run - produces dhat-heap.json on exit
./target/dhat/rource --headless --output /tmp/frames .

# View results in browser
# Open https://nnethercote.github.io/dh_view/dh_view.html
# Load dhat-heap.json
```

DHAT metrics:
- **Total bytes**: Total allocated over program lifetime
- **Max bytes**: Peak heap usage
- **Allocation sites**: Where allocations occur
- **Lifetimes**: How long allocations live

### jemalloc Profiling

Low-overhead continuous memory profiling.

```bash
# Build with jemalloc
cargo build --release --features jemalloc

# Enable profiling at runtime
MALLOC_CONF="prof:true,prof_prefix:jeprof.out" \
    ./target/release/rource --headless --output /tmp/frames .

# Analyze heap dump
jeprof --svg ./target/release/rource jeprof.out.*.heap > heap.svg
```

### Valgrind Massif (Heap Visualization)

```bash
valgrind --tool=massif ./target/profiling/rource --headless --output /tmp/frames .
ms_print massif.out.*
```

### heaptrack (Linux)

Real-time heap tracking with GUI.

```bash
heaptrack ./target/profiling/rource --headless --output /tmp/frames .
heaptrack_gui heaptrack.rource.*.zst
```

## Cache Profiling

### Cachegrind

Detailed cache simulation - find cache misses.

```bash
valgrind --tool=cachegrind ./target/profiling/rource --headless --output /tmp/frames .
cg_annotate cachegrind.out.*
```

Output includes:
- I-cache (instruction) read misses
- D-cache (data) read/write misses
- LL (last-level) cache misses

### Callgrind

Instruction-level profiling with call graph.

```bash
valgrind --tool=callgrind ./target/profiling/rource --headless --output /tmp/frames .
kcachegrind callgrind.out.*
```

## Deterministic Benchmarking

### iai-callgrind (CI-Ready)

Measures instruction counts - deterministic across runs, ideal for CI.

```bash
# Run all iai benchmarks
cargo bench --bench iai_scene

# Output shows instruction counts, not time
# Changes are detected as instruction count deltas
```

Example output:
```
bench_scene_update_100
  Instructions:     1,234,567 (No change)
  L1 Data Hits:     2,345,678 (-0.01%)
  L1 Data Misses:   12,345 (+0.02%)
```

### Criterion (Statistical)

Statistical benchmarks with regression detection.

```bash
# Run all Criterion benchmarks
cargo bench --workspace -- --noplot

# With HTML report
cargo bench --workspace

# Specific benchmark
cargo bench --bench scene_perf -- "scene_update"
```

## Real-Time Tracing

### Tracy Profiler

Nanosecond-precision real-time profiler with GPU support.

**Setup:**

1. Download Tracy from [releases](https://github.com/wolfpld/tracy/releases)
2. Build Rource with Tracy support:
   ```bash
   cargo build --profile profiling --features tracy
   ```
3. Start Tracy capture application
4. Run Rource - it will connect to Tracy automatically

**Features:**
- Frame timing analysis
- GPU queue visualization
- Memory allocation tracking
- Lock contention analysis
- Source code integration

**Adding Trace Points:**

```rust
#[cfg(feature = "tracy")]
use tracing::instrument;

#[cfg_attr(feature = "tracy", instrument(skip(self)))]
fn expensive_operation(&mut self) {
    // Code here will be traced
}
```

## WASM Profiling

The WASM demo is the primary production artifact. Profiling it requires different tools than native profiling.

### Built-in Profiling Features

The WASM build includes profiling infrastructure that integrates with browser DevTools.

**Feature Flags:**
- `profiling` - Adds Performance API marks/measures (shows in DevTools Performance tab)
- `tracing` - Routes Rust tracing spans to browser console

```bash
# Build WASM with profiling features
cd rource-wasm
wasm-pack build --target web --release --features profiling

# Build with tracing (more verbose, for debugging)
wasm-pack build --target web --release --features tracing

# Build with both
wasm-pack build --target web --release --features "profiling,tracing"
```

**Note:** Profiling features add ~5-10KB to WASM size but are invaluable for optimization.

### JavaScript Profiling API

The WASM module exposes detailed profiling statistics via JavaScript:

```javascript
// Check if profiling features are enabled
console.log('Profiling:', rource.isProfilingEnabled());
console.log('Tracing:', rource.isTracingEnabled());

// Get detailed frame statistics (JSON)
const stats = JSON.parse(rource.getDetailedFrameStats());

// Phase breakdown (current frame, in milliseconds)
console.log(`Scene Update: ${stats.sceneUpdateMs.toFixed(2)}ms`);
console.log(`Render: ${stats.renderMs.toFixed(2)}ms`);
console.log(`GPU Wait: ${stats.gpuWaitMs.toFixed(2)}ms`);
console.log(`Effects: ${stats.effectsMs.toFixed(2)}ms`);
console.log(`Total: ${stats.totalMs.toFixed(2)}ms`);

// Rolling averages (60-frame window)
console.log(`Avg Scene Update: ${stats.avgSceneUpdateMs.toFixed(2)}ms`);
console.log(`Avg Render: ${stats.avgRenderMs.toFixed(2)}ms`);
console.log(`Avg Total: ${stats.avgTotalMs.toFixed(2)}ms`);

// Memory usage
console.log(`WASM Heap: ${(stats.wasmHeapBytes / 1024 / 1024).toFixed(1)}MB`);
console.log(`Frame Count: ${stats.frameCount}`);
```

**Creating a Performance Monitor:**
```javascript
function logPerformance() {
    const stats = JSON.parse(rource.getDetailedFrameStats());

    // Identify bottleneck
    const phases = [
        { name: 'Scene', time: stats.avgSceneUpdateMs },
        { name: 'Render', time: stats.avgRenderMs },
        { name: 'GPU Wait', time: stats.avgGpuWaitMs },
        { name: 'Effects', time: stats.avgEffectsMs }
    ];

    const bottleneck = phases.reduce((a, b) => a.time > b.time ? a : b);
    console.log(`Bottleneck: ${bottleneck.name} (${bottleneck.time.toFixed(2)}ms)`);

    // Frame budget (16.67ms for 60fps)
    const budget = 16.67;
    const usage = (stats.avgTotalMs / budget * 100).toFixed(1);
    console.log(`Frame budget usage: ${usage}%`);
}

// Call periodically
setInterval(logPerformance, 5000);
```

### Chrome DevTools Performance Tab

When built with `--features profiling`, Performance marks appear in DevTools:

**Using Performance Marks:**
1. Build with `--features profiling`
2. Open demo in Chrome
3. Open DevTools (F12) → Performance tab
4. Click Record, interact with demo, Stop
5. Look for "rource:*" markers in the timeline:
   - `rource:frame` - Total frame time
   - `rource:scene_update` - Physics and commit processing
   - `rource:render` - Draw calls

**Reading the Timeline:**
- Wide marks = slow phases (optimization targets)
- Consistent width = stable performance
- Growing width = regression or memory leak

**Zoom Levels:**
- 100ms view: Frame-level patterns
- 1ms view: Phase-level detail
- 0.1ms view: Individual operations

### Chrome DevTools Memory Tab

For WASM memory analysis:

1. Go to Memory tab
2. Select "Heap snapshot"
3. Take snapshot before/after operations
4. Compare snapshots for growth

**WASM Memory Patterns to Watch:**
- Growing ArrayBuffer allocations (texture uploads)
- Detached DOM references (canvas recreation)
- Unreleased typed arrays (render buffers)

### Firefox Profiler

Better WASM stack support than Chrome:

1. Open `about:profiling`
2. Set preset to "Web Developer"
3. Enable "Stack walk native frames"
4. Start recording, use demo, stop
5. Analyze - WASM function names are preserved

### Browser Performance APIs

For custom instrumentation:

```javascript
// Using Performance API directly
performance.mark('my-operation-start');
// ... operation ...
performance.mark('my-operation-end');
performance.measure('my-operation', 'my-operation-start', 'my-operation-end');

// Get all measures
const measures = performance.getEntriesByType('measure');
console.log(measures.map(m => `${m.name}: ${m.duration.toFixed(2)}ms`));

// Long Animation Frame API (Chrome 123+)
new PerformanceObserver((list) => {
    for (const entry of list.getEntries()) {
        if (entry.duration > 50) {
            console.warn('Long frame:', entry.duration);
        }
    }
}).observe({ type: 'long-animation-frame', buffered: true });
```

### WebGPU Profiling

When using the wgpu backend (WebGPU):

**Chrome DevTools:**
1. Go to `chrome://flags`
2. Enable "WebGPU Developer Features"
3. DevTools → More Tools → WebGPU Inspector (experimental)

**GPU Timing Queries:**
```javascript
// Check if timestamp queries are supported
const adapter = await navigator.gpu.requestAdapter();
const features = adapter.features;
console.log('Timestamp queries:', features.has('timestamp-query'));
```

### wasmtime Profiling (Standalone)

For profiling WASM outside the browser:

```bash
# Install wasmtime
curl https://wasmtime.dev/install.sh -sSf | bash

# Profile with perf support
wasmtime run --profile=perfmap ./target/wasm32-unknown-unknown/release/rource_wasm.wasm

# Then use perf as normal
perf record -g wasmtime run ...
perf report
```

### Lighthouse Audit

For overall web performance:

```bash
# Install and run
npx lighthouse http://localhost:8080 --output html --output-path lighthouse.html

# Key metrics for WASM apps:
# - First Contentful Paint: Time to first frame
# - Time to Interactive: Time until responsive
# - Total Blocking Time: Main thread blocking
# - Largest Contentful Paint: Full render time
```

### Network Profiling

WASM download and initialization:

```javascript
// Measure WASM load time
const startTime = performance.now();
const rource = await Rource.create(canvas);
const loadTime = performance.now() - startTime;
console.log(`WASM load time: ${loadTime.toFixed(0)}ms`);
```

**Network Tab Analysis:**
1. Open DevTools → Network tab
2. Reload page
3. Look for `.wasm` file
4. Check:
   - Transfer size (gzipped)
   - Content size (uncompressed)
   - Time to download
   - Time to compile (look for "Compile" in waterfall)

### WASM Profiling Checklist

```markdown
- [ ] Build with `--features profiling` for detailed marks
- [ ] Check `getDetailedFrameStats()` for phase breakdown
- [ ] Record Performance timeline during stress test
- [ ] Identify bottleneck phase (scene_update vs render)
- [ ] Check WASM heap size for memory leaks
- [ ] Run Lighthouse for overall web metrics
- [ ] Test with large repository (Home Assistant Core)
- [ ] Compare WebGPU vs WebGL2 vs Software renderer performance
```

## GPU Profiling

### wgpu Tracing (Built-in)

wgpu includes built-in tracing for GPU operations.

```rust
// Enable wgpu tracing via environment
std::env::set_var("WGPU_TRACE", "/tmp/wgpu-trace");
```

### Chrome GPU Debugging

For WebGPU in Chrome:
1. Navigate to `chrome://gpu`
2. Check GPU feature status
3. Use Chrome DevTools → Rendering tab for GPU timing

### RenderDoc (Native)

For native GPU profiling:

1. Install RenderDoc
2. Launch Rource through RenderDoc
3. Capture frame
4. Analyze draw calls, GPU timings

## Stress Testing with Home Assistant Core

The Home Assistant Core repository (103K+ commits, 533K+ file changes) is the standard stress test.

```bash
# Clone if not present
git clone https://github.com/home-assistant/core.git /tmp/ha-core

# Generate git log
cd /tmp/ha-core
git log --pretty=format:"%H|%an|%at" --numstat > /tmp/ha-core.log

# Profile with this large dataset
# Note: Rource takes the repository path as a positional argument, not --git-log
cargo flamegraph --profile profiling -- \
    --headless \
    --output /tmp/frames \
    --seconds-per-day 0.01 \
    /tmp/ha-core

# Memory profile
cargo build --profile dhat --features dhat
./target/dhat/rource --headless --output /tmp/frames /tmp/ha-core
```

## Profile-Guided Optimization (PGO)

Build with PGO for maximum performance:

```bash
# Step 1: Build instrumented binary
RUSTFLAGS="-Cprofile-generate=/tmp/pgo-data" cargo build --release

# Step 2: Run workloads to generate profile data
./target/release/rource --headless --output /tmp/frames .
./target/release/rource --headless --output /tmp/frames /path/to/large/repo

# Step 3: Merge profile data
llvm-profdata merge -o /tmp/pgo-data/merged.profdata /tmp/pgo-data

# Step 4: Build optimized binary
RUSTFLAGS="-Cprofile-use=/tmp/pgo-data/merged.profdata" cargo build --release
```

## Quick Reference: Common Commands

```bash
# CPU flamegraph (quick)
cargo flamegraph --profile profiling -- --headless --output /tmp/frames .

# Interactive CPU profiling
samply record ./target/profiling/rource --headless --output /tmp/frames .

# Memory allocation tracking
cargo build --profile dhat --features dhat
./target/dhat/rource --headless --output /tmp/frames .

# Cache miss analysis
valgrind --tool=cachegrind ./target/profiling/rource --headless --output /tmp/frames .

# Deterministic benchmarks (CI)
cargo bench --bench iai_scene

# Command-line benchmark
hyperfine --warmup 3 './target/release/rource --headless --output /tmp/frames .'

# Real-time tracing
cargo build --profile profiling --features tracy
# Start Tracy, then run binary

# WASM in browser
# Chrome DevTools → Performance tab → Record

# Stress test
./benchmarks/scripts/run_benchmarks.sh
```

## Interpreting Results

### Identifying Hot Spots

In flamegraphs, look for:
- **Wide bars**: Functions taking most time
- **Tall stacks**: Deep call chains (potential for inlining)
- **Repeated patterns**: Loop bodies that could be optimized

### Memory Optimization Targets

From DHAT output, prioritize:
1. **High "Total bytes"**: Allocations that happen frequently
2. **Low "Max bytes" with high "Total"**: Short-lived allocations (potential for pooling)
3. **Duplicate allocations**: Same stack trace appearing multiple times

### Cache Optimization

From Cachegrind:
- **High D1mr (L1 data read misses)**: Consider data layout changes
- **High LLmr (Last-level misses)**: Working set too large, need algorithmic changes

### Instruction Count Changes

From iai-callgrind:
- **>5% instruction increase**: Investigate regression
- **Cache miss increase**: Check data access patterns
- **Branch misprediction increase**: Check conditional logic

## Performance Targets

| Metric | Target | Measured |
|--------|--------|----------|
| Frame time (1000 files) | < 16.6ms (60 FPS) | TBD |
| Frame time (10000 files) | < 33.3ms (30 FPS) | TBD |
| Peak memory (10000 files) | < 500MB | TBD |
| WASM load time | < 1s | TBD |
| Log parsing (100K commits) | < 2s | TBD |

## Continuous Integration

iai-callgrind benchmarks are integrated into CI:

```yaml
# .github/workflows/bench.yml
- name: Run iai benchmarks
  run: cargo bench --bench iai_scene -- --save-baseline ci
```

Regressions trigger alerts when instruction counts increase >5%.

## Further Reading

- [The Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [DHAT Manual](https://valgrind.org/docs/manual/dh-manual.html)
- [Tracy Manual](https://github.com/wolfpld/tracy/releases)
- [Criterion.rs Book](https://bheisler.github.io/criterion.rs/book/)
- [Firefox Profiler Docs](https://profiler.firefox.com/docs/)
