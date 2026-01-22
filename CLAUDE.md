# CLAUDE.md - Rource Project Guide

This document provides context and guidance for Claude (AI assistant) when working on the Rource project.

## Project Overview

**Rource** (Rust + Gource) is a complete rewrite of [Gource](https://github.com/acaudwell/Gource), the software version control visualization tool, in Rust with WebAssembly support.

### Goals
- **Portable**: Run on any CPU architecture without requiring a dedicated GPU
- **Lightweight**: Minimal dependencies, small binary size (~3.8MB native, ~235KB WASM gzip)
- **Fast**: Leverage Rust's performance and modern rendering techniques
- **User-friendly**: Better UI/UX than original Gource
- **Feature-complete**: Maintain at minimum feature parity with Gource

### Key Documents
- `README.md` - Project overview and usage instructions
- `CONTRIBUTING.md` - Development guidelines and code style
- `LICENSE` - GPL-3.0 license (same as original Gource)

## Session Setup

Before starting development, run the setup script to ensure all tools are installed:

```bash
source scripts/session-setup.sh
```

This script will:
1. Verify Rust and Cargo are installed
2. Install the `wasm32-unknown-unknown` target if missing
3. Install `wasm-pack` if missing
4. Ensure `clippy` and `rustfmt` are available

### Required Tools
| Tool | Version | Purpose |
|------|---------|---------|
| Rust | 1.76+ | Core language |
| Cargo | Latest | Package manager |
| wasm-pack | 0.12+ | WASM bundling |
| rustup | Latest | Toolchain management |

### Optional Tools
| Tool | Purpose |
|------|---------|
| wasm-opt | WASM binary optimization |
| cargo-watch | Auto-rebuild on changes |
| ffmpeg | Convert PPM frames to video |
| Python 3 | PPM file inspection scripts |

## Architecture

### Crate Structure

```
rource/
├── crates/
│   ├── rource-math/      # Math types (Vec2, Vec3, Vec4, Mat3, Mat4, Color, etc.) [144 tests]
│   ├── rource-vcs/       # VCS log parsing (Git, SVN, Custom format, compact storage) [150 tests]
│   ├── rource-core/      # Core engine (scene, physics, animation, camera, config) [261 tests]
│   └── rource-render/    # Rendering (software rasterizer, WebGL2, wgpu, bloom, shadows) [310 tests]
├── rource-cli/           # Native CLI application (winit + softbuffer) [95 tests]
└── rource-wasm/          # WebAssembly application [73 tests]
                          # Plus 61 integration/doc tests = 1,094 total
```

### Rendering Backends
1. **wgpu (Native + WASM)** - Cross-platform GPU rendering via WebGPU/Vulkan/Metal/DX12
2. **WebGL2 (WASM)** - GPU-accelerated browser rendering (fallback for older browsers)
3. **Software Rasterizer** - Pure CPU rendering, works everywhere (maximum compatibility)

**Backend Priority (recommended):**
- Native: wgpu → Software
- WASM: wgpu (WebGPU) → WebGL2 → Software (Canvas2D)

The WASM build automatically tries backends in priority order.
Check active renderer via `rource.getRendererType()`.

### IMPORTANT: CLI and WASM Rendering Synchronization

**The CLI and WASM have separate rendering code that must be kept in sync.**

| Component | Rendering Code Location |
|-----------|------------------------|
| Native CLI | `rource-cli/src/rendering.rs` |
| WASM | `rource-wasm/src/lib.rs` (the `render()` method and helper functions) |

When making visual/rendering changes (e.g., avatar styles, branch curves, glow effects, beam rendering):
1. Update `rource-cli/src/rendering.rs` for the native CLI
2. **Also update** `rource-wasm/src/lib.rs` with the same changes
3. Rebuild WASM with `./scripts/build-wasm.sh`
4. Test both CLI and WASM to verify visual parity

The rendering helper functions (spline interpolation, avatar drawing, beam effects, etc.) are duplicated
between CLI and WASM because they have different dependencies and build targets. Future refactoring
could extract these into a shared rendering utilities module in `rource-render`.

## Development Guidelines

### Code Style
- Use `cargo fmt` before committing
- Run `cargo clippy` and address warnings
- Follow Rust API guidelines: https://rust-lang.github.io/api-guidelines/

### Testing
```bash
# Run all tests
cargo test

# Run specific test
cargo test test_name

# Run tests with output
cargo test -- --nocapture

# Run tests for specific crate
cargo test -p rource-core
```

### Building

```bash
# Debug build (native)
cargo build

# Release build (native)
cargo build --release

# WASM build
wasm-pack build --target web --release

# WASM for Node.js
wasm-pack build --target nodejs --release
```

### Performance Considerations
- Use spatial hashing/quadtree for entity queries
- Batch rendering calls (instanced rendering)
- Implement LOD (Level of Detail) for zoomed-out views
- Stream commits for large repositories
- Use arena allocation for entities

## Feature Implementation Checklist

### Phase 1: Foundation
- [x] Math library (Vec2, Vec3, Vec4, Mat3, Mat4, Color, Rect, Bounds)
- [x] Configuration system (Settings struct with all options)
- [x] Core data structures (Entity IDs, Commit, FileChange)

### Phase 2: VCS Parsing
- [x] Git log parser
- [x] Custom format parser
- [x] SVN XML parser
- [x] VCS auto-detection

### Phase 3: Scene Graph
- [x] Directory tree (DirNode, DirTree)
- [x] File entities (FileNode)
- [x] User entities (User)
- [x] Action entities (Action, beams)
- [x] Quadtree spatial index
- [x] Scene struct with apply_commit()
- [x] Frustum culling for performance
- [x] Entity bounds calculation (compute_entity_bounds)

### Phase 4: Physics & Animation
- [x] Force-directed layout
- [x] Tweening system
- [x] Spline interpolation (Catmull-Rom)
- [x] Camera system

### Phase 5: Rendering
- [x] Software rasterizer (SoftwareRenderer with pixel buffer)
- [x] Anti-aliased lines (Xiaolin Wu's algorithm)
- [x] Anti-aliased circles and discs
- [x] Textured quad drawing
- [x] Font rendering (fontdue integration)
- [x] Bloom effect (CPU)
- [x] Shadow rendering (drop shadows)

### Phase 6: Platform Integration
- [x] Native CLI (winit + softbuffer)
- [x] Text overlays (title, date, commit info, usernames, filenames)
- [x] Mouse input (pan with drag, zoom with scroll wheel)
- [x] Video export (PPM frames for ffmpeg piping)
- [x] Headless rendering mode (batch export without window)
- [x] WASM/Canvas2D (software renderer + ImageData)
- [x] WASM/WebGL2 (GPU acceleration, with automatic fallback to software)
- [x] wgpu backend (cross-platform WebGPU/Vulkan/Metal/DX12 with GPU compute)

## Recent Progress & Insights

### Performance Optimizations (2026-01-21)

Implemented verified, production-grade performance optimizations for maintaining high FPS regardless of repository size:

#### 1. SIMD Enabled for WASM (+simd128)

Created `.cargo/config.toml` with SIMD feature flag:

```toml
[target.wasm32-unknown-unknown]
rustflags = ["-C", "target-feature=+simd128"]
```

**Expected Impact**: 2-6x faster for math-heavy operations (verified by V8 benchmarks).

**Browser Support**: Production-ready in Chrome (v91+), Firefox (v89+), Safari (v16.4+).

#### 2. wasm-opt Performance Flags (-O3)

Updated `scripts/build-wasm.sh` to use performance-optimized flags:

```bash
wasm-opt -O3 --converge --low-memory-unused \
    --enable-simd --enable-bulk-memory --enable-sign-ext \
    --enable-nontrapping-float-to-int --enable-mutable-globals
```

**Note**: Changed from `-Oz` (size optimization) to `-O3` (performance optimization).

#### 3. Level-of-Detail (LOD) System

Implemented LOD culling in both WASM and CLI renderers to skip sub-pixel entities:

**Configuration** (in `render_phases.rs` and `rendering.rs`):

| Constant | Value | Purpose |
|----------|-------|---------|
| `LOD_MIN_FILE_RADIUS` | 0.5px | Skip files smaller than this |
| `LOD_MIN_DIR_RADIUS` | 0.3px | Skip directories smaller than this |
| `LOD_MIN_FILE_LABEL_RADIUS` | 3.0px | Skip file labels below this |
| `LOD_MIN_DIR_LABEL_RADIUS` | 4.0px | Skip dir labels below this |
| `LOD_MIN_USER_RADIUS` | 1.0px | Skip users smaller than this |
| `LOD_MIN_USER_LABEL_RADIUS` | 5.0px | Skip user labels below this |
| `LOD_MIN_ZOOM_FOR_FILE_BRANCHES` | 0.05 | Skip file branches below this zoom |
| `LOD_MIN_ZOOM_FOR_DIR_BRANCHES` | 0.02 | Skip dir branches below this zoom |

**Impact at Scale**: At zoom=0.01 with 50,000 files, most entities are sub-pixel and skipped entirely.

#### 4. sqrt() Optimization in Disc Rendering

Optimized `draw_disc_3d()` in software renderer to use squared distance comparisons:

```rust
// Before: sqrt() called for EVERY pixel
let dist = dist2.sqrt();
if dist <= radius - aa_width { ... }

// After: sqrt() only for edge pixels (~18% of disc area)
if dist2 <= inner_sq {
    // Inner region: full opacity, NO sqrt needed
    color.a
} else {
    // Edge region: anti-aliased, sqrt needed
    let dist = dist2.sqrt();
    ...
}
```

**Impact**: ~78% of pixels in a typical disc skip the sqrt() call entirely.

#### 5. Zero-Allocation Post-Processing Effects

Eliminated per-frame allocations in `BloomEffect` and `ShadowEffect` by pre-allocating
reusable buffers that persist across frames.

**Files Modified**:
- `crates/rource-render/src/effects/bloom.rs`
- `crates/rource-render/src/effects/shadow.rs`

**BloomEffect Buffers** (for 1920x1080):
| Buffer | Size | Purpose |
|--------|------|---------|
| `bright_buffer` | 8.3 MB | Extracted bright pixels |
| `small_buffer` | 518 KB | Downscaled for blur |
| `blur_temp` | 518 KB | Blur intermediate |
| `bloom_buffer` | 8.3 MB | Final upscaled bloom |
| **Total saved** | **~19.2 MB/frame** | |

**ShadowEffect Buffers** (for 1920x1080):
| Buffer | Size | Purpose |
|--------|------|---------|
| `silhouette_buffer` | 2.1 MB | Alpha channel extraction |
| `offset_buffer` | 2.1 MB | Offset shadow |
| `blur_temp` | 2.1 MB | Blur intermediate |
| **Total saved** | **~8.4 MB/frame** | |

**Memory Churn Eliminated**:
- At 60 FPS: **1.66 GB/second** (bloom + shadow combined)
- At 144 FPS: **3.97 GB/second** (bloom + shadow combined)

**API Change**: Both effects now use `apply(&mut self, ...)` instead of `apply(&self, ...)`.
Buffers are allocated lazily on first `apply()` and reused for subsequent frames.
Automatic resize when dimensions change.

#### Performance Testing

All optimizations have been verified:
- Test suite: 939 tests passing
- WASM build: 583KB (250KB gzipped)
- No clippy warnings

### Phase 4 Optimizations (2026-01-21)

Additional performance optimizations for WebGL2 renderer:

#### 1. Shader Warmup/Precompilation

GPU shader compilation often happens lazily when a program is first used with actual
draw calls, causing visible stutters on the first frame. The `warmup_shaders()` method
moves this cost to initialization:

**Implementation** (in `mod.rs`):
```rust
fn warmup_shaders(&mut self) {
    // For each shader program:
    // 1. Use the program (gl.use_program)
    // 2. Set all uniforms with valid values
    // 3. Bind the appropriate VAO
    // 4. Issue zero-instance draw call (triggers GPU compilation)
}
```

**Benefits**:
- Eliminates first-frame stutters for each primitive type
- Forces GPU driver optimization at startup instead of during rendering
- Especially important for WebGL where compilation can be heavily deferred

**Timing**: Called at end of `init_gl()` after all shaders are compiled.

#### 2. Texture Atlas Defragmentation

The font atlas uses row-based packing which can lead to fragmentation over time.
Added tracking and automatic defragmentation:

**Statistics** (`AtlasStats` struct):
| Field | Description |
|-------|-------------|
| `glyph_count` | Total number of glyphs in atlas |
| `used_pixels` | Pixels occupied by actual glyph data |
| `allocated_pixels` | Pixels in allocated regions (includes padding) |
| `fragmentation` | Ratio: `1 - (used / allocated)` |

**Configuration**:
```rust
const DEFRAG_THRESHOLD: f32 = 0.5; // 50% fragmentation triggers defrag
```

**Defragmentation Process**:
1. Collect all glyphs with their stored bitmaps
2. Sort by height (tallest first) for better row packing
3. Clear atlas data and reset packer
4. Re-insert all glyphs in optimal order
5. Update all region positions
6. Force full texture upload

**API**:
```rust
// Check if defragmentation is recommended
let needs_defrag = atlas.needs_defragmentation();

// Get detailed statistics
let stats = atlas.stats();
println!("Fragmentation: {:.1}%", stats.fragmentation * 100.0);

// Manually trigger defragmentation
let did_defrag = atlas.defragment();
```

**Automatic Trigger**: When allocation fails and fragmentation > 50%, defragmentation
is attempted before resizing the atlas.

### Phase 5 Optimizations (2026-01-21)

Additional GPU buffer and WebGL state optimizations:

#### 1. Instance Buffer Sub-Data Updates

Optimized instance buffer uploads to reuse existing GPU buffer memory when possible,
avoiding expensive reallocations on every frame.

**Before**: Every frame called `gl.bufferData()` which:
- Allocates new GPU memory
- Copies data to GPU
- Deallocates old buffer
- Cost: ~0.5ms per primitive type × 6 types = ~3ms/frame

**After**: Uses `gl.bufferSubData()` when data fits within existing capacity:
- Reuses existing GPU buffer
- Only copies data (no allocation)
- Cost: ~0.1ms per primitive type × 6 types = ~0.6ms/frame

**Implementation** (in `buffers.rs`):
```rust
// Track GPU buffer capacity separately from CPU capacity
gpu_buffer_size: usize,

// In upload():
if data_size <= self.gpu_buffer_size && self.gpu_buffer_size > 0 {
    // Fast path: update existing buffer in-place
    gl.buffer_sub_data_with_i32_and_u8_array(
        WebGl2RenderingContext::ARRAY_BUFFER,
        0,
        byte_data,
    );
} else {
    // Slow path: allocate with extra capacity, then upload
    gl.buffer_data_with_i32(...);  // Pre-allocate
    gl.buffer_sub_data_with_i32_and_u8_array(...);  // Upload data
}
```

**Performance Impact**:
- ~80% reduction in GPU buffer overhead per frame
- Eliminates per-frame GPU memory churn
- Especially noticeable for large visualizations (5000+ entities)

**Capacity Strategy**: Buffers are allocated with 2x headroom to reduce future
reallocations. When usage drops significantly, buffers shrink after a stability
period (tracked via `low_usage_frames` and `peak_usage`).

#### 2. WebGL State Caching (Already Implemented)

The WebGL2 renderer includes comprehensive state caching via `GlStateCache`:

| Cached State | Purpose |
|--------------|---------|
| `bound_program` | Avoid redundant `gl.useProgram()` |
| `bound_vao` | Avoid redundant `gl.bindVertexArray()` |
| `bound_texture` | Avoid redundant `gl.bindTexture()` |
| `cached_resolution` | Avoid redundant uniform updates |

**Usage**: All state changes go through the state cache:
```rust
fn use_program(&mut self, gl: &WebGl2RenderingContext, program: &WebGlProgram) {
    if self.bound_program.as_ref() != Some(program) {
        gl.use_program(Some(program));
        self.bound_program = Some(program.clone());
    }
}
```

### Phase 6 Optimizations (2026-01-21)

Additional WebGL2 rendering optimizations for reduced API overhead:

#### 1. Uniform Buffer Objects (UBOs)

Implemented UBOs for sharing common uniforms across all shader programs. Instead of
setting `u_resolution` individually for each shader (~12 calls/frame), we now upload
it once via a uniform buffer.

**Files Added**:
- `crates/rource-render/src/backend/webgl2/ubo.rs` - UBO management

**Implementation**:
```rust
// UBO binding point shared by all shaders
pub const COMMON_UNIFORMS_BINDING: u32 = 0;

// UBO layout (std140):
// - bytes 0-7: u_resolution (vec2)
// - bytes 8-15: padding (std140 alignment)

// Per-frame update (once per frame instead of per-shader):
ubo_manager.set_resolution(width, height);
ubo_manager.upload(gl);
ubo_manager.bind(gl);
```

**UBO-Enabled Shaders**:
All primitive vertex shaders now have UBO variants (`*_UBO` suffix) that use a
uniform block instead of individual uniforms:

```glsl
// UBO-enabled shader (std140 layout, binding = 0)
layout(std140, binding = 0) uniform CommonUniforms {
    vec2 u_resolution;
    vec2 _padding;
};
```

**Performance Impact**:
- Legacy mode: ~12 `gl.uniform2f()` calls per frame
- UBO mode: 1 `gl.bufferSubData()` call per frame
- ~90% reduction in uniform-related API overhead

**Automatic Fallback**: If UBO initialization fails, the renderer falls back to
legacy shaders with individual uniforms transparently.

#### 2. Frame Statistics for Debugging

Added comprehensive frame statistics tracking for performance profiling:

**Files Added**:
- `crates/rource-render/src/backend/webgl2/stats.rs` - FrameStats struct

**Statistics Tracked**:

| Metric | Description |
|--------|-------------|
| `draw_calls` | Number of instanced draw calls |
| `total_instances` | Total primitives rendered |
| `circle_instances` | Circles rendered |
| `ring_instances` | Rings rendered |
| `line_instances` | Lines rendered |
| `quad_instances` | Solid quads rendered |
| `textured_quad_instances` | Textured quads rendered |
| `text_instances` | Text glyphs rendered |
| `program_switches` | Shader program changes |
| `vao_switches` | VAO binding changes |
| `texture_binds` | Texture binding calls |
| `uniform_calls` | Uniform calls (legacy mode only) |
| `ubo_enabled` | Whether UBO mode is active |

**API Usage**:
```rust
let stats = renderer.frame_stats();
println!("{}", stats.summary());
// Output: "Draws: 6, Instances: 1200 (200.0/draw), Programs: 6, VAOs: 6, UBO: on"
```

**Test Count**: 950 tests (added 11 new tests for UBO and stats modules)

### Phase 7 Optimizations (2026-01-21)

Enhanced frame statistics and render efficiency tracking:

#### 1. Active Primitive Tracking

Added `ActivePrimitives` bitflags to track which primitive types were rendered each frame:

| Flag | Description |
|------|-------------|
| `CIRCLES` | Filled circles (discs) |
| `RINGS` | Circle outlines |
| `LINES` | Line segments |
| `QUADS` | Solid colored rectangles |
| `TEXTURED_QUADS` | Textured rectangles |
| `TEXT` | Text glyphs |

**Usage**:
```rust
let stats = renderer.frame_stats();
let active = stats.active_primitives;
println!("Active types: {}", active.count());
println!("Has circles: {}", active.is_set(ActivePrimitives::CIRCLES));
```

#### 2. Enhanced Frame Statistics

Extended `FrameStats` with additional metrics for render efficiency analysis:

| Metric | Description |
|--------|-------------|
| `skipped_program_binds` | Redundant program binds avoided by state cache |
| `skipped_vao_binds` | Redundant VAO binds avoided by state cache |
| `skipped_texture_binds` | Redundant texture binds avoided by state cache |
| `active_primitives` | Bitflags of rendered primitive types |
| `bloom_applied` | Whether bloom effect was applied |
| `shadow_applied` | Whether shadow effect was applied |

**New Methods**:
```rust
// Batch efficiency (0.0-1.0): active_primitives / program_switches
let efficiency = stats.batch_efficiency();

// Total redundant state changes avoided
let saved = stats.total_skipped_binds();

// Check if any post-processing was applied
let has_pp = stats.has_post_processing();

// Detailed summary with all metrics
println!("{}", stats.detailed_summary());
```

#### 3. Improved Bloom+Shadow Handling

Clarified the interaction between bloom and shadow effects in `end_frame()`:
- When both effects are enabled, bloom takes precedence
- Shadow-only and bloom-only paths are now explicit
- Post-processing application is tracked in frame stats

**Test Count**: 955 tests (added 5 new tests for enhanced frame statistics)

### Phase 8 Optimizations (2026-01-22)

Zero-allocation hot path optimizations for maximum FPS in WASM WebGPU demo.

#### 1. Zero-Allocation Visibility Query

Added `visible_entities_into()` method to Scene that reuses pre-allocated buffers:

**Files Modified**:
- `crates/rource-core/src/scene/mod.rs` - Added `visible_entities_into()`
- `rource-wasm/src/lib.rs` - Visibility buffers in Rource struct
- `rource-wasm/src/render_phases.rs` - RenderContext uses borrowed slices

**Before**:
```rust
// Allocates 3 new Vecs every frame
let (dirs, files, users) = scene.visible_entities(&bounds);
```

**After**:
```rust
// Zero allocations after initial capacity
scene.visible_entities_into(&bounds, &mut dirs_buf, &mut files_buf, &mut users_buf);
```

**Impact**: Eliminates 180 allocations/second at 60 FPS.

#### 2. Streaming Spline Interpolation

Replaced Vec-allocating spline interpolation with streaming computation:

**Files Modified**:
- `crates/rource-render/src/backend/wgpu/mod.rs` - Streaming Catmull-Rom
- `crates/rource-render/src/backend/software.rs` - Streaming transform

**Before**:
```rust
let interpolated = Self::interpolate_spline(points, 8);  // Allocates Vec
for window in interpolated.windows(2) { ... }
```

**After**:
```rust
// Zero-allocation streaming: compute and draw immediately
for i in 0..points.len() - 1 {
    for j in 1..=SEGMENTS_PER_SPAN {
        // Catmull-Rom computed on-the-fly
        self.draw_line(prev_point, curr_point, width, color);
    }
}
```

**Impact**: Eliminates 1 Vec allocation per visible curve (potentially 1000s/frame).

#### 3. Cached Texture ID Buffer

Both wgpu and WebGL2 renderers now cache texture ID lists:

**Files Modified**:
- `crates/rource-render/src/backend/wgpu/mod.rs`
- `crates/rource-render/src/backend/webgl2/mod.rs`

**Before**:
```rust
let tex_ids: Vec<TextureId> = self.textured_quad_instances.keys().copied().collect();
```

**After**:
```rust
self.cached_texture_ids.clear();
self.cached_texture_ids.extend(self.textured_quad_instances.keys().copied());
```

**Impact**: Eliminates 1 Vec allocation per frame per renderer.

#### 4. Hot Path Inline Hints

Added `#[inline]` hints to frequently-called functions:
- `visible_entities_into()` - Called every frame
- `draw_circle()`, `draw_disc()`, `draw_line()` - Called per primitive
- `push_raw()` - Called for every instance

#### Memory Impact Summary

| Optimization | Before (60 FPS) | After |
|-------------|-----------------|-------|
| Visibility query | 180 allocs/sec | 0 |
| Spline interpolation | N × curves/sec | 0 |
| Texture ID collection | 60 allocs/sec | 0 |

#### 5. wgpu Bloom Pipeline Wiring (2026-01-22)

Completed the integration of the wgpu GPU bloom post-processing pipeline:

**Files Modified**:
- `crates/rource-render/src/backend/wgpu/mod.rs` - Updated `begin_frame()` and `end_frame()`

**Architecture**:
```text
┌─────────────────────────────────────────────────────────────────────┐
│                         Frame Flow                                   │
│                                                                      │
│  begin_frame()                    end_frame()                       │
│  ┌─────────────┐                  ┌─────────────────────────────┐  │
│  │ Bloom       │──► scene_view() ─│ flush() to scene target    │  │
│  │ enabled?    │                  │ bloom.apply() ──► surface  │  │
│  └─────────────┘                  └─────────────────────────────┘  │
│  ┌─────────────┐                  ┌─────────────────────────────┐  │
│  │ Shadow-only │──► scene_texture │ flush() to scene texture   │  │
│  │ enabled?    │                  │ shadow.apply() ─► surface  │  │
│  └─────────────┘                  └─────────────────────────────┘  │
│  ┌─────────────┐                  ┌─────────────────────────────┐  │
│  │ No effects  │──► surface view  │ flush() direct to surface  │  │
│  └─────────────┘                  └─────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────────┘
```

**Key Changes**:
- `begin_frame()`: When bloom is enabled, calls `bloom_pipeline.ensure_size()` and uses
  `bloom_pipeline.scene_view()` as the render target (BloomPipeline manages its own scene FBO)
- `end_frame()`: Calls `bloom.apply()` to run the full bloom pipeline (bright extraction,
  gaussian blur passes, composite) and output to the surface
- Shadow-only path uses renderer's `scene_texture` and calls `shadow.apply()`
- Frame stats track `bloom_applied` and `shadow_applied` for debugging

**Post-Processing Priority**:
- Bloom takes precedence when both bloom and shadow are enabled
- Shadow-only renders when only shadow is enabled
- Direct rendering when no effects are enabled

#### 6. Bind Group Caching for Bloom/Shadow (2026-01-22)

Eliminated per-frame bind group allocations in wgpu bloom and shadow pipelines.

**Problem**: The `apply()` methods were creating bind groups on every frame call,
resulting in ~8-13 allocations per frame (480-780 allocations/second at 60 FPS).

**Solution**: Cache bind groups in `ensure_size()` when render targets are created,
reuse them in `apply()`.

**Files Modified**:
- `crates/rource-render/src/backend/wgpu/bloom.rs` - Added `CachedBindGroups` struct
- `crates/rource-render/src/backend/wgpu/shadow.rs` - Added `CachedShadowBindGroups` struct

**Bloom Pipeline Cached Bind Groups** (7 total):
| Bind Group | References |
|------------|------------|
| `bright_uniform_bg` | `bright_uniforms` buffer |
| `blur_uniform_bg` | `blur_uniforms` buffer |
| `composite_uniform_bg` | `composite_uniforms` buffer |
| `scene_texture_bg` | `scene_target` texture view |
| `bloom_a_texture_bg` | `bloom_target_a` texture view |
| `bloom_b_texture_bg` | `bloom_target_b` texture view |
| `bloom_final_texture_bg` | `bloom_target_a` (for composite) |

**Shadow Pipeline Cached Bind Groups** (5 total):
| Bind Group | References |
|------------|------------|
| `blur_uniform_bg` | `blur_uniforms` buffer |
| `composite_uniform_bg` | `composite_uniforms` buffer |
| `shadow_texture_bg` | `shadow_target` texture view |
| `blur_texture_bg` | `blur_target` texture view |
| `shadow_final_texture_bg` | `shadow_target` (for composite) |

**Note**: Shadow's `scene_texture_bg` cannot be cached because `scene_view` is passed
as a parameter to `apply()` and may vary between calls.

**Performance Impact**:
- Bloom: ~8 allocations/frame eliminated → 0
- Shadow: ~5 allocations/frame eliminated → 1 (scene_texture_bg)
- At 60 FPS: **780 allocations/second → 60 allocations/second** (92% reduction)

**When Bind Groups Are Recreated**:
- Viewport resize (via `ensure_size()`)
- First frame after initialization

**Test Count**: 1,094 tests passing

### Phase 9 Optimizations (2026-01-22)

GPU physics dispatch API for wgpu renderer.

#### 1. GPU Physics Dispatch Methods

Added methods to `WgpuRenderer` for running force-directed physics simulation on the GPU.
The existing `ComputePipeline` (1,325 lines, fully implemented) is now accessible through
a high-level API.

**Files Modified**:
- `crates/rource-render/src/backend/wgpu/mod.rs` - Added physics dispatch methods

**New Methods**:

| Method | Platform | Description |
|--------|----------|-------------|
| `warmup_physics()` | All | Pre-compiles compute shaders to avoid first-frame stutter |
| `dispatch_physics()` | Native | Synchronous physics step with immediate results |
| `dispatch_physics_with_bounds()` | Native | Physics + bounding box calculation |
| `dispatch_physics_async()` | WASM | Async physics step for non-blocking operation |
| `set_physics_config()` | All | Configure physics parameters |
| `physics_config()` | All | Get current physics configuration |
| `physics_stats()` | All | Get compute statistics from last dispatch |

**API Usage (Native)**:
```rust
use rource_render::backend::wgpu::{WgpuRenderer, ComputeEntity, PhysicsConfig};

// Create renderer
let mut renderer = WgpuRenderer::new_headless(800, 600)?;

// Optional: warmup to avoid first-frame stutter
renderer.warmup_physics();

// Configure physics (optional, has sensible defaults)
renderer.set_physics_config(PhysicsConfig::dense());

// Create entities from scene data
let entities: Vec<ComputeEntity> = scene_nodes.iter()
    .map(|node| ComputeEntity::new(node.x, node.y, node.radius))
    .collect();

// Run physics step (synchronous)
let updated = renderer.dispatch_physics(&entities, 0.016); // dt = 1/60s

// Apply updated positions back to scene
for (node, entity) in scene_nodes.iter_mut().zip(updated.iter()) {
    let (x, y) = entity.position();
    node.set_position(x, y);
}
```

**API Usage (WASM)**:
```rust
// Async version for WASM (non-blocking)
let updated = renderer.dispatch_physics_async(&entities, 0.016).await;
```

**Physics Configuration Presets**:

| Preset | Repulsion | Attraction | Damping | Use Case |
|--------|-----------|------------|---------|----------|
| `PhysicsConfig::default()` | 1000 | 0.05 | 0.9 | General use |
| `PhysicsConfig::dense()` | 2000 | 0.1 | 0.85 | Tightly packed nodes |
| `PhysicsConfig::sparse()` | 500 | 0.02 | 0.95 | Spread out layouts |
| `PhysicsConfig::fast_converge()` | 1500 | 0.08 | 0.8 | Quick settling |

**Compute Pipeline Architecture**:
```text
┌─────────────────────────────────────────────────────────────────────┐
│                    GPU Physics Pipeline                              │
│                                                                      │
│  upload_entities()                                                   │
│       │                                                              │
│       ▼                                                              │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐   │
│  │ Clear Grid  │→│ Build Grid  │→│ Calc Forces │→│  Integrate  │   │
│  │ (spatial    │ │ (populate   │ │ (repulsion  │ │ (velocity + │   │
│  │  hash)      │ │  cells)     │ │ + attract)  │ │  position)  │   │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────────┘   │
│       │                                                  │           │
│       ▼                                                  ▼           │
│  ┌─────────────┐                              ┌─────────────┐       │
│  │ Calc Bounds │ (optional)                   │  Readback   │       │
│  │ (AABB)      │                              │ (download)  │       │
│  └─────────────┘                              └─────────────┘       │
└─────────────────────────────────────────────────────────────────────┘
```

**Performance Characteristics**:

| Aspect | CPU Physics | GPU Physics |
|--------|-------------|-------------|
| Algorithm | O(n²) pairwise | Spatial hash grid |
| 1000 nodes | ~1M comparisons/frame | ~Local neighbors only |
| 5000 nodes | ~25M comparisons/frame | ~Same overhead |
| Parallelization | Single-threaded | 64-thread workgroups |
| Best for | < 500 nodes | > 1000 nodes |

**When to Use GPU Physics**:
- Large repositories with 1000+ directories
- Need for real-time interaction at high FPS
- GPU compute is available (WebGPU or native Vulkan/Metal/DX12)

**When to Use CPU Physics**:
- Small repositories (< 500 nodes)
- No GPU compute available (software renderer fallback)
- Need for deterministic cross-platform results

**Test Count**: 1,094 tests passing

### GPU Bloom Effect for WebGL2 (2026-01-21)

Implemented full GPU-based bloom post-processing for the WebGL2 backend. This provides
hardware-accelerated glow effects around bright areas of the scene.

#### Architecture

```
crates/rource-render/src/backend/webgl2/
├── mod.rs          # WebGl2Renderer with bloom integration
├── bloom.rs        # BloomPipeline, BloomFbo, BloomConfig
├── shadow.rs       # ShadowPipeline for drop shadows
├── shaders.rs      # GLSL ES 3.0 shaders (legacy + UBO variants)
├── buffers.rs      # VBO/VAO management including fullscreen quad
├── textures.rs     # Texture atlas for font glyphs
├── state.rs        # GlStateCache for state caching
├── stats.rs        # FrameStats for debugging
├── ubo.rs          # UniformBufferManager for shared uniforms
└── adaptive.rs     # Adaptive quality controller
```

#### Pipeline Overview

The bloom effect is implemented as a multi-pass post-processing pipeline:

1. **Scene Render**: Scene is rendered to a scene FBO instead of directly to canvas
2. **Bright Pass**: Extract pixels above brightness threshold (using ITU-R BT.601 luminance)
3. **Blur Pass (H)**: Horizontal 9-tap Gaussian blur on downscaled bloom FBO
4. **Blur Pass (V)**: Vertical blur (ping-pong to second FBO)
5. **Composite**: Additively blend bloom with original scene to canvas

#### Key Components

| Component | Description |
|-----------|-------------|
| `BloomConfig` | Configuration struct (enabled, threshold, intensity, downscale, passes) |
| `BloomFbo` | Framebuffer object wrapper with texture attachment |
| `BloomPipeline` | Orchestrates the full bloom pipeline |
| `BloomProgram` | Compiled shader program with uniform locations |

#### Configuration Options

```rust
// Default configuration
pub const DEFAULT_BLOOM_THRESHOLD: f32 = 0.7;  // Brightness threshold (0.0 - 1.0)
pub const DEFAULT_BLOOM_INTENSITY: f32 = 1.0;  // Glow intensity multiplier
pub const DEFAULT_BLOOM_DOWNSCALE: u32 = 4;    // Bloom buffer downscale factor
pub const DEFAULT_BLOOM_PASSES: u32 = 2;       // Number of blur passes
```

#### Preset Configurations

```rust
// Subtle bloom - gentle glow on very bright areas
let subtle = BloomConfig::subtle();   // threshold=0.8, intensity=0.5, passes=1

// Intense bloom - pronounced glow effect
let intense = BloomConfig::intense(); // threshold=0.5, intensity=2.0, passes=3
```

#### WebGL2 Renderer API

```rust
// Enable/disable bloom
renderer.set_bloom_enabled(true);

// Configure bloom parameters
renderer.set_bloom_threshold(0.7);   // Lower = more bloom
renderer.set_bloom_intensity(1.0);   // Higher = brighter glow
renderer.set_bloom_downscale(4);     // Higher = faster but blockier
renderer.set_bloom_passes(2);        // More = softer, spread-out bloom

// Get full configuration
let config = renderer.bloom_config();
renderer.set_bloom_config(BloomConfig::intense());
```

#### Performance Characteristics

| Aspect | Details |
|--------|---------|
| Memory | 3 FBOs: scene (full res), bloom A/B (downscaled) |
| GPU Cost | 4 draw calls per frame (bright + 2×blur + composite) |
| Downscale | Bloom computed at 1/4 resolution by default |
| Lazy Init | FBOs created only when bloom is enabled |
| Context Recovery | Full state preserved across WebGL context loss |

#### WASM Integration Note

The GPU bloom is automatically wired into the WebGL2 backend. When WASM calls
`setBloom(true)`, the `WebGl2Renderer::set_bloom_enabled()` method activates the
full GPU pipeline. No additional JavaScript code is required.

### WebAssembly Implementation (2026-01-10)

Successfully implemented WebAssembly support for running Rource in web browsers:

#### Implementation Details

1. **Architecture**: Uses software renderer with ImageData transfer to canvas
   - Reuses existing SoftwareRenderer for all drawing operations
   - Converts ARGB pixel buffer to RGBA for web canvas
   - ~235KB gzipped WASM bundle

2. **JavaScript API**: Exposes Rource class with methods:
   - `loadCustomLog(log)`: Load pipe-delimited commit data
   - `loadGitLog(log)`: Load git log format
   - `play()`, `pause()`, `togglePlay()`: Playback control
   - `zoom(factor)`, `pan(dx, dy)`: Camera control
   - `frame(timestamp)`: Animation frame handler

3. **Controls**:
   - Mouse drag for panning
   - Mouse wheel for zooming
   - Keyboard: Space=play, +/-=zoom, R=reset, arrows=pan

4. **Build**: `scripts/build-wasm.sh` uses wasm-pack
   - Output in `rource-wasm/www/pkg/`
   - Demo page in `rource-wasm/www/index.html`

### wgpu Backend Implementation (2026-01-21)

Implemented production-grade wgpu rendering backend for cross-platform GPU rendering:

#### Architecture

```
crates/rource-render/src/backend/wgpu/
├── mod.rs          # WgpuRenderer implementing Renderer trait
├── buffers.rs      # Instance/uniform buffer management
├── compute.rs      # GPU compute shaders for physics simulation
├── pipeline.rs     # Render pipeline creation and caching
├── shaders.rs      # WGSL shader source code
├── state.rs        # Render state caching (pipeline, bind groups)
├── stats.rs        # Frame statistics with active primitive tracking
├── textures.rs     # Font atlas and texture management
├── bloom.rs        # GPU bloom post-processing pipeline
└── shadow.rs       # GPU drop shadow effect
```

#### Key Features

1. **Cross-Platform GPU**: Native (Vulkan/Metal/DX12) + WASM (WebGPU/WebGL)
2. **Instanced Rendering**: All primitives use GPU instancing for efficient batching
3. **WGSL Shaders**: Distance-field anti-aliasing for smooth edges
4. **Font Atlas**: Row-based packing with automatic defragmentation
5. **State Caching**: Minimizes redundant GPU API calls
6. **GPU Compute**: Force-directed physics simulation on GPU
7. **Post-Processing**: Configurable bloom and shadow effects
8. **Deterministic Output**: Identical inputs produce identical outputs

#### Usage

```rust
// Native - headless
let renderer = WgpuRenderer::new_headless(800, 600)?;

// Native - with window
let renderer = WgpuRenderer::new_with_window(&window)?;

// WASM - with canvas (async)
let renderer = WgpuRenderer::new_from_canvas(&canvas).await?;
```

#### Feature Flag

Enable with `wgpu` feature in Cargo.toml:
```toml
rource-render = { path = "...", features = ["wgpu"] }
```

### WebGL2 Backend Implementation (2026-01-11)

Successfully implemented GPU-accelerated WebGL2 rendering backend for WASM:

#### Architecture

```
crates/rource-render/src/backend/webgl2/
├── mod.rs          # WebGl2Renderer implementing Renderer trait
├── bloom.rs        # GPU bloom post-processing pipeline
├── shadow.rs       # GPU shadow post-processing pipeline
├── shaders.rs      # GLSL ES 3.0 shader sources (legacy + UBO variants)
├── buffers.rs      # VBO/VAO management for instanced rendering
├── textures.rs     # Texture atlas for font glyphs
├── state.rs        # GlStateCache for avoiding redundant API calls
├── stats.rs        # FrameStats for debugging and profiling
├── ubo.rs          # Uniform Buffer Objects for shared uniforms
└── adaptive.rs     # Adaptive quality controller
```

#### Key Features

1. **Instanced Rendering**: All primitives use GPU instancing for efficient batching
   - Circles, rings, lines, quads, and text are drawn with single draw calls
   - Instance data uploaded per-frame via dynamic VBOs

2. **Anti-Aliased Shaders**: All primitives are rendered with anti-aliasing
   - Circles/rings use distance-field based AA
   - Lines use perpendicular distance for smooth edges

3. **Font Atlas**: Glyph caching in GPU texture
   - Row-based packing with dynamic growth (512 -> 2048 max)
   - Single-channel alpha texture for efficient text rendering

4. **Automatic Fallback**: WASM tries WebGL2 first, falls back to software
   - `rource.getRendererType()` returns "webgl2" or "software"
   - `rource.isWebGL2()` for boolean check

5. **Context Loss Handling**: Graceful recovery from WebGL context loss
   - Detects loss via `gl.is_context_lost()`
   - `recover_context()` method to reinitialize resources

6. **GPU Bloom Effect**: Full post-processing bloom pipeline
   - FBO-based render-to-texture for scene capture
   - Separable Gaussian blur (9-tap, configurable passes)
   - Additive compositing with original scene

#### JavaScript API Additions

```javascript
// Check which renderer is active
const renderer = rource.getRendererType(); // "webgl2" or "software"
const isGPU = rource.isWebGL2();           // true/false
```

### Memory Optimization for Large Repositories (2026-01-11)

Implemented memory-efficient storage for very large repositories (tested with Home Assistant core: 103,533 commits, 533,366 file changes).

#### Architecture

```
crates/rource-vcs/src/
├── intern.rs     # String interning (StringInterner, PathInterner)
├── compact.rs    # Compact commit storage (CommitStore, CompactCommit)
└── stream.rs     # Streaming parsers (GitLogStream, StreamingCommitLoader)
```

#### Key Features

1. **String Interning**: Deduplicates repeated strings
   - `StringInterner` - Basic deduplication with u32 handles
   - `PathInterner` - Stores path segments separately for deeper deduplication
   - Author names: 4,776 unique vs 103,533 commits (22x dedup)
   - Path segments: 10,248 unique vs 62,012 paths (6x reuse)

2. **Compact Structures**: Minimized per-commit/file overhead
   - `CompactCommit`: 24 bytes (vs ~72+ for standard Commit)
   - `CompactFileChange`: 8 bytes (vs ~48+ for standard FileChange)
   - Short hash stored inline as `[u8; 7]`

3. **Streaming Parsing**: Process logs without full memory load
   - `GitLogStream` - Iterator-based git log parsing
   - `StreamingCommitLoader` - Loads directly into CommitStore
   - Progress callbacks for large file feedback

#### Benchmark Results (Home Assistant Core)

```
Standard Storage:    51.65 MB
Compact Storage:     16.43 MB
Memory Savings:      35.22 MB (68.2%)

Deduplication:
- Unique authors: 4,776 (vs 103,533 commits) = 22x
- Unique paths: 62,012 (10,248 segments) = 8.6x reuse
```

#### Usage

```rust
use rource_vcs::stream::StreamingCommitLoader;
use std::io::BufReader;
use std::fs::File;

let file = File::open("git.log")?;
let loader = StreamingCommitLoader::new(BufReader::new(file));
let store = loader.load_with_progress(|commits, files| {
    eprintln!("Loaded {} commits, {} files", commits, files);
});

// Access commits via CommitStore API
for (id, commit) in store.commits() {
    let author = store.resolve_author(commit.author).unwrap();
    let files = store.file_changes(commit);
    // ...
}
```

### Web UI Development (2026-01-20)

The WASM demo includes a rich web UI (`rource-wasm/www/`) with interactive controls. The JavaScript code uses a modular ES Module architecture for maintainability.

#### File Structure

```
rource-wasm/www/
├── index.html           # Page structure, sidebar panels, controls
├── styles.css           # Complete styling including responsive design
├── app.js               # Legacy monolithic file (kept for reference)
├── pkg/                 # WASM build output (auto-generated)
└── js/                  # Modular JavaScript (ES Modules)
    ├── main.js          # Entry point - initializes WASM and coordinates modules
    ├── config.js        # Configuration constants and extension colors
    ├── telemetry.js     # Observability and debugging utilities
    ├── utils.js         # Utility functions (debounce, escapeHtml, etc.)
    ├── state.js         # Application state with observable pattern
    ├── preferences.js   # localStorage handling for user preferences
    ├── url-state.js     # URL parameters for shareable links
    ├── wasm-api.js      # Safe WASM call wrappers with error boundaries
    ├── cached-data.js   # Embedded demo repository data
    ├── dom.js           # Centralized DOM element references
    ├── toast.js         # Toast notification system
    ├── animation.js     # Render loop, canvas management, perf metrics
    ├── data-loader.js   # Data loading and format detection
    └── features/        # Feature-specific modules
        ├── screenshot.js   # Screenshot capture
        ├── fullscreen.js   # Native and pseudo-fullscreen support
        ├── theme.js        # Light/dark theme toggle
        ├── help.js         # First-time user help overlay
        └── keyboard.js     # Centralized keyboard shortcuts
```

#### Module Architecture

The modular architecture follows these principles:

1. **Single Responsibility**: Each module handles one concern
2. **Explicit Dependencies**: All imports are at the top of each file
3. **Observable State**: `state.js` provides subscribe/setState for loose coupling
4. **Error Boundaries**: `wasm-api.js` wraps all WASM calls with error handling
5. **Centralized DOM**: `dom.js` lazily initializes and caches element references

#### Key Modules

| Module | Purpose |
|--------|---------|
| `main.js` | Entry point, WASM init, event listeners, coordinates all modules |
| `state.js` | Observable application state with subscribe pattern |
| `wasm-api.js` | Safe WASM call wrappers (safeWasmCall, safeWasmVoid) |
| `animation.js` | Render loop, resizeCanvas, updatePlaybackUI, performance metrics |
| `preferences.js` | localStorage read/write with panel state management |
| `features/screenshot.js` | Screenshot capture with animation loop pause/resume |

#### Sidebar Architecture

The sidebar uses a scroll indicator pattern to show users when more content is available:

```html
<div class="sidebar-wrapper">
    <div class="sidebar-panel" id="sidebar-panel">
        <!-- All sidebar content -->
    </div>
    <div class="sidebar-scroll-indicator">
        <span>Scroll for more</span>
        <svg><!-- chevron --></svg>
    </div>
</div>
```

JavaScript (in `main.js`) detects scroll position and hides the indicator when near the bottom.

#### Collapsible Panels

Panels use a single consolidated handler in `setupPanelToggleHandlers()` (from `preferences.js`) that:
1. Toggles the `collapsed` class
2. Updates `aria-expanded` for accessibility
3. Saves state to localStorage via `updatePreference()`

**CRITICAL**: Avoid duplicate event handlers. If you add both `addEventListener` and `onclick`, the toggle will fire twice, canceling itself out.

#### Common Web UI Issues

| Symptom | Cause | Solution |
|---------|-------|----------|
| Collapsible panels don't toggle | Duplicate handlers (toggle twice = no effect) | Use single handler via `setupPanelToggleHandlers()` in `preferences.js` |
| Fetch button errors not visible | Error caught but not displayed | Show toast AND update status element |
| Buttons disabled after load | WASM not initialized | Buttons enable in `main()` after `init()` |
| Panel state not persisting | Wrong preference key | Check `panelMappings` in `preferences.js` |
| Screenshot corrupted/blank | Animation loop races with toBlob() | Stop animation before capture (see `features/screenshot.js`) |

#### Testing Web UI Changes

Since JavaScript has no compile-time checks, test manually:
1. Open browser DevTools console for errors
2. Test all collapsible panels (click to expand/collapse)
3. Test fetch with valid URL, invalid URL, and empty input
4. Test on mobile viewport (sidebar becomes overlay)
5. Verify scroll indicator appears/disappears correctly
6. Test screenshot functionality (should pause/resume animation)

### Headless Rendering Implementation (2026-01-10)

Successfully implemented headless rendering mode for batch video export. Key learnings:

#### Issues Discovered & Fixed

1. **Infinite Loop Bug**: The termination condition `current_commit >= commits.len()` was never true because `current_commit` maxes at `len-1`. Fixed by using `saturating_sub(1)` and checking `last_applied_commit`.

2. **Static Bounds Issue**: `scene.bounds()` returned the quadtree's fixed bounds (-5000 to 5000) instead of actual entity positions. Added `compute_entity_bounds()` method to calculate real bounding box.

3. **Files Invisible on First Frame**: Files start with `alpha=0.0` and fade in at `FADE_RATE=2.0` per second. On first frame with dt=1/60, alpha was only 3%. Fixed with pre-warm phase.

4. **Camera Not Positioned**: Camera smoothing (0.85 factor) prevented immediate positioning. Fixed by using `jump_to()` and `set_zoom()` directly.

#### Architecture Insights

- **Entity Alpha**: Files use fade-in animation (`rource-core/src/scene/file.rs:98`). New files start invisible and fade in over ~0.5 seconds.
- **Scene Bounds vs Entity Bounds**: `scene.bounds()` returns the spatial index bounds, not entity bounds. Use `scene.compute_entity_bounds()` for actual entity positions.
- **Camera Smoothing**: Camera uses lerp interpolation by default. For immediate positioning, use `jump_to()` + `set_zoom()` instead of `fit_to_bounds()`.

### Coordinate System

- **World Space**: Entities live in world coordinates centered around (0,0)
- **Screen Space**: Top-left is (0,0), Y increases downward
- **Camera Transform**: `camera.world_to_screen(pos)` converts world to screen coordinates

## Testing & Validation Best Practices

### Production-Grade Testing Checklist

Before considering any feature complete, verify:

```bash
# 1. All tests pass
cargo test

# 2. No clippy warnings
cargo clippy -- -D warnings

# 3. Code is formatted
cargo fmt --check

# 4. Release build works
cargo build --release

# 5. Headless export produces valid output
./target/release/rource --headless --output /tmp/test-frames /path/to/repo
```

### Validating Headless Output

```bash
# Generate frames
./target/release/rource --headless --output /tmp/frames --seconds-per-day 0.5 .

# Verify frames have content (not all black)
python3 << 'EOF'
with open('/tmp/frames/frame_00000000.ppm', 'rb') as f:
    for _ in range(3): f.readline()  # Skip header
    data = f.read()
    non_zero = sum(1 for b in data if b != 0)
    pct = 100 * non_zero / len(data)
    print(f'{non_zero} non-zero bytes ({pct:.1f}%) - {"OK" if pct > 1 else "EMPTY!"}')
EOF

# Convert to video (requires ffmpeg)
ffmpeg -framerate 60 -i /tmp/frames/frame_%08d.ppm -c:v libx264 -pix_fmt yuv420p output.mp4
```

### Key Test Files

| File | Purpose |
|------|---------|
| `rource-cli/src/main.rs` | CLI integration tests (24 tests) |
| `rource-core/src/scene/mod.rs` | Scene graph tests |
| `rource-core/src/camera/mod.rs` | Camera behavior tests |
| `rource-render/src/backend/software.rs` | Renderer tests |

### Determinism Requirements

For 100% deterministic output:

1. **Use fixed time step**: In headless mode, use `dt = 1.0 / framerate` instead of real delta time
2. **Seed random generators**: Any randomness (e.g., initial positions) should use a fixed seed
3. **Pre-warm the scene**: Apply first commit and run ~30 update cycles before first render
4. **Force camera position**: Use `jump_to()` + `set_zoom()` instead of smooth transitions

### Observability

Add debug output for troubleshooting:

```rust
// In headless mode, add early exit debugging:
eprintln!("files={}, users={}, camera=({:.1},{:.1}), zoom={:.3}",
    scene.file_count(), scene.user_count(),
    camera.position().x, camera.position().y, camera.zoom());

// Check pixel output:
let non_black = pixels.iter().filter(|&&p| p != 0xFF000000).count();
eprintln!("Frame {}: {} non-black pixels", frame, non_black);
```

## Common Tasks

### Adding a New VCS Parser

1. Create `crates/rource-vcs/src/parser/newvcs.rs`
2. Implement the `Parser` trait (see `parser/mod.rs`)
3. Register in `crates/rource-vcs/src/detect.rs`
4. Add tests in `crates/rource-vcs/src/parser/newvcs.rs`

### Adding a New Rendering Backend

1. Create `crates/rource-render/src/backend/newbackend.rs`
2. Implement the `Renderer` trait
3. Add feature flag in `Cargo.toml`
4. Update backend selection logic

### Adding a New Configuration Option

1. Add field to `Settings` struct in `rource-core/src/config/settings.rs`
2. Add CLI argument in `rource-cli/src/args.rs`
3. Add environment variable handling in `rource-core/src/config/config_env.rs`
4. Add WASM binding in `rource-wasm/src/lib.rs`
5. Update documentation

### Environment Variable Configuration

Settings can be configured via environment variables with the `ROURCE_` prefix:

```bash
# Examples
export ROURCE_WIDTH=1920
export ROURCE_HEIGHT=1080
export ROURCE_BLOOM_ENABLED=false
export ROURCE_SECONDS_PER_DAY=5.0
export ROURCE_TITLE="My Project"
export ROURCE_HIDE_USERS="bot.*"
```

Configuration priority (highest to lowest):
1. CLI arguments
2. Environment variables
3. Config file (--config)
4. Defaults

Boolean values accept: `1/true/yes/on` for true, `0/false/no/off` for false.

See `rource-core/src/config/config_env.rs` for the full list of 40+ supported variables.

### Running Against This Repository

```bash
# Windowed mode (interactive)
cargo run --release -- .

# Headless mode (batch export)
cargo run --release -- --headless --output /tmp/frames --seconds-per-day 0.5 .

# With effects disabled for faster rendering
cargo run --release -- --headless --no-bloom --output /tmp/frames .
```

## Dependencies Philosophy

We minimize external dependencies to:
- Reduce binary size
- Improve compile times
- Ensure WASM compatibility
- Avoid security surface area

### Approved Dependencies
| Crate | Reason |
|-------|--------|
| `fontdue` | Best pure-Rust font rasterizer |
| `regex-lite` | Lighter than `regex`, no PCRE |
| `chrono` | Date/time handling (limited features) |
| `wasm-bindgen` | Required for WASM |
| `clap` | CLI only, feature-gated |

### Avoid
- Heavy GUI frameworks (egui, iced) - we do custom rendering
- Full `image` crate - use minimal PNG/JPEG decoders
- `tokio`/`async-std` - synchronous design is simpler
- `serde` for core (optional for config files)

## Debugging

### Native
```bash
# Run with backtrace
RUST_BACKTRACE=1 cargo run

# Run with debug logging
RUST_LOG=debug cargo run

# Check specific frame output
./target/release/rource --headless --output /tmp/debug . 2>&1 | head -20
```

### WASM
- Use browser DevTools console
- Enable `console_error_panic_hook` for better panic messages
- Use `web-sys` console logging

### Common Issues

| Symptom | Cause | Solution |
|---------|-------|----------|
| Black frames | Files haven't faded in | Pre-warm scene with 30 update cycles |
| Infinite loop | Wrong termination condition | Check `current_commit >= commits.len().saturating_sub(1)` |
| Camera shows empty area | Using quadtree bounds | Use `compute_entity_bounds()` instead |
| Files at wrong position | Camera not updated | Call `camera.update(dt)` each frame |
| UI clicks do nothing | Duplicate event handlers | Consolidate to single handler, avoid both `onclick` and `addEventListener` |
| GitHub fetch silently fails | Error swallowed in catch | Always show error via `showToast()` and update status UI |
| WASM visuals don't match CLI | Rendering code not synced | Update both `rource-cli/src/rendering.rs` AND `rource-wasm/src/lib.rs` |
| Module import errors in browser | Wrong path or missing export | Check imports match exports, use relative paths (`./module.js`) |
| Screenshot blank/corrupted | Animation loop races with capture | Use `features/screenshot.js` which pauses animation during capture |

## CI/CD Pipeline

The project uses a comprehensive GitHub Actions CI/CD pipeline designed for portfolio-quality standards.

### Workflow Overview

| Workflow | File | Purpose | Triggers |
|----------|------|---------|----------|
| **CI** | `ci.yml` | Core quality gates | Push/PR to main |
| **Coverage** | `coverage.yml` | Code coverage with Codecov | Push/PR to main |
| **Benchmarks** | `bench.yml` | Performance tracking & regression detection | Push/PR to main |
| **Integration** | `integration.yml` | Headless rendering tests, nightly/beta Rust | Push/PR to main |
| **Security** | `security.yml` | Audits, license checks, unsafe code scan | Push/PR/Weekly |
| **Release** | `release.yml` | Multi-platform builds, signing, SBOM | Release published |
| **Docker** | `docker.yml` | Multi-arch container images | Push to main/tags |
| **Deploy Pages** | `deploy-pages.yml` | GitHub Pages deployment | Push to main |

### CI Jobs (ci.yml)

| Job | Description |
|-----|-------------|
| Format | `cargo fmt --check` |
| Clippy | All lints with `-D warnings` |
| Test | Multi-platform (Linux, macOS, Windows) |
| MSRV | Minimum Supported Rust Version (1.82) |
| Build (Native) | Release binary with size report |
| Build (WASM) | WebAssembly with gzip size check |
| Documentation | Rustdoc with warning-as-error |
| Features | Feature matrix (default, all, none) |

### Code Coverage (coverage.yml)

Uses `cargo-llvm-cov` for accurate coverage metrics:

```bash
# Local coverage generation
cargo llvm-cov --all-features --workspace --html
open target/llvm-cov/html/index.html
```

Coverage is uploaded to Codecov and displayed as a badge in README.

### Performance Regression Detection (bench.yml)

Benchmarks are stored and compared using `github-action-benchmark`:

- **Alert threshold**: 110% (10% regression triggers alert)
- **Storage**: Results stored in `gh-pages` branch under `dev/bench/`
- **PR comments**: Automatic comments on performance changes

Size metrics are also tracked:
- Native binary target: < 5MB
- WASM gzipped target: < 300KB

### Integration Tests (integration.yml)

**Headless Rendering Tests:**
- Tests custom log format parsing and rendering
- Tests repository visualization
- Validates PPM frame format and content
- Tests screenshot mode with PNG output

**Rust Toolchain Compatibility:**
- Nightly Rust (non-blocking)
- Beta Rust (non-blocking)

### Security Audit (security.yml)

| Check | Tool | Purpose |
|-------|------|---------|
| Vulnerabilities | `cargo audit` | Known CVE detection |
| Unsafe code | grep scan | Informational count |
| Advisories | `cargo deny` | RUSTSEC database |
| Licenses | `cargo deny` | License compliance |
| Bans | `cargo deny` | Dependency policies |

Runs weekly on schedule plus on every push/PR.

### Release Pipeline (release.yml)

**Build Targets (5 platforms):**

| Target | OS | Notes |
|--------|----|----|
| x86_64-unknown-linux-gnu | Ubuntu | Native |
| aarch64-unknown-linux-gnu | Ubuntu | Cross-compiled |
| x86_64-apple-darwin | macOS 13 | Intel |
| aarch64-apple-darwin | macOS 14 | Apple Silicon |
| x86_64-pc-windows-msvc | Windows | Native |

**Release Features:**
- GPG signed artifacts (requires `GPG_PRIVATE_KEY` secret)
- SHA256 checksums for all artifacts
- SBOM generation (SPDX + CycloneDX formats)
- Auto-generated changelog via git-cliff

### Docker Builds (docker.yml)

Multi-architecture container images:

```bash
# Pull from GitHub Container Registry
docker pull ghcr.io/tomtom215/rource:latest

# Run with repository mounted
docker run --rm -v $(pwd):/repo ghcr.io/tomtom215/rource /repo
```

**Features:**
- Multi-arch: `linux/amd64`, `linux/arm64`
- Build attestation for supply chain security
- Trivy vulnerability scanning
- Non-root user for security

### Auto-Changelog (cliff.toml)

Uses git-cliff with conventional commits:

```bash
# Generate changelog locally
git cliff --output CHANGELOG.md

# Preview unreleased changes
git cliff --unreleased
```

Commit types mapped to sections:
- `feat:` → Features
- `fix:` → Bug Fixes
- `perf:` → Performance
- `docs:` → Documentation
- `refactor:` → Refactoring
- `test:` → Testing

### Required Secrets

For full CI functionality, configure these repository secrets:

| Secret | Purpose | Required |
|--------|---------|----------|
| `GITHUB_TOKEN` | Automatic | Yes (auto) |
| `GPG_PRIVATE_KEY` | Release signing | Optional |
| `GPG_PASSPHRASE` | GPG key passphrase | Optional |
| `CODECOV_TOKEN` | Coverage uploads | Optional |

### Local CI Verification

Before pushing, run these checks locally:

```bash
# Full CI check
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test --all
cargo doc --no-deps --all-features

# Coverage
cargo llvm-cov --all-features --workspace

# Security
cargo audit
cargo deny check

# Integration test
cargo build --release
./target/release/rource --headless --output /tmp/frames --seconds-per-day 0.1 .
```

## Git Workflow

### Branches
- `main` - Stable releases
- `develop` - Integration branch
- `feature/*` - New features
- `fix/*` - Bug fixes
- `claude/*` - AI-assisted development branches

### Commit Messages
Follow conventional commits:
```
feat: add git log parser
fix: correct spline interpolation at endpoints
docs: update CLAUDE.md with new guidelines
refactor: extract quadtree into separate module
test: add unit tests for Vec2 operations
```

## Troubleshooting

### WASM Build Fails
1. Ensure `wasm32-unknown-unknown` target is installed: `rustup target add wasm32-unknown-unknown`
2. Check `wasm-pack` version: `wasm-pack --version`
3. Try building without `wasm-opt`: add `wasm-opt = false` to `[package.metadata.wasm-pack.profile.release]`

### Performance Issues
1. Check if running debug build (use `--release`)
2. Profile with `cargo flamegraph` or browser DevTools
3. Verify spatial indexing is working
4. Check for excessive allocations

### Rendering Artifacts
1. Check coordinate system (Y-up vs Y-down)
2. Verify alpha blending order (back-to-front)
3. Check clip rectangle handling

## Reference Links

- Original Gource: https://github.com/acaudwell/Gource
- Gource Core Library: https://github.com/acaudwell/Core
- Rust WASM Book: https://rustwasm.github.io/docs/book/
- wasm-pack Docs: https://rustwasm.github.io/docs/wasm-pack/
- fontdue: https://github.com/mooman219/fontdue
- uniform-cubic-splines: https://docs.rs/uniform-cubic-splines

## Contact

This project uses Claude (AI assistant) for development assistance. When working with Claude:

1. Reference this document for project context
2. Run `source scripts/session-setup.sh` at the start of each session
3. Commit frequently with clear messages

---

*Last updated: 2026-01-22 (wgpu bind group caching for bloom/shadow - 1,094 tests)*
