# Rource Architecture

This document describes the high-level architecture of Rource, a Rust rewrite of Gource for software version control visualization.

## Overview

Rource is designed as a modular, multi-platform visualization system with three primary targets:
- **Native CLI** (`rource-cli`): Desktop application using `winit` + `softbuffer`
- **WebAssembly** (`rource-wasm`): Browser-based visualization with WebGL2/Canvas2D
- **Headless**: Server-side rendering for video export

```
┌───────────────────────────────────────────────────────────────────┐
│                         User Interface                            │
├─────────────────────┬─────────────────────┬───────────────────────┤
│     rource-cli      │     rource-wasm     │    Headless Mode      │
│   (Native Desktop)  │      (Browser)      │    (Video Export)     │
├─────────────────────┴─────────────────────┴───────────────────────┤
│                          rource-core                              │
│                    (Scene, Camera, Config)                        │
├───────────────────────────────────────────────────────────────────┤
│                         rource-render                             │
│             (Software Renderer, WebGL2 Renderer)                  │
├─────────────────────┬─────────────────────────────────────────────┤
│     rource-math     │                rource-vcs                   │
│   (Vec2, Mat4, etc) │     (Git, SVN, Custom format parsers)       │
└─────────────────────┴─────────────────────────────────────────────┘
```

## Crate Structure

### rource-math

Pure math library with no dependencies. Provides:
- Vector types: `Vec2`, `Vec3`, `Vec4`
- Matrix types: `Mat3`, `Mat4`
- Color representation: `Color` (RGBA)
- Geometric primitives: `Rect`, `Bounds`

**Design Decision**: We chose to implement our own math types rather than use `glam` or `nalgebra` to minimize dependencies and ensure WASM compatibility without feature flags.

### rource-vcs

Version control system log parsing with memory-efficient storage:

```
┌───────────────────────────────────────────────────────┐
│                      rource-vcs                       │
├─────────────────┬─────────────────┬───────────────────┤
│     Parsers     │  Compact Store  │  String Interning │
│                 │                 │                   │
│  • GitParser    │  • CommitStore  │  • StringInterner │
│  • SvnParser    │  • CompactCommit│  • PathInterner   │
│  • CustomParser │  • CompactChange│                   │
│  • BazaarParser │                 │                   │
├─────────────────┴─────────────────┴───────────────────┤
│                StreamingCommitLoader                  │
│            (Memory-efficient large repos)             │
└───────────────────────────────────────────────────────┘
```

**Key Features**:
- **String Interning**: Deduplicates repeated author names and path segments
- **Compact Storage**: 24 bytes per commit (vs ~72+ standard)
- **Streaming Parsing**: Process million-commit repos without loading all into memory

### rource-core

Core visualization logic independent of rendering:

```
┌───────────────────────────────────────────────────────┐
│                      rource-core                      │
├───────────────────────────┬───────────────────────────┤
│           Scene           │          Camera           │
│                           │                           │
│  • DirTree (hierarchy)    │  • 2D orthographic proj.  │
│  • FileNode (files)       │  • Smooth pan/zoom        │
│  • User (authors)         │  • Frustum culling        │
│  • Action (beams)         │  • Visible bounds calc    │
│  • Quadtree (spatial)     │                           │
├───────────────────────────┼───────────────────────────┤
│          Physics          │          Config           │
│                           │                           │
│  • Force-directed         │  • Settings struct        │
│  • Spring forces          │  • Environment variables  │
│  • Repulsion forces       │  • TOML config files      │
│  • Damping                │  • Filter patterns        │
└───────────────────────────┴───────────────────────────┘
```

**Scene Graph Architecture**:

```
Scene
├── DirTree (directory hierarchy)
│   ├── DirNode (root: /)
│   │   ├── DirNode (src/)
│   │   │   ├── FileNode (main.rs)
│   │   │   └── FileNode (lib.rs)
│   │   └── DirNode (tests/)
│   │       └── FileNode (test.rs)
│   └── ... (radial layout positions)
├── Users (HashMap<UserId, User>)
│   └── User { position, color, actions }
├── Actions (Vec<Action>)
│   └── Action { user → file, type, progress }
└── Quadtree (spatial index for culling)
```

### rource-render

Backend-agnostic rendering with multiple implementations:

```
┌───────────────────────────────────────────────────────┐
│                     rource-render                     │
├───────────────────────────────────────────────────────┤
│                    Renderer Trait                     │
│   • begin_frame() / end_frame()                       │
│   • draw_circle(), draw_line(), draw_text()           │
│   • Clip rectangles, alpha blending                   │
├───────────────────────────┬───────────────────────────┤
│    SoftwareRenderer       │      WebGl2Renderer       │
│                           │                           │
│  • Pure CPU rendering     │  • GPU-accelerated        │
│  • Xiaolin Wu AA          │  • Instanced rendering    │
│  • Bloom post-process     │  • GLSL ES 3.0 shaders    │
│  • Platform agnostic      │  • Font atlas texture     │
│                           │  • Context loss handling  │
└───────────────────────────┴───────────────────────────┘
```

### rource-cli

Native desktop application:

```
┌───────────────────────────────────────────────────────┐
│                       rource-cli                      │
├───────────────────────────────────────────────────────┤
│   main.rs       - Entry point, event loop             │
│   args.rs       - CLI argument parsing (clap)         │
│   window.rs     - Window creation, input handling     │
│   rendering.rs  - Scene to pixel rendering            │
│   avatar.rs     - User avatar image loading           │
│   headless.rs   - Batch video export mode             │
└───────────────────────────────────────────────────────┘
```

### rource-wasm

WebAssembly module for browser deployment:

```
┌───────────────────────────────────────────────────────┐
│                      rource-wasm                      │
├───────────────────────────────────────────────────────┤
│   lib.rs           - WASM entry, Rource class API     │
│   backend.rs       - RendererBackend abstraction      │
│   metrics.rs       - FPS tracking, render statistics  │
│   playback.rs      - Timeline management              │
│   interaction.rs   - Mouse/touch handling             │
│   render_phases.rs - Phased rendering pipeline        │
│   rendering.rs     - Splines, curves, visual helpers  │
│   png.rs           - Screenshot export                │
├───────────────────────────────────────────────────────┤
│   www/             - Web demo page                    │
│   ├── index.html   - Page structure                   │
│   ├── styles.css   - Responsive styling               │
│   └── js/          - Modular JavaScript (ES Modules)  │
│       ├── main.js       - Entry point                 │
│       ├── state.js      - Observable state            │
│       ├── animation.js  - Render loop                 │
│       └── features/     - Feature modules             │
└───────────────────────────────────────────────────────┘
```

## Data Flow

### Commit Processing Pipeline

```
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│ Git Log  │───▶│  Parser  │───▶│ Commit[] │───▶│  Scene   │
│  (text)  │    │          │    │          │    │ .apply() │
└──────────┘    └──────────┘    └──────────┘    └──────────┘
                                                     │
┌────────────────────────────────────────────────────────────┐
│                      Per-Frame Update                      │
├────────────────────────────────────────────────────────────┤
│   1. Apply pending commits (based on playback speed)       │
│   2. Update physics (force-directed layout)                │
│   3. Update entity animations (fade-in, pulse, etc.)       │
│   4. Update camera (smooth following, zoom)                │
│   5. Cull non-visible entities (frustum culling)           │
│   6. Render visible entities (files, users, connections)   │
└────────────────────────────────────────────────────────────┘
```

### Rendering Pipeline

```
┌────────────────────────────────────────────────────────────┐
│                      Frame Rendering                       │
├────────────────────────────────────────────────────────────┤
│   1. begin_frame()                                         │
│   2. clear(background_color)                               │
│   3. Calculate visible entities (quadtree query)           │
│   4. Render layers (back to front):                        │
│      a. Directory connections (tree branches)              │
│      b. Directory labels                                   │
│      c. Files (colored dots)                               │
│      d. Action beams (user → file connections)             │
│      e. Users (avatars/circles)                            │
│      f. User labels                                        │
│      g. File labels                                        │
│   5. Apply post-processing (bloom, if enabled)             │
│   6. end_frame()                                           │
│   7. present() (software) or implicit (WebGL)              │
└────────────────────────────────────────────────────────────┘
```

## Key Design Patterns

### 1. Entity-Component Pattern

Entities (files, users, directories) are identified by typed IDs:

```rust
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct FileId(u32, Generation);

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct UserId(u32, Generation);

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct DirId(u32, Generation);
```

The `Generation` component enables slot reuse without ABA problems.

### 2. Backend Abstraction

Rendering backends implement a common `Renderer` trait:

```rust
pub trait Renderer {
    fn begin_frame(&mut self);
    fn end_frame(&mut self);
    fn clear(&mut self, color: Color);
    fn draw_circle(&mut self, center: Vec2, radius: f32, color: Color);
    fn draw_line(&mut self, start: Vec2, end: Vec2, width: f32, color: Color);
    fn draw_text(&mut self, text: &str, pos: Vec2, size: f32, color: Color, font: FontId);
    // ... more primitives
}
```

### 3. Radial Tree Layout

Directories are positioned using a radial layout algorithm:

```
        Root (center)
             │
    ┌────────┼────────┐
    │        │        │
   src     tests    docs
   /│\       │        │
  / │ \      │        │
lib main utils  tests.rs  README.md
```

Each directory owns an angular sector, subdivided among children based on their "weight" (descendant count).

### 4. Force-Directed Layout

Files and directories use physics simulation:
- **Spring forces**: Pull connected entities together
- **Repulsion forces**: Push overlapping entities apart
- **Damping**: Prevents oscillation
- **Target positions**: Guide entities toward radial layout positions

## Memory Optimization

For large repositories (100k+ commits), we use:

1. **String Interning**: Shared strings for repeated author names and path segments
2. **Compact Commits**: 24-byte struct instead of ~72+ bytes
3. **Streaming Parsing**: Iterator-based processing without full memory load
4. **Spatial Indexing**: Quadtree for O(log n) visible entity queries

Benchmark (Home Assistant Core: 103k commits, 533k file changes):
- Standard Storage: 51.65 MB
- Compact Storage: 16.43 MB
- **Savings: 68.2%**

## Error Handling Strategy

- **Parse errors**: Return `Result<Vec<Commit>, ParseError>` with context
- **Render errors**: Log and continue (graceful degradation)
- **WebGL context loss**: Detect via `is_context_lost()`, recover with `recover_context()`
- **WASM panics**: `console_error_panic_hook` for browser debugging

## Testing Strategy

- **Unit tests**: Per-module, 650+ tests across crates
- **Integration tests**: End-to-end parsing and rendering
- **Visual tests**: Headless frame export for regression testing
- **Property tests**: Math operations with random inputs
- **Doc tests**: Examples in rustdoc comments

Total: **1,899 tests** across the codebase

## Future Considerations

1. **GPU Compute**: Use compute shaders for physics simulation
2. **LOD System**: Reduce detail for zoomed-out views
3. **Incremental Updates**: Only recompute affected subtrees
4. **WebGPU Backend**: When browser support matures
5. **Native GPU**: Vulkan/Metal backends via `wgpu`
