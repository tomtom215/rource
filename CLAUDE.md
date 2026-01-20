# CLAUDE.md - Rource Project Guide

This document provides context and guidance for Claude (AI assistant) when working on the Rource project.

## Project Overview

**Rource** (Rust + Gource) is a complete rewrite of [Gource](https://github.com/acaudwell/Gource), the software version control visualization tool, in Rust with WebAssembly support.

### Goals
- **Portable**: Run on any CPU architecture without requiring a dedicated GPU
- **Lightweight**: Minimal dependencies, small binary size (~2.5MB native, ~76KB WASM gzip)
- **Fast**: Leverage Rust's performance and modern rendering techniques
- **User-friendly**: Better UI/UX than original Gource
- **Feature-complete**: Maintain at minimum feature parity with Gource

### Key Documents
- `GOURCE_RUST_REWRITE_PLAN.md` - Comprehensive implementation plan (2,691 lines)
- `README.md` - Project overview and usage instructions
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
| Rust | 1.75+ | Core language |
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
│   ├── rource-math/      # Math types (Vec2, Vec3, Vec4, Mat3, Mat4, Color, etc.) [141 tests]
│   ├── rource-vcs/       # VCS log parsing (Git, SVN, Custom format, compact storage) [130 tests]
│   ├── rource-core/      # Core engine (scene, physics, animation, camera, config) [236 tests]
│   └── rource-render/    # Rendering (software rasterizer, WebGL2, bloom, shadows, fonts) [99 tests]
├── rource-cli/           # Native CLI application (winit + softbuffer) [41 tests]
└── rource-wasm/          # WebAssembly application [3 tests]
```

### Rendering Backends
1. **Software Rasterizer** - Pure CPU rendering, works everywhere (native and WASM)
2. **WebGL2 (WASM)** - GPU-accelerated browser rendering (default for WASM)
3. **Canvas2D (WASM)** - Software renderer + canvas ImageData (fallback)

The WASM build automatically tries WebGL2 first and falls back to software rendering
if WebGL2 is unavailable. You can check which renderer is active via `rource.getRendererType()`.

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

## Recent Progress & Insights

### WebAssembly Implementation (2026-01-10)

Successfully implemented WebAssembly support for running Rource in web browsers:

#### Implementation Details

1. **Architecture**: Uses software renderer with ImageData transfer to canvas
   - Reuses existing SoftwareRenderer for all drawing operations
   - Converts ARGB pixel buffer to RGBA for web canvas
   - ~76KB gzipped WASM bundle

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

### WebGL2 Backend Implementation (2026-01-11)

Successfully implemented GPU-accelerated WebGL2 rendering backend for WASM:

#### Architecture

```
crates/rource-render/src/backend/webgl2/
├── mod.rs          # WebGl2Renderer implementing Renderer trait
├── shaders.rs      # GLSL ES 3.0 shader sources
├── buffers.rs      # VBO/VAO management for instanced rendering
└── textures.rs     # Texture atlas for font glyphs
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
2. Point to `GOURCE_RUST_REWRITE_PLAN.md` for detailed implementation specs
3. Run `source scripts/session-setup.sh` at the start of each session
4. Commit frequently with clear messages

---

*Last updated: 2026-01-20 (Web UI modularized, 840+ tests)*
