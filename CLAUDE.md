# CLAUDE.md - Rource Project Guide

This document provides context and guidance for Claude (AI assistant) when working on the Rource project.

## Project Overview

**Rource** (Rust + Gource) is a complete rewrite of [Gource](https://github.com/acaudwell/Gource), the software version control visualization tool, in Rust with WebAssembly support.

### Goals
- **Portable**: Run on any CPU architecture without requiring a dedicated GPU
- **Lightweight**: Minimal dependencies, small binary size (~2.5MB native, ~400KB WASM gzip)
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
│   ├── rource-vcs/       # VCS log parsing (Git, SVN, Custom format) [86 tests]
│   ├── rource-core/      # Core engine (scene, physics, animation, camera, config) [171 tests]
│   └── rource-render/    # Rendering (software rasterizer, bloom, shadows, fonts, text) [75 tests]
├── rource-cli/           # Native CLI application (winit + softbuffer) [29 tests]
└── rource-wasm/          # WebAssembly application (planned)
```

### Rendering Backends
1. **Software Rasterizer** - Pure CPU rendering, works everywhere
2. **WebGL2** - GPU-accelerated browser rendering (planned)
3. **Canvas2D** - Simple browser fallback (planned)

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
- [ ] WASM/Canvas2D
- [ ] WASM/WebGL2

## Recent Progress & Insights

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
3. Add WASM binding in `rource-wasm/src/lib.rs`
4. Update documentation

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

*Last updated: 2026-01-10 (Phase 6 complete - 554 tests)*
