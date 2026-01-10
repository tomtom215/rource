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

## Architecture

### Crate Structure

```
rource/
├── crates/
│   ├── rource-math/      # Math types (Vec2, Vec3, Vec4, Mat3, Mat4, Color, etc.) [141 tests]
│   ├── rource-vcs/       # VCS log parsing (Git, SVN, Custom format) [86 tests]
│   ├── rource-core/      # Core engine (scene, physics, animation, camera, config) [171 tests]
│   └── rource-render/    # Rendering (software rasterizer, bloom, shadows, fonts, text) [75 tests]
├── rource-cli/           # Native CLI application (winit + softbuffer) [8 tests]
└── rource-wasm/          # WebAssembly application (planned)
```

### Rendering Backends
1. **Software Rasterizer** - Pure CPU rendering, works everywhere
2. **WebGL2** - GPU-accelerated browser rendering
3. **Canvas2D** - Simple browser fallback

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
- [ ] WASM/Canvas2D
- [ ] WASM/WebGL2
- [ ] Video export

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
```

### WASM
- Use browser DevTools console
- Enable `console_error_panic_hook` for better panic messages
- Use `web-sys` console logging

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

*Last updated: 2026-01-10 (Phase 6 CLI in progress - 536 tests)*
