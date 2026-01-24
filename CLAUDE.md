# CLAUDE.md - Rource Project Guide

This document provides context and guidance for Claude (AI assistant) when working on the Rource project.

---

## Table of Contents

1. [Project Overview](#project-overview)
2. [Quick Start](#quick-start)
3. [Architecture](#architecture)
4. [Development Guidelines](#development-guidelines)
5. [Performance Optimization Standards](#performance-optimization-standards)
6. [Common Tasks](#common-tasks)
7. [Testing & Validation](#testing--validation)
8. [CI/CD Pipeline](#cicd-pipeline)
9. [Debugging](#debugging)
10. [Dependencies Philosophy](#dependencies-philosophy)
11. [Git Workflow](#git-workflow)
12. [Troubleshooting](#troubleshooting)
13. [Reference Links](#reference-links)

---

## Project Overview

**Rource** (Rust + Gource) is a complete rewrite of [Gource](https://github.com/acaudwell/Gource), the software version control visualization tool, in Rust with WebAssembly support.

### Goals

| Goal             | Description                                               |
|------------------|-----------------------------------------------------------|
| **Portable**     | Run on any CPU architecture without requiring a dedicated GPU |
| **Lightweight**  | Minimal dependencies, small binary size (~3.8MB native, ~1MB WASM gzip) |
| **Fast**         | Leverage Rust's performance and modern rendering techniques |
| **User-friendly**| Better UI/UX than original Gource                         |
| **Feature-complete** | Maintain at minimum feature parity with Gource        |

### Key Documents

| Document           | Purpose                                |
|--------------------|----------------------------------------|
| `README.md`        | Project overview and usage instructions |
| `CONTRIBUTING.md`  | Development guidelines and code style  |
| `PERFORMANCE.md`   | Performance optimization changelog     |
| `docs/ALGORITHMIC_COMPLEXITY.md` | Big-O analysis of all functions |
| `LICENSE`          | GPL-3.0 license (same as original Gource) |

---

## Quick Start

### Session Setup

Before starting development, run the setup script:

```bash
source scripts/session-setup.sh
```

This script will:
1. Verify Rust and Cargo are installed
2. Install the `wasm32-unknown-unknown` target if missing
3. Install `wasm-pack` if missing
4. Ensure `clippy` and `rustfmt` are available

### Required Tools

| Tool      | Version | Purpose            |
|-----------|---------|-------------------|
| Rust      | 1.82+   | Core language      |
| Cargo     | Latest  | Package manager    |
| wasm-pack | 0.12+   | WASM bundling      |
| rustup    | Latest  | Toolchain management |

### Optional Tools

| Tool        | Purpose                        |
|-------------|--------------------------------|
| wasm-opt    | WASM binary optimization       |
| cargo-watch | Auto-rebuild on changes        |
| ffmpeg      | Convert PPM frames to video    |
| Python 3    | PPM file inspection scripts    |

### Running the Project

```bash
# Windowed mode (interactive)
cargo run --release -- .

# Headless mode (batch export)
cargo run --release -- --headless --output /tmp/frames --seconds-per-day 0.5 .

# With effects disabled for faster rendering
cargo run --release -- --headless --no-bloom --output /tmp/frames .
```

---

## Architecture

### Crate Structure

```
rource/
├── crates/
│   ├── rource-math/       # Math types (Vec2, Vec3, Vec4, Mat3, Mat4, Color)
│   ├── rource-vcs/        # VCS log parsing (Git, SVN, Custom, Mercurial, Bazaar)
│   ├── rource-core/       # Core engine (scene, physics, animation, camera, config)
│   └── rource-render/     # Rendering (software, WebGL2, wgpu, bloom, shadows)
├── rource-cli/            # Native CLI application (winit + softbuffer)
└── rource-wasm/           # WebAssembly application
```

**Test Count**: 1,899 tests total across all crates.

### Rendering Backends

| Backend            | Platform     | Description                                    |
|--------------------|--------------|------------------------------------------------|
| wgpu               | Native + WASM | Cross-platform GPU via WebGPU/Vulkan/Metal/DX12 |
| WebGL2             | WASM         | GPU-accelerated browser rendering (fallback)   |
| Software Rasterizer | All         | Pure CPU rendering, maximum compatibility      |

**Backend Priority:**
- Native: wgpu → Software
- WASM: wgpu (WebGPU) → WebGL2 → Software (Canvas2D)

The WASM build automatically tries backends in priority order. Check active renderer via `rource.getRendererType()`.

### Module Structure

#### Scene Module (`rource-core/src/scene/`)

| File                  | Purpose                                    |
|-----------------------|--------------------------------------------|
| `mod.rs`              | Scene struct, core methods                 |
| `action.rs`           | Action entities (beams)                    |
| `dir_node.rs`         | Directory node entities                    |
| `file.rs`             | File node entities                         |
| `tree.rs`             | Directory tree structure                   |
| `user.rs`             | User entities                              |
| `bounds_methods.rs`   | Entity bounds computation                  |
| `layout_methods.rs`   | Force-directed layout algorithm            |
| `spatial_methods.rs`  | Spatial index and visibility queries       |
| `stats_methods.rs`    | Extension statistics for legend            |

#### Render Backends (`rource-render/src/backend/`)

| Directory   | Purpose                                      |
|-------------|----------------------------------------------|
| `software/` | CPU-based software rasterizer                |
| `webgl2/`   | WebGL2 GPU renderer with bloom/shadow        |
| `wgpu/`     | wgpu GPU renderer with compute shaders       |

#### WASM API (`rource-wasm/src/wasm_api/`)

| File          | Purpose                          |
|---------------|----------------------------------|
| `authors.rs`  | Author list and statistics       |
| `cache.rs`    | Visualization cache (bitcode)    |
| `camera.rs`   | Camera control                   |
| `export.rs`   | Screenshot/video export          |
| `hover.rs`    | Entity hover detection           |
| `input.rs`    | Mouse/keyboard input handling    |
| `layout.rs`   | Layout configuration             |
| `playback.rs` | Playback control                 |
| `settings.rs` | Settings configuration           |
| `stats.rs`    | Statistics and metrics           |

### CLI and WASM Rendering Synchronization

**The CLI and WASM have separate rendering code that must be kept in sync.**

| Component  | Rendering Code Location                                    |
|------------|------------------------------------------------------------|
| Native CLI | `rource-cli/src/rendering.rs`                              |
| WASM       | `rource-wasm/src/lib.rs` (render method and helpers)       |

When making visual/rendering changes:
1. Update `rource-cli/src/rendering.rs` for the native CLI
2. **Also update** `rource-wasm/src/lib.rs` with the same changes
3. Rebuild WASM with `./scripts/build-wasm.sh`
4. Test both CLI and WASM to verify visual parity

### Coordinate System

| Space        | Description                                    |
|--------------|------------------------------------------------|
| World Space  | Entities live in coordinates centered at (0,0) |
| Screen Space | Top-left is (0,0), Y increases downward        |
| Transform    | `camera.world_to_screen(pos)` converts coordinates |

---

## Development Guidelines

### Code Style

- Use `cargo fmt` before committing
- Run `cargo clippy` and address warnings
- Follow Rust API guidelines: https://rust-lang.github.io/api-guidelines/

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

### General Performance Guidelines

- Use spatial hashing/quadtree for entity queries
- Batch rendering calls (instanced rendering)
- Implement LOD (Level of Detail) for zoomed-out views
- Stream commits for large repositories
- Use arena allocation for entities

---

## Performance Optimization Standards

**This project serves as the center showpiece of a professional portfolio and a publicly deployed WASM demo.** As such, we aim for **mathematical perfection** in all performance optimizations—measured, repeatable, verifiable, auditable, and documented improvements.

### Quality Bar

Every optimization must meet these standards:

| Criterion | Requirement |
|-----------|-------------|
| **Measurable** | Backed by criterion benchmarks with statistical significance |
| **Documented** | Added to `PERFORMANCE.md` with before/after measurements |
| **Correct** | All 1,899+ tests must pass |
| **Clean** | Clippy and rustfmt compliant |
| **Verifiable** | Benchmarks can be re-run to reproduce results |

### Optimization Philosophy

We pursue optimizations at the **nanosecond level** and **CPU cycle level**:

| Level | Examples |
|-------|----------|
| **Algorithmic** | O(n²) → O(n log n) via Barnes-Hut, spatial indexing |
| **Arithmetic** | Division → multiplication by reciprocal, sqrt elimination |
| **Memory** | Zero-allocation hot paths, arena allocation, buffer reuse |
| **Compile-time** | Lookup tables, const evaluation, precomputed constants |
| **Instruction** | Fixed-point arithmetic, bit shifts instead of division |

### Optimization Patterns

**Replace expensive operations with cheaper equivalents:**
```rust
// Before: expensive
let normalized = delta.normalized();  // sqrt + division

// After: reuse known length
let normalized = delta / known_length;  // division only
```

**Eliminate redundant calculations:**
```rust
// Before: sqrt computed twice
let length = dir.length();
let perp = Vec2::new(-dir.y, dir.x).normalized();  // same magnitude!

// After: perpendicular has same length, skip normalization
let perp = Vec2::new(-dir.y, dir.x);
```

**Use compile-time lookup tables:**
```rust
// Before: runtime division
let f = byte as f32 / 255.0;

// After: LUT access
static U8_TO_F32_LUT: [f32; 256] = { /* compile-time computed */ };
let f = U8_TO_F32_LUT[byte as usize];
```

**Replace allocations with iterators:**
```rust
// Before: allocates Vec
let parts: Vec<&str> = line.split('|').collect();

// After: zero allocation
let mut parts = line.split('|');
let first = parts.next()?;
```

### Optimization Methodology

Every optimization follows this rigorous process:

1. **Identify** - Profile, grep for patterns, analyze algorithmic complexity
2. **Benchmark** - Create criterion benchmarks measuring baseline performance
3. **Implement** - Make targeted changes with clear before/after comments
4. **Verify** - Run all tests, clippy, rustfmt
5. **Document** - Update `PERFORMANCE.md` with measurements and rationale
6. **Commit** - Clear commit message referencing phase number

### Benchmark Requirements

All benchmarks must:

- Use `criterion` for statistical rigor
- Test multiple input sizes/scenarios
- Report throughput (elements/second) where applicable
- Include both micro-benchmarks (isolated operation) and macro-benchmarks (realistic workload)
- Be reproducible across runs

Example benchmark structure:
```rust
fn benchmark_operation(c: &mut Criterion) {
    let mut group = c.benchmark_group("operation_name");
    group.throughput(Throughput::Elements(1000));

    group.bench_function("baseline", |b| {
        b.iter(|| baseline_implementation(black_box(input)))
    });

    group.bench_function("optimized", |b| {
        b.iter(|| optimized_implementation(black_box(input)))
    });

    group.finish();
}
```

### Documentation Format

Each optimization phase in `PERFORMANCE.md` must include:

1. **Overview** - What was optimized and why
2. **The Problem** - Code showing the inefficiency
3. **The Solution** - Optimized code with explanation
4. **Mathematical Proof** (if applicable) - Why the optimization is correct
5. **Benchmark Results** - Table with before/after measurements
6. **Files Modified** - What changed and where
7. **Correctness Verification** - How correctness was validated

### Current Optimization Phases

See [PERFORMANCE.md](./PERFORMANCE.md) for the complete optimization history (48+ phases), including:

- Fixed-point alpha blending (-21% batch, -81% same-color)
- Color conversion LUTs (-54% from_hex, -62% to_argb8)
- VCS parser zero-allocation (iterator-based parsing)
- Force normalization (eliminated redundant sqrt)
- Perpendicular vector optimization (-72% operation, +14% throughput)
- Barnes-Hut O(n log n) force layout
- And many more...

---

## Common Tasks

### Adding a New VCS Parser

1. Create `crates/rource-vcs/src/parser/newvcs.rs`
2. Implement the `Parser` trait (see `parser/mod.rs`)
3. Register in `crates/rource-vcs/src/detect.rs`
4. Add tests in the new parser file

### Adding a New Rendering Backend

1. Create `crates/rource-render/src/backend/newbackend/`
2. Implement the `Renderer` trait
3. Add feature flag in `Cargo.toml`
4. Update backend selection logic

### Adding a New Configuration Option

1. Add field to appropriate module in `rource-core/src/config/settings/`:

   | Module          | Settings Type                |
   |-----------------|------------------------------|
   | `camera.rs`     | Camera behavior              |
   | `display.rs`    | Display/visual               |
   | `playback.rs`   | Playback timing              |
   | `visibility.rs` | UI element visibility        |
   | `limits.rs`     | Performance limits           |
   | `input.rs`      | Input handling               |
   | `export.rs`     | Video/screenshot export      |
   | `title.rs`      | Title and captions           |
   | `directory.rs`  | Directory display            |
   | `layout.rs`     | Radial tree layout           |
   | `overlay.rs`    | Logo/background overlays     |
   | `filter.rs`     | User/file filtering          |

2. Add CLI argument in `rource-cli/src/args/mod.rs`
3. Add environment variable in `rource-core/src/config/config_env.rs`
4. Add WASM binding in `rource-wasm/src/wasm_api/settings.rs`
5. Update documentation

### Environment Variable Configuration

Settings can be configured via environment variables with the `ROURCE_` prefix:

```bash
export ROURCE_WIDTH=1920
export ROURCE_HEIGHT=1080
export ROURCE_BLOOM_ENABLED=false
export ROURCE_SECONDS_PER_DAY=5.0
export ROURCE_TITLE="My Project"
export ROURCE_HIDE_USERS="bot.*"
```

**Configuration priority** (highest to lowest):
1. CLI arguments
2. Environment variables
3. Config file (`--config`)
4. Defaults

Boolean values accept: `1/true/yes/on` for true, `0/false/no/off` for false.

---

## Testing & Validation

### Pre-Commit Checklist

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

### Determinism Requirements

For 100% deterministic output:

1. **Use fixed time step**: In headless mode, use `dt = 1.0 / framerate` instead of real delta time
2. **Seed random generators**: Any randomness should use a fixed seed
3. **Pre-warm the scene**: Apply first commit and run ~30 update cycles before first render
4. **Force camera position**: Use `jump_to()` + `set_zoom()` instead of smooth transitions

---

## CI/CD Pipeline

The project uses GitHub Actions for CI/CD.

### Workflow Overview

| Workflow       | File               | Purpose                              |
|----------------|--------------------|--------------------------------------|
| CI             | `ci.yml`           | Core quality gates                   |
| Coverage       | `coverage.yml`     | Code coverage with Codecov           |
| Benchmarks     | `bench.yml`        | Performance regression detection     |
| Integration    | `integration.yml`  | Headless rendering tests             |
| Security       | `security.yml`     | Audits, license checks               |
| Release        | `release.yml`      | Multi-platform builds, signing       |
| Docker         | `docker.yml`       | Multi-arch container images          |
| Deploy Pages   | `deploy-pages.yml` | GitHub Pages deployment              |

### CI Jobs

| Job           | Description                              |
|---------------|------------------------------------------|
| Format        | `cargo fmt --check`                      |
| Clippy        | All lints with `-D warnings`             |
| Test          | Multi-platform (Linux, macOS, Windows)   |
| MSRV          | Minimum Supported Rust Version (1.82)    |
| Build Native  | Release binary with size report          |
| Build WASM    | WebAssembly with gzip size check         |
| Documentation | Rustdoc with warning-as-error            |

### Local CI Verification

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

### Required Secrets

| Secret            | Purpose               | Required    |
|-------------------|-----------------------|-------------|
| `GITHUB_TOKEN`    | Automatic             | Yes (auto)  |
| `GPG_PRIVATE_KEY` | Release signing       | Optional    |
| `GPG_PASSPHRASE`  | GPG key passphrase    | Optional    |
| `CODECOV_TOKEN`   | Coverage uploads      | Optional    |

---

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

### Observability

```rust
// Debug output for troubleshooting:
eprintln!("files={}, users={}, camera=({:.1},{:.1}), zoom={:.3}",
    scene.file_count(), scene.user_count(),
    camera.position().x, camera.position().y, camera.zoom());

// Check pixel output:
let non_black = pixels.iter().filter(|&&p| p != 0xFF000000).count();
eprintln!("Frame {}: {} non-black pixels", frame, non_black);
```

---

## Dependencies Philosophy

We minimize external dependencies to:
- Reduce binary size
- Improve compile times
- Ensure WASM compatibility
- Avoid security surface area

### Approved Dependencies

| Crate         | Reason                         |
|---------------|--------------------------------|
| `fontdue`     | Best pure-Rust font rasterizer |
| `regex-lite`  | Lighter than `regex`, no PCRE  |
| `chrono`      | Date/time handling             |
| `wasm-bindgen`| Required for WASM              |
| `clap`        | CLI only, feature-gated        |

### Avoid

- Heavy GUI frameworks (egui, iced) - we do custom rendering
- Full `image` crate - use minimal decoders
- `tokio`/`async-std` - synchronous design is simpler
- `serde` for core (optional for config files)

---

## Git Workflow

### Branches

| Branch       | Purpose                    |
|--------------|----------------------------|
| `main`       | Stable releases            |
| `develop`    | Integration branch         |
| `feature/*`  | New features               |
| `fix/*`      | Bug fixes                  |
| `claude/*`   | AI-assisted development    |

### Commit Messages

Follow conventional commits:

```
feat: add git log parser
fix: correct spline interpolation at endpoints
docs: update CLAUDE.md with new guidelines
refactor: extract quadtree into separate module
test: add unit tests for Vec2 operations
perf: optimize bloom effect with sliding window blur
```

---

## Troubleshooting

### Common Issues

| Symptom                      | Cause                        | Solution                                      |
|------------------------------|------------------------------|-----------------------------------------------|
| Black frames                 | Files haven't faded in       | Pre-warm scene with 30 update cycles          |
| Infinite loop                | Wrong termination condition  | Check `current_commit >= commits.len().saturating_sub(1)` |
| Camera shows empty area      | Using quadtree bounds        | Use `compute_entity_bounds()` instead         |
| Files at wrong position      | Camera not updated           | Call `camera.update(dt)` each frame           |
| UI clicks do nothing         | Duplicate event handlers     | Use single handler via consolidated function  |
| GitHub fetch fails silently  | Error swallowed in catch     | Always show error via toast and update status |
| WASM visuals don't match CLI | Rendering code not synced    | Update both CLI and WASM rendering code       |
| Screenshot blank/corrupted   | Animation loop races         | Stop animation before capture                 |

### WASM Build Fails

1. Ensure `wasm32-unknown-unknown` target is installed:
   ```bash
   rustup target add wasm32-unknown-unknown
   ```
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

---

## Reference Links

| Resource                | URL                                              |
|-------------------------|--------------------------------------------------|
| Original Gource         | https://github.com/acaudwell/Gource              |
| Gource Core Library     | https://github.com/acaudwell/Core                |
| Rust WASM Book          | https://rustwasm.github.io/docs/book/            |
| wasm-pack Docs          | https://rustwasm.github.io/docs/wasm-pack/       |
| fontdue                 | https://github.com/mooman219/fontdue             |
| uniform-cubic-splines   | https://docs.rs/uniform-cubic-splines            |

---

## Contact

This project uses Claude (AI assistant) for development assistance. When working with Claude:

1. Reference this document for project context
2. Run `source scripts/session-setup.sh` at the start of each session
3. Commit frequently with clear messages
4. See [PERFORMANCE.md](./PERFORMANCE.md) for optimization history

---

*Last updated: 2026-01-24*
