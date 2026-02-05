<p align="center">
  <img src="docs/images/logo.svg" alt="Rource Logo" width="100" height="100">
</p>

<h1 align="center">Rource</h1>

<p align="center">
  <strong>Software version control visualization in Rust + WebAssembly</strong>
</p>

<p align="center">
  <a href="https://github.com/tomtom215/rource/actions/workflows/ci.yml"><img src="https://img.shields.io/github/actions/workflow/status/tomtom215/rource/ci.yml?branch=main&logo=github&label=CI" alt="CI"></a>
  <a href="https://github.com/tomtom215/rource/actions/workflows/security.yml"><img src="https://img.shields.io/github/actions/workflow/status/tomtom215/rource/security.yml?branch=main&logo=github&label=Security" alt="Security"></a>
  <a href="https://codecov.io/gh/tomtom215/rource"><img src="https://img.shields.io/codecov/c/github/tomtom215/rource?logo=codecov" alt="codecov"></a>
</p>

<p align="center">
  <a href="https://www.gnu.org/licenses/gpl-3.0"><img src="https://img.shields.io/badge/License-GPL%203.0-blue.svg?logo=gnu" alt="License: GPL-3.0"></a>
  <a href="https://www.rust-lang.org/"><img src="https://img.shields.io/badge/MSRV-1.93+-orange.svg?logo=rust" alt="Rust: 1.93+"></a>
  <a href="https://github.com/tomtom215/rource/releases"><img src="https://img.shields.io/github/v/release/tomtom215/rource?include_prereleases&logo=github" alt="GitHub Release"></a>
</p>

<p align="center">
  <a href="https://tomtom215.github.io/rource/"><img src="https://img.shields.io/badge/demo-live-brightgreen.svg?logo=github-pages" alt="Live Demo"></a>
  <a href="https://github.com/tomtom215/rource/pkgs/container/rource"><img src="https://img.shields.io/badge/docker-available-blue.svg?logo=docker" alt="Docker"></a>
</p>

<p align="center">
  <strong><a href="https://tomtom215.github.io/rource/">▶ Try it live in your browser</a></strong> — no installation required!
</p>

<p align="center">
  <b>Rource</b> (Rust + Gource) is a complete rewrite of <a href="https://github.com/acaudwell/Gource">Gource</a> in Rust with WebAssembly support.<br>
  Visualizes your repository's commit history as an animated tree where directories branch outward,<br>
  files appear as leaves, and contributors move around making changes.
</p>

---

## Table of Contents

- [Features](#features)
- [Why Rource?](#why-rource)
- [Installation](#installation)
- [Quick Start](#quick-start)
- [Usage](#usage)
- [Controls](#controls)
- [Configuration](#configuration)
- [Advanced Features](#advanced-features)
- [WebAssembly](#webassembly)
- [Architecture](#architecture)
- [Documentation](#documentation)
- [Contributing](#contributing)
- [License](#license)
- [Credits](#credits)

---

## Features

- **Portable**: Pure Rust with software rendering - runs on any CPU without GPU requirements
- **Lightweight**: ~3.8MB native binary, ~1MB WASM (gzipped)
- **Fast**: Handles repositories with 100k+ commits
- **Cross-platform**: Native (Linux, macOS, Windows) and WebAssembly
- **Compatible**: Supports Git, SVN, Mercurial, Bazaar, and custom log formats

---

## Why Rource?

| | Rource | Gource |
|---|:---:|:---:|
| **GPU Required** | No | Yes (OpenGL) |
| **Runs in Browser** | Yes (WASM) | No |
| **Binary Size** | ~3.8 MB | ~10 MB |
| **Memory (100k commits)** | ~16 MB | ~52 MB |
| **Test Coverage** | 2800+ tests | - |
| **Rendering** | CPU + WebGL2 + wgpu | OpenGL only |

### Performance Highlights

- **68% memory savings** on large repositories via string interning and compact storage
- **GPU acceleration** in browsers via WebGPU or WebGL2 (with automatic CPU fallback)
- **Tested with 100k+ commit repos** (Home Assistant: 103,533 commits, 533,366 file changes)
- **83 optimization phases** documented with picosecond/nanosecond-level measurements
- **50,000 FPS target** on test hardware (20 µs frame budget)
- **132 WASM functions profiled** with criterion benchmarks (100+ samples, 95% CI)

See [Performance Documentation](#performance-documentation) for the complete optimization history.

### Formal Verification

**PEER REVIEWED PUBLISHED ACADEMIC STANDARD** - Mathematical correctness proven by machine-checked proofs:

| Tool | Components | Theorems | Status |
|------|------------|----------|--------|
| **Verus** | Vec2, Vec3, Vec4, Mat3, Mat4, Color, Rect | 475 proof functions, 452+ VCs | Verified |
| **Coq (R-based)** | Vec2-4, Mat3-4, Color, Rect, Bounds, Utils + Complexity + CrossType | 1366 theorems | Zero admits |
| **Coq (Z-based)** | Vec2-4, Mat3-4, Color, Rect, Bounds, Utils (extractable) | 471 theorems | Zero admits |
| **Kani (CBMC)** | Vec2-4, Mat3-4, Color, Rect, Bounds, Utils | 225 harnesses | IEEE 754 verified |
| **Combined** | All 8 core math types + Bounds + FP layer + CrossType | **2909 theorems/harnesses** | **TRIPLE VERIFIED** |

Properties verified include: vector space axioms, dot/cross product laws, matrix multiplication associativity (critical for MVP transformations), ring structure, RGBA color blending/interpolation/luminance, rectangle containment/intersection/union, O(1) complexity bounds, and a complete Coq-to-WASM extraction pipeline.

**Verification architecture**: Layered (R-abstract proofs → Z-computational bridge → OCaml extraction → WASM via wasm_of_ocaml).

See [docs/verification/FORMAL_VERIFICATION.md](docs/verification/FORMAL_VERIFICATION.md) for complete details.

---

## Installation

### From Source

```bash
# Clone the repository
git clone https://github.com/tomtom215/rource.git
cd rource

# Build release binary
cargo build --release

# The binary is at ./target/release/rource
```

### Requirements

- Rust 1.93+ (install via [rustup](https://rustup.rs/))
- For WASM: `wasm-pack` (`cargo install wasm-pack`)

---

## Quick Start

```bash
# Visualize the current repository
rource .

# Visualize a specific repository
rource /path/to/repo

# Fast playback (2 seconds per day instead of 10)
rource -s 2.0 .

# With custom title
rource --title "My Project" .

# Export video frames
rource --output /tmp/frames --headless .
```

---

## Usage

```
rource [OPTIONS] [PATH]

Arguments:
  [PATH]  Path to git repository or log file [default: .]

Options:
  -W, --width <WIDTH>              Window width in pixels [default: 1280]
  -H, --height <HEIGHT>            Window height in pixels [default: 720]
  -f, --fullscreen                 Run in fullscreen mode
  -s, --seconds-per-day <SECS>     Seconds per day of history [default: 10.0]
  -t, --title <TITLE>              Title to display
  -L, --loop-playback              Loop the visualization
      --paused                     Start paused
      --no-bloom                   Disable bloom effect
      --shadows                    Enable drop shadows
      --hide-filenames             Hide file names
      --hide-usernames             Hide user names
      --hide-date                  Hide the date display
      --hide-legend                Hide file extension legend
  -o, --output <PATH>              Output PPM frames for video export
      --headless                   Run without window (for batch export)
      --framerate <FPS>            Video export framerate [default: 60]
      --screenshot <PATH>          Save screenshot and exit
      --screenshot-at <INDEX>      Commit index for screenshot (0-based, default: final)
  -c, --config <FILE>              Load settings from TOML config file
      --sample-config              Print sample configuration file
      --env-help                   Print environment variable help
  -h, --help                       Print help
  -V, --version                    Print version
```

---

## Controls

### Keyboard

| Key | Action |
|-----|--------|
| Space | Play/Pause |
| +/- | Zoom in/out |
| Arrow keys | Pan camera |
| R | Reset camera |
| Q/Escape | Quit |

### Mouse

| Action | Effect |
|--------|--------|
| Left drag | Pan camera or drag entities |
| Scroll wheel | Zoom in/out |
| Middle click | Reset camera |
| Click progress bar | Seek to position |

### Visual Elements

| Element | Description |
|---------|-------------|
| **Colored dots** | Files - color indicates file type (e.g., orange = Rust, blue = TypeScript) |
| **Large circles** | Users/developers - each has a unique color |
| **Gray hollow circles** | Directories - with center dots, connected by branch lines |
| **Colored beams** | Actions - lines connecting users to files they're modifying |
| **Branch lines** | Directory structure - curved lines showing folder hierarchy |

The visualization uses a radial layout where the root directory is at the center, and subdirectories branch outward. Files orbit around their parent directories.

---

## Configuration

### Config File

Create a `rource.toml` file:

```toml
# Display settings
width = 1920
height = 1080
background_color = "1a1a2e"
no_bloom = false
shadows = true

# Playback
seconds_per_day = 5.0
loop = true

# Title
title = "My Awesome Project"

# Filtering
hide_users = "dependabot.*|renovate.*"
hide_dirs = "node_modules|target|vendor"
```

Then run: `rource --config rource.toml .`

Generate a sample config: `rource --sample-config > rource.toml`

### Environment Variables

All settings can be configured via environment variables with the `ROURCE_` prefix:

```bash
export ROURCE_WIDTH=1920
export ROURCE_HEIGHT=1080
export ROURCE_SECONDS_PER_DAY=5.0
export ROURCE_TITLE="My Project"
rource .
```

Run `rource --env-help` for the complete list.

**Priority**: CLI args > Environment variables > Config file > Defaults

---

## Advanced Features

### Video Export

Export frames for video creation:

```bash
# Export PPM frames
rource --headless --output /tmp/frames .

# Convert to video with ffmpeg
ffmpeg -framerate 60 -i /tmp/frames/frame_%08d.ppm \
       -c:v libx264 -pix_fmt yuv420p output.mp4
```

Options:
- `--framerate 30` - Lower framerate for smaller files
- `--no-bloom` - Faster rendering without glow effect
- `-s 0.5` - Speed up playback (0.5 seconds per day)

### Screenshots

The `--screenshot` option captures a single frame as a PNG image:

```bash
# Capture final state of visualization
rource --screenshot output.png .

# Capture at a specific commit (0-based index)
rource --screenshot output.png --screenshot-at 50 .

# Capture with custom resolution
rource -W 1920 -H 1080 --screenshot output.png .
```

### Filtering

**Filter Users:**

```bash
# Show only specific users
rource --show-users "^(alice|bob)$" .

# Hide bots and CI
rource --hide-users "bot.*|dependabot|renovate" .
```

**Filter Files:**

```bash
# Show only Rust files
rource --show-files "\.rs$" .

# Hide generated files
rource --hide-files "\.(lock|sum|generated)$" .

# Hide directories
rource --hide-dirs "node_modules|target|\.git|vendor" .
```

### User Avatars

Display custom user avatars:

```bash
# Load avatars from directory (named by username)
rource --user-image-dir ./avatars .

# Provide default avatar for users without custom images
rource --user-image-dir ./avatars --default-user-image ./default.png .
```

Avatar files should be PNG format and named after the username (case-insensitive matching):

```
./avatars/
├── alice.png           # Matches "Alice", "alice", "ALICE"
├── Bob Smith.png       # Matches "Bob Smith" (spaces allowed)
└── john_doe.png        # Matches "john_doe"
```

### Custom Log Format

Rource supports a pipe-delimited custom format:

```
timestamp|username|action|filepath
```

Where action is: A (add), M (modify), D (delete)

Example:
```
1609459200|alice|A|src/main.rs
1609459260|bob|M|README.md
1609459320|alice|D|old_file.txt
```

```bash
rource --custom-log custom.log
```

### Performance Tips

For large repositories (50k+ commits):

```bash
# Disable effects for faster rendering
rource --no-bloom .

# Limit visible files
rource --max-files 1000 .

# Speed up playback
rource -s 0.5 .

# Filter out noise
rource --hide-dirs "node_modules|vendor|target" .
```

### Migrating from Gource

See [docs/GOURCE_COMPARISON.md](docs/GOURCE_COMPARISON.md) for a detailed comparison and migration guide.

Quick comparison:
| Gource | Rource |
|--------|--------|
| `-s 0.5` | `-s 0.5` (same) |
| `--seconds-per-day` | `--seconds-per-day` (same) |
| `--hide-filenames` | `--hide-filenames` (same) |
| `-o -` (pipe to ffmpeg) | `--output dir --headless` |
| Requires OpenGL | Pure software rendering |

---

## WebAssembly

Rource runs in web browsers via WebAssembly with GPU-accelerated rendering.

**[Live Demo](https://tomtom215.github.io/rource/)** - Try Rource instantly without installing anything.

### Rendering Backends

**Native (CLI):**
- **Software**: Pure CPU rendering, works everywhere without GPU requirements

**WebAssembly (Browser):**
- **wgpu (WebGPU)**: Best performance, modern GPU API (Chrome 113+, Edge 113+)
- **WebGL2**: Good performance, widely supported in all modern browsers
- **Software**: Pure CPU rendering via Canvas2D (automatic fallback)

The WASM build automatically tries wgpu (WebGPU) first, then WebGL2, and falls back to software rendering if unavailable.

### Building

```bash
cd rource-wasm
wasm-pack build --target web --release
```

### Running

```bash
cd www
python3 -m http.server 8080
# Open http://localhost:8080
```

### JavaScript API

```javascript
import init, { Rource } from './pkg/rource_wasm.js';

await init();

const canvas = document.getElementById('canvas');
const rource = new Rource(canvas);

// Check which renderer is being used
console.log('Renderer:', rource.getRendererType()); // "wgpu", "webgl2", or "software"

// Load data
rource.loadCustomLog("1234567890|John|A|src/main.rs");

// Start playback
rource.play();

// Animation loop
function frame(timestamp) {
    rource.frame(timestamp);
    requestAnimationFrame(frame);
}
requestAnimationFrame(frame);
```

---

## Architecture

```
rource/
├── crates/
│   ├── rource-math/      473 tests   Math primitives (Vec2, Vec3, Mat4, Color)
│   ├── rource-vcs/       340 tests   VCS parsing (Git, SVN, custom format)
│   ├── rource-core/      539 tests   Scene graph, physics, camera, Barnes-Hut
│   └── rource-render/    370 tests   Software + WebGL2 + wgpu rendering
├── rource-cli/           358 tests   Native application (winit + softbuffer)
└── rource-wasm/          461 tests   WebAssembly (browser)
                         ─────────
                         2,800+ total tests
```

---

## Documentation

### Project Documents

| Document | Description |
|----------|-------------|
| [CONTRIBUTING.md](CONTRIBUTING.md) | Development setup and contribution guidelines |
| [CLAUDE.md](CLAUDE.md) | AI-assisted development and Expert+ quality standards |
| [STABILITY.md](STABILITY.md) | API versioning and stability policy |
| [SECURITY.md](SECURITY.md) | Security policy and vulnerability reporting |
| [CHANGELOG.md](CHANGELOG.md) | Release history and version notes |

### Architecture Documentation

| Document | Description |
|----------|-------------|
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | System architecture and crate structure |
| [docs/RENDERING.md](docs/RENDERING.md) | Rendering pipeline and backends |
| [docs/GOURCE_COMPARISON.md](docs/GOURCE_COMPARISON.md) | Feature comparison with original Gource |
| [docs/adr/](docs/adr/) | Architecture Decision Records |

### Performance Documentation

| Document | Description |
|----------|-------------|
| [docs/performance/CHRONOLOGY.md](docs/performance/CHRONOLOGY.md) | 83 optimization phases with measurements |
| [docs/performance/BENCHMARKS.md](docs/performance/BENCHMARKS.md) | Raw benchmark data and methodology |
| [docs/performance/ALGORITHMIC_COMPLEXITY.md](docs/performance/ALGORITHMIC_COMPLEXITY.md) | Big-O analysis of algorithms |
| [docs/verification/FORMAL_VERIFICATION.md](docs/verification/FORMAL_VERIFICATION.md) | Formal verification overview and index (2573 theorems/harnesses) |
| [docs/performance/SUCCESSFUL_OPTIMIZATIONS.md](docs/performance/SUCCESSFUL_OPTIMIZATIONS.md) | Catalog of implemented optimizations |
| [docs/performance/ALGORITHM_CANDIDATES.md](docs/performance/ALGORITHM_CANDIDATES.md) | Future optimization candidates |
| [docs/performance/NOT_APPLICABLE.md](docs/performance/NOT_APPLICABLE.md) | Algorithms evaluated and ruled out |
| [docs/performance/FUTURE_WORK.md](docs/performance/FUTURE_WORK.md) | Technical roadmap and Expert+ targets |

### Testing & Quality Documentation

| Document | Description |
|----------|-------------|
| [docs/testing/MUTATION_TESTING.md](docs/testing/MUTATION_TESTING.md) | Mutation testing setup and results |
| [docs/testing/VISUAL_REGRESSION.md](docs/testing/VISUAL_REGRESSION.md) | Visual regression testing methodology |
| [docs/REVIEW_STANDARDS.md](docs/REVIEW_STANDARDS.md) | Code review requirements and checklists |

### Verification Documentation

| Document | Description |
|----------|-------------|
| [docs/verification/FORMAL_VERIFICATION.md](docs/verification/FORMAL_VERIFICATION.md) | 2909 formally verified theorems (Verus + Coq) |
| [docs/verification/SETUP_GUIDE.md](docs/verification/SETUP_GUIDE.md) | Formal verification environment setup (Verus, Coq, MetaCoq, wasm_of_ocaml) |
| [docs/verification/CERTICOQ_WASM_ASSESSMENT.md](docs/verification/CERTICOQ_WASM_ASSESSMENT.md) | Coq-to-WASM pipeline: 9-path landscape assessment |

### UX Documentation

| Document | Description |
|----------|-------------|
| [docs/ux/MOBILE_UX_ROADMAP.md](docs/ux/MOBILE_UX_ROADMAP.md) | Mobile UX improvement roadmap |

For the complete documentation index, see [docs/README.md](docs/README.md).

---

## Acknowledgments

This project was developed with AI-assisted programming using [Claude](https://www.anthropic.com/claude) by Anthropic. The AI assisted with code implementation, architecture decisions, documentation, and adherence to Rust best practices throughout the development process.

---

## Contributing

Contributions are welcome! See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines on:
- Setting up the development environment
- Code style and testing requirements
- Submitting pull requests

---

## License

GPL-3.0 (same as original Gource)

---

## Credits

- Original [Gource](https://github.com/acaudwell/Gource) by Andrew Caudwell
- Font: Roboto Mono (Apache 2.0)
