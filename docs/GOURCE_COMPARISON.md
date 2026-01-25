# Gource Comparison

Rource is a complete Rust rewrite of [Gource](https://github.com/acaudwell/Gource). This document tracks feature parity, performance comparisons, and CLI compatibility.

---

## Table of Contents

1. [Key Differences](#key-differences)
2. [Feature Parity Status](#feature-parity-status)
3. [Remaining Roadmap](#remaining-roadmap)
4. [Performance Comparison](#performance-comparison)
5. [CLI Compatibility](#cli-compatibility)
6. [VCS Support](#vcs-support)

---

## Key Differences

| Aspect | Gource | Rource |
|--------|--------|--------|
| Language | C++ | Rust |
| GPU Required | Yes (OpenGL) | No (software rendering available) |
| Binary Size | ~10MB | ~2.5MB native, ~1MB WASM gzip |
| WASM Support | No | Yes |
| Dependencies | SDL2, FTGL, PCRE, Boost, etc. | Minimal (pure Rust) |
| Portability | OpenGL platforms only | Any CPU architecture |
| Config Format | Key-value | TOML |
| Environment Variables | No | Yes (`ROURCE_*` prefix) |

---

## Feature Parity Status

### Fully Implemented

| Feature | Status | Notes |
|---------|--------|-------|
| Interactive mode | Done | Full mouse/keyboard support |
| Video export | Done | PPM frames + ffmpeg workflow |
| Screenshot | Done | `--screenshot` option |
| Fullscreen | Done | `-f` flag |
| Custom title | Done | `--title` option |
| Date overlay | Done | HUD display |
| User filtering | Done | Enhanced: `--hide-users`, `--show-users` |
| File filtering | Done | Enhanced: `--hide-files`, `--show-files` |
| Directory filtering | Done | New: `--hide-dirs` (not in Gource) |
| User avatars | Done | PNG format |
| Auto-skip idle | Done | Configurable |
| Camera modes | Done | Multiple modes |
| Bloom effect | Done | `--no-bloom` to disable |
| Shadows | Done | `--shadows` to enable |
| Elasticity | Done | Physics simulation |
| Config file | Done | TOML format |
| Custom log format | Done | `--custom-log` |

### Rource-Only Features

| Feature | Description |
|---------|-------------|
| WASM/Browser support | Run in any modern browser |
| Environment variables | `ROURCE_*` configuration |
| Software rendering | No GPU required |
| Directory filtering | `--hide-dirs` pattern matching |
| Show filters | Whitelist mode (`--show-users`, `--show-files`) |

---

## Remaining Roadmap

Features needed for 100% Gource feature parity:

| Feature | Priority | Complexity | Notes |
|---------|----------|------------|-------|
| Background image | Medium | Low | `--background-image` overlay |
| Logo overlay | Medium | Low | `--logo` positioning |
| Caption files | Low | Medium | Timed text overlays |
| Highlight users | Low | Low | `--highlight-users` visual emphasis |
| Multi-monitor | Low | Medium | Span across displays |
| CVS support | Low | Medium | Legacy VCS parser |
| Font color option | Low | Low | `--font-colour` equivalent |

**Current parity: ~85%** (all core visualization features complete)

---

## Performance Comparison

> **Note**: These benchmarks require re-verification with current codebase. Last validated against Gource 0.54.

### Frame Rate Comparison

| Repository Size | Gource | Rource | Notes |
|-----------------|--------|--------|-------|
| Small (<1k commits) | 60+ fps | 60+ fps | Both smooth |
| Medium (1k-10k commits) | 60+ fps | 60+ fps | Both smooth |
| Large (10k-100k commits) | GPU-dependent | 30-60 fps | Rource uses CPU |
| Very large (100k+) | May struggle | Works with filters | Use `--max-files` |

### Resource Usage

| Metric | Gource | Rource |
|--------|--------|--------|
| GPU memory | Required | Optional |
| CPU usage (idle) | Low | Low |
| CPU usage (active) | Medium | Higher (software render) |
| RAM (10k files) | ~200MB | ~150MB |

### Optimization Tips for Large Repos

```bash
# Reduce visual complexity
rource --no-bloom --hide-dirs "node_modules|vendor|target" .

# Limit concurrent files
rource --max-files 1000 -s 0.5 .

# Use faster playback
rource --seconds-per-day 0.1 --auto-skip-seconds 1 .
```

---

## CLI Compatibility

### Identical Options

These work the same in both tools:

```bash
-s, --seconds-per-day VALUE
--title "Project Name"
-f, --fullscreen
--hide-filenames
--hide-usernames
--hide-date
--start-date YYYY-MM-DD
--stop-date YYYY-MM-DD
--user-image-dir PATH
--default-user-image PATH
```

### Changed Options

| Gource | Rource | Notes |
|--------|--------|-------|
| `-o video.mp4` | `--output dir --headless` | Outputs PPM frames |
| `--output-ppm-stream -` | `--output - --headless` | Pipe to stdout |
| `--output-framerate 30` | `--framerate 30` | Shorter name |
| `-1280x720` | `-W 1280 -H 720` | Separate options |
| `--viewport WxH` | `-W width -H height` | Separate options |
| `--background-colour` | `--background-color` | American spelling |
| `--user-filter` | `--hide-users` | Clearer naming |
| `--file-filter` | `--hide-files` | Clearer naming |
| `--loop` | `-L, --loop-playback` | Explicit flag |

### Video Export Workflow

**Gource (direct)**:
```bash
gource -o - | ffmpeg -i - -c:v libx264 output.mp4
```

**Rource (frames)**:
```bash
rource --headless --output /tmp/frames .
ffmpeg -framerate 60 -i /tmp/frames/frame_%08d.ppm \
       -c:v libx264 -pix_fmt yuv420p output.mp4
```

**Rource (piped)**:
```bash
rource --headless --output - . | \
  ffmpeg -f image2pipe -framerate 60 -i - \
         -c:v libx264 -pix_fmt yuv420p output.mp4
```

---

## VCS Support

| VCS | Gource | Rource | Notes |
|-----|--------|--------|-------|
| Git | Yes | Yes | Full support |
| SVN | Yes | Yes | Full support |
| Mercurial | Yes | Yes | Full support |
| Bazaar | Yes | Yes | Full support |
| CVS | Yes | Not yet | Roadmap item |
| Custom log | Yes | Yes | `--custom-log` |

### Custom Log Format

Both use identical pipe-delimited format:

```
timestamp|username|action|filepath
```

- `timestamp`: Unix timestamp (seconds)
- `username`: Author name
- `action`: `A` (add), `M` (modify), `D` (delete)
- `filepath`: Path relative to repository root

---

## Visual Differences

### Rendering Approach

- **Gource**: Hardware-accelerated OpenGL
- **Rource**: Software rasterizer (default), wgpu, or WebGL2

Visual output is similar but not pixel-identical due to different rendering pipelines.

### Color Scheme

Rource uses the same file extension color mapping as Gource for familiarity.

### Effects Comparison

| Effect | Gource | Rource |
|--------|--------|--------|
| Bloom/Glow | OpenGL shader | CPU or GPU post-process |
| Shadows | OpenGL | CPU or GPU |
| Anti-aliasing | Hardware MSAA | Software AA |
| Alpha blending | Hardware | Fixed-point optimized |

---

*Last updated: 2026-01-25*
