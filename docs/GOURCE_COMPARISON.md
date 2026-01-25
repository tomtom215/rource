# Gource Comparison

Rource is a complete Rust rewrite of [Gource](https://github.com/acaudwell/Gource). This document tracks feature parity, performance comparisons, and CLI compatibility.

---

## Table of Contents

1. [Key Differences](#key-differences)
2. [Feature Parity Status](#feature-parity-status)
3. [Remaining Roadmap](#remaining-roadmap)
4. [Benchmark Results](#benchmark-results)
5. [Performance Comparison](#performance-comparison)
6. [CLI Compatibility](#cli-compatibility)
7. [VCS Support](#vcs-support)

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

## Benchmark Results

### Test Environment

| Component | Value |
|-----------|-------|
| Repository | [Home Assistant Core](https://github.com/home-assistant/core) |
| Commits | 86,758 |
| File Operations | 524,925 |
| History Span | 13+ years (2013-2026) |
| Test Date | 2026-01-25 |
| Platform | x86_64-unknown-linux-gnu |
| Rource Version | 0.1.0 |

### Benchmark Parameters

| Parameter | Value | Rationale |
|-----------|-------|-----------|
| Resolution | 1280×720 | Standard HD |
| Bloom | Disabled | Isolate core rendering |
| Seconds per day | 0.01 | Fast playback to process entire history |
| Framerate | 60 | Standard video framerate |
| Rendering | Software (CPU) | Maximum compatibility |
| Input | Custom log (pipe-delimited) | 524,925 operations |

### Rource Measured Results

**Timing (nanosecond precision via `--benchmark` flag):**

| Metric | Value |
|--------|-------|
| Wall clock time | 243.046 seconds |
| Total frames | 2,708 |
| Average frame time | 89.75 ms |
| Min frame time | 4.45 ms |
| Max frame time | 241.42 ms |
| P50 frame time | 76.47 ms |
| P95 frame time | 199.38 ms |
| P99 frame time | 214.66 ms |

**Phase Breakdown:**

| Phase | Time | Percentage |
|-------|------|------------|
| Render | 212.021s | 87.2% |
| Scene update | 17.719s | 7.3% |
| PPM export | 12.710s | 5.2% |
| Commit apply | 0.591s | 0.2% |
| Effects | <0.001s | 0.0% |

**Throughput:**

| Metric | Value |
|--------|-------|
| Frame rate | 11.14 fps |
| Commits/second | 357.0 |
| File ops/second | 2,160 |

**Final Scene Complexity:**

| Metric | Value |
|--------|-------|
| Files rendered | 31,245 |
| Users rendered | 4,786 |
| Directories rendered | 4,836 |
| Commits applied | 86,756 |

### Output Verification

| Check | Result |
|-------|--------|
| Frame count | 2,708 PPM files |
| Frame size | 2,764,816 bytes each (1280×720×3 + header) |
| Total output | 7.0 GB |
| Content verification | 2.2% → 23.8% non-zero pixels (increasing) |

### Reproducible Commands

**Generate custom log from any Git repository:**

```bash
cd /path/to/repo
git log --pretty=format:'%at|%aN' --name-status | awk '
/^[0-9]+\|/ { timestamp_author=$0; next }
/^[AMD]/ {
  action = substr($0,1,1)
  file = substr($0,3)
  if (file != "") print timestamp_author "|" action "|" file
}' > /tmp/custom.log

# Filter to valid 4-field lines and sort chronologically
awk -F'|' 'NF == 4' /tmp/custom.log | sort -t'|' -k1,1n > /tmp/valid.log
```

**Run Rource benchmark:**

```bash
rm -rf /tmp/rource_frames && mkdir -p /tmp/rource_frames
/path/to/rource \
  --headless --benchmark --custom-log \
  -W 1280 -H 720 --no-bloom \
  --seconds-per-day 0.01 --framerate 60 \
  --output /tmp/rource_frames \
  /tmp/valid.log 2>&1 | tee /tmp/rource_result.log
```

**Run Gource benchmark (for comparison):**

```bash
xvfb-run -a gource --log-format custom /tmp/valid.log \
  -1280x720 --stop-at-end --disable-auto-rotate --disable-bloom \
  --seconds-per-day 0.01 --output-framerate 60 \
  -o /tmp/gource_output.ppm
```

**Verify output frames have content:**

```bash
python3 << 'EOF'
with open('/tmp/rource_frames/frame_00000000.ppm', 'rb') as f:
    for _ in range(3): f.readline()  # Skip header
    data = f.read()
    non_zero = sum(1 for b in data if b != 0)
    pct = 100 * non_zero / len(data)
    print(f'{non_zero} non-zero bytes ({pct:.1f}%)')
EOF
```

---

## Performance Comparison

### Architecture Differences

| Aspect | Gource | Rource |
|--------|--------|--------|
| Rendering | OpenGL (GPU) | Software rasterizer (CPU) |
| Memory model | GPU VRAM + RAM | RAM only |
| Parallelism | GPU shaders | Single-threaded CPU |
| Bottleneck | GPU fill rate | CPU rendering |

### Expected Tradeoffs

| Scenario | Gource Advantage | Rource Advantage |
|----------|------------------|------------------|
| Desktop with GPU | Faster rendering | N/A |
| Headless server | Requires virtual framebuffer | Native headless |
| Browser/WASM | Not supported | Native support |
| ARM/embedded | May lack OpenGL | Works on any CPU |
| CI/CD pipelines | Complex setup | Simple binary |

### Resource Usage

| Metric | Gource | Rource |
|--------|--------|--------|
| GPU memory | Required | Not used |
| CPU usage (idle) | Low | Low |
| CPU usage (active) | Low-Medium | High (software render) |
| RAM scaling | Linear with scene | Linear with scene |

### Optimization Tips for Large Repos

```bash
# Reduce visual complexity
rource --no-bloom --hide-dirs "node_modules|vendor|target" .

# Limit concurrent files
rource --max-files 1000 -s 0.5 .

# Use faster playback
rource --seconds-per-day 0.1 --auto-skip-seconds 1 .

# Headless batch export (fastest)
rource --headless --output /tmp/frames --seconds-per-day 0.01 .
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

*Last updated: 2026-01-25* (benchmark results added)
