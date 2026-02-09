# Rource vs Gource Benchmark Methodology

## Overview

This document describes the methodology used to compare Rource (Rust implementation) against Gource (original C++ implementation) for software version control visualization.

## Test Repository

**Repository**: [home-assistant/core](https://github.com/home-assistant/core)

### Why Home Assistant Core?

1. **Large scale**: ~100,000+ commits with ~500,000+ file changes
2. **Active development**: Continuous updates provide realistic data
3. **Diverse structure**: Multiple directories and file types
4. **Open source**: Freely available for reproducible testing
5. **Community recognition**: Well-known project in the developer community

## Benchmark Categories

### 1. Log Parsing Performance

**Purpose**: Measure how quickly each tool can parse and load git history.

**Methodology**:
- Generate standardized log format from the test repository
- Measure wall-clock time to parse entire log
- Measure peak memory usage during parsing
- Run multiple iterations (default: 3) and report average

**Metrics**:
- Parse time (seconds)
- Peak memory (MB)
- Memory per commit (KB)
- Memory per file change (bytes)

**Rource Command**:
```bash
rource --headless --output /tmp/frames --framerate 1 --custom-log custom.log
```

**Gource Command**:
```bash
gource --log-format custom log.txt --stop-at-end -s 0.001 -o /dev/null
```

### 2. Rendering Performance

**Purpose**: Measure frame generation speed for video export.

**Methodology**:
- Configure identical parameters: resolution, framerate, visualization speed
- Export a fixed number of frames (default: 300)
- Measure total export time
- Calculate effective rendering FPS
- Measure peak memory during rendering

**Parameters**:
- Resolution: 1280x720
- Target framerate: 60 FPS
- Seconds per day: 0.1
- Bloom: Disabled (fair comparison)

**Metrics**:
- Export time (seconds)
- Render FPS (frames/second)
- Peak memory (MB)
- Output size (bytes)

**Rource Command**:
```bash
rource --headless --output /tmp/frames --framerate 300 \
       --width 1280 --height 720 --no-bloom --custom-log custom.log
```

**Gource Command**:
```bash
xvfb-run gource --log-format custom log.txt --stop-at-end \
         -s 0.1 --output-framerate 60 --viewport 1280x720 \
         --disable-bloom -o output.ppm
```

### 3. Memory Usage Analysis

**Purpose**: Detailed analysis of memory consumption patterns.

**Methodology**:
- Test initial load memory (parsing only)
- Test memory at different resolutions
- Test memory with varying frame counts
- Track memory growth over time

**Test Matrix**:
- Resolutions: 640x480, 1280x720, 1920x1080, 2560x1440
- Frame counts: 10, 50, 100, 200, 500

**Metrics**:
- Initial load memory (MB)
- Memory per resolution (MB)
- Memory per frame count (MB)
- Memory growth rate

### 4. Binary Size Comparison

**Purpose**: Compare deployment footprint.

**Methodology**:
- Measure raw binary size
- Measure stripped binary size
- Count shared library dependencies
- Measure resource file sizes
- Calculate total footprint

**Metrics**:
- Binary size (bytes)
- Stripped size (bytes)
- Dependency count
- Resource size (bytes)
- WASM size (Rource only)

### 5. Feature Parity

**Purpose**: Document feature availability.

**Methodology**:
- Parse CLI help output
- Categorize features
- Document platform support
- Document rendering backends

**Categories**:
- Input/Output features
- Display features
- Camera features
- Filter features
- Playback features
- Appearance features

## Environment Requirements

### Hardware
- Any modern x86_64 or ARM64 CPU
- At least 4GB RAM (8GB recommended for large repos)
- SSD storage recommended

### Software
- Linux (tested on Ubuntu 24.04)
- Rust 1.93+ (for building Rource)
- GCC/Clang (for building Gource)
- Xvfb (for headless Gource testing)
- `/usr/bin/time` (for memory measurement)

### Dependencies (Gource build)
```bash
apt-get install -y libsdl2-dev libsdl2-image-dev libfreetype6-dev \
    libglew-dev libglm-dev libboost-filesystem-dev libpng-dev \
    libtinyxml-dev libpcre2-dev autoconf automake
```

## Measurement Tools

### Timing
- `/usr/bin/time -v` for wall-clock time and memory
- `date +%s.%N` for precise timestamps
- Multiple runs with statistical analysis

### Memory
- Maximum Resident Set Size (RSS) from `/usr/bin/time -v`
- Peak memory during execution

### Statistics
- Average across N runs (default: 3)
- Standard deviation
- Min/Max values

## Reproducibility

### Running the Benchmarks

```bash
# Clone and prepare
cd /path/to/rource
source scripts/session-setup.sh

# Build Rource
cargo build --release

# Run all benchmarks
./benchmarks/scripts/run_benchmarks.sh

# Or run individual benchmarks
./benchmarks/scripts/benchmark_log_parsing.sh
./benchmarks/scripts/benchmark_memory.sh
./benchmarks/scripts/benchmark_rendering.sh
./benchmarks/scripts/benchmark_binary.sh
./benchmarks/scripts/benchmark_features.sh
```

### Output
Results are saved to `benchmarks/results/` with:
- JSON files for programmatic access
- Markdown reports for human reading
- Raw log files for debugging

### Configuration
Edit `benchmarks/scripts/common.sh` to modify:
- `BENCHMARK_RUNS`: Number of iterations
- `WARMUP_RUNS`: Warmup iterations
- `FRAME_COUNT`: Frames to render
- `RESOLUTION_WIDTH/HEIGHT`: Test resolution
- `SECONDS_PER_DAY`: Visualization speed

## Limitations

### Gource
- Requires OpenGL even for PPM output
- Must use xvfb-run for headless testing
- PPM output to stdout (stream processing)

### Rource
- Multiple renderer backends: wgpu (GPU via Vulkan/Metal/DX12), WebGL2 (browser), software (CPU fallback)
- Some Gource features not yet implemented
- WASM build has browser-specific constraints

### Comparison Notes
1. **Rendering technology differs**: Gource uses GPU (OpenGL), Rource supports GPU (wgpu) and CPU (software) backends
2. **Feature sets differ**: Not all Gource features in Rource (and vice versa)
3. **Headless approach differs**: Rource is truly headless; Gource requires virtual display

## Interpreting Results

### When Rource wins
- Lower memory usage → Better for large repositories
- Faster parsing → Better for quick visualizations
- Smaller binary → Better for deployment/embedding

### When Gource wins
- GPU rendering → Faster when GPU available
- More features → Better for advanced customization
- Mature codebase → Better stability/polish

### Key trade-offs
- **CPU vs GPU**: Rource works everywhere; Gource faster with good GPU
- **Memory vs Speed**: Rource optimizes memory; Gource optimizes frame rate
- **Portability vs Features**: Rource runs in browser; Gource has more options
