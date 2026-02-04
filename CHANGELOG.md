# Changelog

All notable changes to Rource are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- Shared LOD (Level-of-Detail) constants module in `rource-render`
- Shared rendering helpers module for visual parity between CLI and WASM
- Comprehensive CHANGELOG.md for version history tracking

### Changed
- CLI and WASM renderers now import LOD constants from shared module
- Consolidated duplicate rendering helper functions

## [0.9.0] - 2026-01-25

### Performance - Phase 59
- Optimized file rendering to skip glow effect for inactive files
- Added measured Gource 0.55 benchmark comparison
- Verified rendering bottleneck analysis with empirical data

### Performance - Phase 58
- Implemented LUT-based random direction generation (13.9x faster than sin/cos)
- Added empirical validation with actual measurements

### Documentation
- Consolidated PERFORMANCE.md into organized `docs/performance/` structure
- Added comprehensive algorithmic complexity documentation
- Created GOURCE_COMPARISON.md for feature parity tracking

## [0.8.0] - 2026-01-20

### Performance - Phases 44-57
- **Phase 57**: Cutting-edge WASM optimization analysis
- **Phase 56**: Quantum algorithm analysis for future readiness
- **Phase 55**: Targeted algorithmic optimization analysis
- **Phase 54**: Analysis of 2025 mathematical breakthroughs
- **Phase 53**: Graph coloring algorithm analysis
- **Phase 52**: SSSP analysis and theoretical algorithms documentation
- **Phase 51**: Algorithmic excellence exploration
- **Phase 50**: Rust 1.93.0 upgrade with benchmark analysis
- **Phase 49**: Easing functions and camera optimizations using `exp2()` instead of `powf()` (3x faster)
- **Phase 48**: Eliminated redundant sqrt in perpendicular normalization (-72% operation time)
- **Phase 47**: Force normalization optimization
- **Phase 46**: VCS parser zero-allocation with iterator-based parsing
- **Phase 45**: Color conversion LUTs (-54% from_hex, -62% to_argb8)
- **Phase 44**: Fixed-point alpha blending (-21% batch, -81% same-color operations)

### Changed
- Upgraded minimum Rust version to 1.93.0
- Updated Dockerfile to use Debian Trixie base image

## [0.7.0] - 2026-01-15

### Performance - Phases 33-43
- **Phase 43**: Micro-optimization audit with verified improvements
- **Phase 42**: Bloom vertical blur strip-based optimization
- **Phase 41**: Browser freeze prevention for large repositories
- **Phase 40**: Data structure and algorithm perfection
- **Phase 39**: O(f·c) → O(f) cache serialization optimization
- **Phase 38**: GPU physics command buffer batching
- **Phase 37**: Data structure and algorithm micro-optimizations
- **Phase 36**: Instruction-level micro-optimizations
- **Phase 35**: Bloom optimization and division-to-multiplication
- **Phase 34**: Micro-optimizations and state caching
- **Phase 33**: Spatial hashing and zero-allocation readbacks

### Fixed
- Browser freeze with large repositories resolved

## [0.6.0] - 2026-01-10

### Performance - Phases 26-32
- **Phase 32**: WASM hot path optimizations with precomputed reciprocals
- **Phase 31**: Visual rendering hot paths with precomputed constants
- **Phase 30**: Profiler zero-allocation optimization
- **Phase 29**: Visualization cache for ~100x faster repeat loads
- **Phase 28**: Per-fragment division elimination in WebGL2 shaders
- **Phase 27**: `#[inline]` annotations on hot path methods
- **Phase 26**: FxHashMap and sort_unstable for better performance

### Added
- Visualization cache system (bitcode serialization)
- WASM profiling infrastructure
- Comprehensive profiling tools

### Fixed
- Mobile Safari crash prevention with async WebGPU check
- Recursive borrow crash and timeline misalignment

## [0.5.0] - 2026-01-05

### Performance - Phases 20-25
- **Phase 25**: HUD string caching to eliminate per-frame allocations
- **Phase 24**: Barnes-Hut tree structure preservation across frames
- **Phase 23**: Path clone elimination in commit loops
- **Phase 22**: Double user lookup elimination in spawn_action
- **Phase 21**: Critical performance optimizations from audit

### Added
- Comprehensive performance audit report
- CLI `--benchmark` flag with nanosecond precision timing
- Microsecond precision frame time display in WASM

### Fixed
- Per-frame Vec allocations in file label rendering

## [0.4.0] - 2025-12-28

### Added
- O(N) GPU spatial hash physics with Blelloch prefix sum
- Mobile UX redesign for iOS Safari
- iOS-style bottom sheet for mobile UI
- Portfolio-quality mobile UI/UX improvements
- Watermark overlay system with configurable positioning

### Performance
- O(N log N) Barnes-Hut algorithm for force-directed layout
- GPU physics command buffer batching
- Per-frame allocation elimination in wgpu backend

### Fixed
- Mobile sidebar toggle and close button visibility
- Timeline tick alignment with commit dates
- Large repo handling and dropdown z-index

## [0.3.0] - 2025-12-20

### Added
- Label collision avoidance with spatial hash grid
- Adaptive label visibility based on zoom level
- Directory circles legend in file types panel
- Gource-style radial tree layout
- Entity dragging for files and users

### Changed
- Modularized web UI into ES modules
- Enhanced visualization with stylized avatars and curved branches

### Fixed
- Screenshot capture for WebGL2 (force render before capture)
- Zoom behavior to zoom toward mouse position
- Mobile fullscreen handling

## [0.2.0] - 2025-12-10

### Added
- WebGL2 rendering backend with bloom and shadow effects
- wgpu rendering backend for WebGPU/Vulkan/Metal/DX12
- Software rasterizer for maximum compatibility
- Catmull-Rom spline interpolation for smooth curves
- Action beams from users to files with glow effects
- Stylized avatar shapes (modern person silhouettes)
- Curved tree branches with depth-based styling

### Performance
- QuadTree spatial indexing with O(log n) queries
- Level-of-Detail (LOD) system for large repositories
- Zero-allocation hot paths in rendering

## [0.1.0] - 2025-12-01

### Added
- Initial release of Rource
- Complete Rust rewrite of Gource visualization tool
- Multi-backend rendering architecture
- VCS log parsing (Git, SVN, Mercurial, Bazaar, Custom)
- Force-directed graph layout
- Camera system with smooth transitions and auto-fit
- CLI application with winit + softbuffer
- WebAssembly build with wasm-pack
- Headless rendering mode for batch export
- PPM frame output for video conversion
- Configuration via CLI arguments, environment variables, and config files

### Architecture
- `rource-math`: Pure math types (Vec2, Vec3, Vec4, Mat3, Mat4, Color)
- `rource-vcs`: VCS log parsing with 5 format support
- `rource-core`: Engine logic (scene, physics, animation, camera, config)
- `rource-render`: Rendering abstraction with 3 backends
- `rource-cli`: Native CLI application
- `rource-wasm`: WebAssembly application

---

## Performance Optimization Summary

Rource has undergone 83 documented optimization phases, achieving:

| Metric | Improvement |
|--------|-------------|
| Alpha blending (same-color) | -81% |
| Color from_hex | -54% |
| Color to_argb8 | -62% |
| Perpendicular normalization | -72% |
| Easing exp2 vs powf | 3x faster |
| Random direction LUT | 13.9x faster |
| Repeat load (cache) | ~100x faster |

See [docs/performance/](./docs/performance/) for detailed documentation of all optimization phases.

## Architectural Decisions

### Why Rust?
- Memory safety without garbage collection
- Zero-cost abstractions
- Excellent WASM support via wasm-pack
- Strong type system prevents common bugs

### Why Multiple Rendering Backends?
- **wgpu**: Best performance on modern GPUs
- **WebGL2**: Broad browser compatibility
- **Software**: Maximum portability, deterministic output

### Why No External GUI Framework?
- Custom rendering enables consistent visuals across platforms
- Smaller binary size (~3.8MB native, ~1MB WASM gzipped)
- Full control over rendering pipeline for optimization

---

## Links

- [Original Gource](https://github.com/acaudwell/Gource) - The inspiration for this project
- [Performance Documentation](./docs/performance/) - 83 optimization phases
- [Architecture Documentation](./docs/ARCHITECTURE.md) - Crate structure
- [Contributing Guidelines](./CONTRIBUTING.md) - How to contribute

[Unreleased]: https://github.com/tomtom215/rource/compare/v0.9.0...HEAD
[0.9.0]: https://github.com/tomtom215/rource/compare/v0.8.0...v0.9.0
[0.8.0]: https://github.com/tomtom215/rource/compare/v0.7.0...v0.8.0
[0.7.0]: https://github.com/tomtom215/rource/compare/v0.6.0...v0.7.0
[0.6.0]: https://github.com/tomtom215/rource/compare/v0.5.0...v0.6.0
[0.5.0]: https://github.com/tomtom215/rource/compare/v0.4.0...v0.5.0
[0.4.0]: https://github.com/tomtom215/rource/compare/v0.3.0...v0.4.0
[0.3.0]: https://github.com/tomtom215/rource/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/tomtom215/rource/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/tomtom215/rource/releases/tag/v0.1.0
