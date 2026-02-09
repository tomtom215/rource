# ADR 0002: Software Renderer as Primary Backend

## Status

Accepted

## Date

2024-01-10

## Context

Rource needs to render visualizations on diverse platforms:
- Desktop (Windows, macOS, Linux)
- Web browsers (Chrome, Firefox, Safari, Edge)
- Potentially embedded systems

**Problem**: GPU availability and capabilities vary significantly:
- WebGL2/WebGPU support differs by browser
- Some environments have no GPU (CI, headless servers)
- GPU driver bugs can cause rendering issues
- Users may have outdated hardware

**Goal**: Rource should work everywhere, with GPU acceleration as an enhancement rather than requirement.

## Decision

Implement a pure software renderer as the primary/fallback backend, with GPU backends (WebGL2, wgpu) as optional accelerators.

**Architecture**:
```
Renderer trait
├── SoftwareBackend (pure CPU, always available)
├── WebGL2Backend (browser GPU, optional)
└── WgpuBackend (native/WebGPU, optional)
```

**Selection Logic**:
1. Try wgpu/WebGPU if available
2. Fall back to WebGL2 in browser
3. Fall back to software renderer

## Consequences

### Positive

- **Universal compatibility**: Works on any platform with Rust support
- **Deterministic output**: Software renderer produces identical output across platforms
- **No GPU dependencies**: CI/testing doesn't require GPU
- **Graceful degradation**: Automatically falls back if GPU unavailable
- **Debugging simplicity**: Software path is easier to debug than GPU

### Negative

- **CPU cost**: Software rendering is slower than GPU for large scenes
- **Development overhead**: Must maintain 3 rendering backends
- **Feature parity**: All backends must support same features
- **Memory bandwidth**: Software renderer is memory-bound

### Neutral

- Binary size includes all backends (~200KB for software rasterization)
- GPU backends are feature-gated to reduce compilation for software-only builds

## Alternatives Considered

### Alternative 1: GPU-Only (wgpu)

Require wgpu/WebGPU for all rendering.

**Rejected because**:
- WebGPU not universally available
- Excludes older browsers and devices
- CI would require GPU setup

### Alternative 2: WebGL2-Only in Browser

Use WebGL2 as primary web backend, software as native-only fallback.

**Rejected because**:
- WebGL2 has browser-specific quirks
- Software renderer useful for testing in browser too
- Simpler to have consistent fallback logic

### Alternative 3: External Rendering Library (e.g., wgpu only)

Depend on external GPU library for all rendering.

**Rejected because**:
- Adds large dependency
- Still need fallback for no-GPU environments
- Custom renderer allows optimization for specific use case

## References

- `crates/rource-render/src/lib.rs` - Renderer trait
- `crates/rource-render/src/backend/software/` - Software renderer implementation
- `crates/rource-render/src/backend/webgl2/` - WebGL2 backend
- `crates/rource-render/src/backend/wgpu/` - wgpu backend

---

*ADR created: 2024-01-10*
*Last reviewed: 2026-01-26*
