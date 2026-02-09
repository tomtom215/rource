# ADR 0003: WASM-First Architecture

## Status

Accepted

## Date

2024-01-05

## Context

Rource is a rewrite of Gource (C++/OpenGL) with goals of:
- Running in web browsers without plugins
- Cross-platform deployment (single binary)
- Reduced system dependencies

**Problem**: Traditional desktop applications require:
- Platform-specific builds (Windows, macOS, Linux)
- GPU driver installations
- User downloads and installations

**Opportunity**: WebAssembly enables:
- Run in any modern browser
- No installation required
- Instant deployment via URL

## Decision

Design Rource with WASM as a first-class target, not an afterthought.

**Architecture Principles**:
1. **No filesystem dependencies**: All data via memory/streams
2. **No threads required**: Single-threaded with async-compatible design
3. **No native allocator assumptions**: Work with WASM allocator
4. **No platform-specific code in core**: Isolate in cli/wasm crates

**Crate Structure**:
```
rource-math     - Pure computation, no I/O
rource-vcs      - Log parsing, no filesystem
rource-core     - Scene logic, no platform deps
rource-render   - Rendering, abstracted backends
rource-cli      - Native CLI (optional)
rource-wasm     - WASM bindings
```

## Consequences

### Positive

- **Browser deployment**: Demo at `https://tomtom215.github.io/rource/`
- **No installation**: Users can try immediately
- **Cross-platform**: Single codebase, works everywhere
- **Reduced binary size**: WASM is ~1MB gzipped (includes wgpu support)
- **Sandboxed execution**: Browser security model applies

### Negative

- **Performance overhead**: WASM is ~10-30% slower than native
- **Limited APIs**: No direct filesystem, threading constrained
- **Browser quirks**: Different browsers have different WASM performance
- **Memory limits**: WASM typically has 2-4GB limit

### Neutral

- Native CLI still available for headless batch processing
- Same core code compiles to both targets
- Feature flags control target-specific code

## Alternatives Considered

### Alternative 1: Native-First with WASM Port

Build for native, then port to WASM.

**Rejected because**:
- Often results in WASM as second-class citizen
- Architecture decisions made for native don't translate well
- Threading/filesystem usage creeps in

### Alternative 2: Electron/Tauri Wrapper

Wrap native app in web shell.

**Rejected because**:
- Large download size (100MB+)
- Still requires installation
- Defeats purpose of browser deployment

### Alternative 3: JavaScript Implementation

Rewrite in JavaScript/TypeScript.

**Rejected because**:
- Loses performance of Rust
- More difficult to maintain type safety
- Can't share code with native CLI

## References

- `rource-wasm/` - WASM crate with bindings
- `rource-wasm/www/` - Web frontend
- Live demo: `https://tomtom215.github.io/rource/`
- Rust and WebAssembly Book: https://rustwasm.github.io/docs/book/

---

*ADR created: 2024-01-05*
*Last reviewed: 2026-01-26*
