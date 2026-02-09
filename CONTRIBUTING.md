# Contributing to Rource

Thank you for your interest in contributing to Rource! This document provides guidelines and instructions for contributing.

## Code of Conduct

Be respectful and constructive in all interactions. We welcome contributors of all experience levels.

## Getting Started

### Prerequisites

- **Rust 1.93+** - Install via [rustup](https://rustup.rs/)
- **wasm-pack** - For WebAssembly builds (`cargo install wasm-pack`)
- **Git** - For version control

### Development Setup

```bash
# Clone the repository
git clone https://github.com/tomtom215/rource.git
cd rource

# Run the setup script to install all dependencies
source scripts/session-setup.sh

# Verify everything works
cargo test
cargo clippy
```

### Building

```bash
# Native debug build
cargo build

# Native release build
cargo build --release

# WebAssembly build
cd rource-wasm
wasm-pack build --target web --release
```

## Project Structure

```
rource/
├── crates/
│   ├── rource-math/      # Math primitives (Vec2, Mat4, Color, etc.)
│   ├── rource-vcs/       # VCS log parsing (Git, SVN, Custom, Mercurial, Bazaar)
│   ├── rource-core/      # Core engine (scene, physics, camera)
│   └── rource-render/    # Rendering (software, WebGL2, wgpu)
├── rource-cli/           # Native command-line application
├── rource-wasm/          # WebAssembly application
│   └── www/              # Web demo (HTML, CSS, JavaScript)
│       └── js/           # Modular ES modules (main.js, features/, etc.)
├── scripts/              # Build and development scripts
└── benchmarks/           # Performance benchmarks
```

## Development Workflow

### 1. Create a Branch

```bash
git checkout -b feature/your-feature-name
# or
git checkout -b fix/issue-description
```

### 2. Make Changes

Follow these guidelines:

- **Code Style**: Run `cargo fmt` before committing
- **Linting**: Ensure `cargo clippy` passes with no warnings
- **Testing**: Add tests for new functionality
- **Documentation**: Update docs for public API changes

### 3. Test Your Changes

```bash
# Run all tests (2900+ tests)
cargo test

# Run tests for a specific crate
cargo test -p rource-core

# Run with output for debugging
cargo test -- --nocapture

# Check for warnings (must include --all-features to catch feature-gated code)
cargo clippy --all-targets --all-features -- -D warnings

# Format code
cargo fmt
```

### 4. Commit Your Changes

Use [Conventional Commits](https://www.conventionalcommits.org/) format:

```bash
# Feature
git commit -m "feat: add SVN log parser"

# Bug fix
git commit -m "fix: correct camera bounds calculation"

# Documentation
git commit -m "docs: update WebGL2 setup instructions"

# Refactoring
git commit -m "refactor: extract quadtree into separate module"

# Tests
git commit -m "test: add unit tests for spline interpolation"
```

### 5. Submit a Pull Request

1. Push your branch to your fork
2. Open a pull request against `main`
3. Fill out the PR template with:
   - Summary of changes
   - Related issue (if any)
   - Test plan
4. Wait for CI checks to pass
5. Address review feedback

**Important**: All PRs must pass the Expert+ review standards. See [`docs/REVIEW_STANDARDS.md`](docs/REVIEW_STANDARDS.md) for the complete checklist.

## Testing Guidelines

### Unit Tests

Every module should have unit tests:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_feature_behavior() {
        // Arrange
        let input = create_test_input();

        // Act
        let result = function_under_test(input);

        // Assert
        assert_eq!(result, expected_output);
    }
}
```

### Test Categories

| Crate | Test Count | Focus |
|-------|------------|-------|
| rource-math | 508 | Numerical accuracy, edge cases |
| rource-vcs | 366 | Parser correctness, format edge cases |
| rource-core | 560 | Scene graph, physics, camera |
| rource-render | 615 | Rendering correctness, GPU backends |
| rource-cli | 358 | CLI argument parsing, integration |
| rource-wasm | 557 | WebAssembly bindings, JavaScript API |

### Integration Tests

For end-to-end testing:

```bash
# Test headless rendering
./target/release/rource --headless --output /tmp/test-frames .

# Verify output
ls /tmp/test-frames/*.ppm | head -5
```

## Formal Verification

This project uses a **hybrid verification architecture** with Verus, Coq, and Kani for machine-checked proofs of mathematical correctness. Together these tools provide **2968 formally verified theorems/harnesses** across all 9 primary math types (Vec2-4, Mat3-4, Color, Rect, Bounds, Utils) plus floating-point error bounds.

- **Verus**: 498 proof functions (Rust-native verification)
- **Coq (R-based + Z-based)**: 1837 theorems (0 admits, machine-checked)
- **Coq (FP error bounds)**: 361 theorems (Flocq 4.1.3, IEEE 754 binary32)
- **Kani (CBMC)**: 272 proof harnesses (bit-precise IEEE 754 f32 verification)

For full details, see [`docs/verification/FORMAL_VERIFICATION.md`](docs/verification/FORMAL_VERIFICATION.md).

To set up and run all verification tools:

```bash
# Install all formal verification tools and run proofs
./scripts/setup-formal-verification.sh --verify

# Check-only mode (verify tools are installed)
./scripts/setup-formal-verification.sh --check
```

## Documentation Automation

Documentation metrics (verification counts, test counts, optimization phases) are kept consistent via automated scripts:

```bash
# Update all documentation metrics from ground truth
./scripts/update-doc-metrics.sh

# Update verification counts only
./scripts/update-verification-counts.sh

# CI enforcement (exits non-zero if metrics are stale)
./scripts/update-verification-counts.sh --check
./scripts/update-doc-metrics.sh --check
```

Run these scripts after adding or removing proofs, tests, or other tracked metrics. CI enforces consistency via `--check` mode.

## Code Style

### Rust

- Follow the [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- Use `cargo fmt` for formatting
- Use `cargo clippy` for linting
- Prefer explicit over implicit
- Document public APIs with doc comments

```rust
/// Computes the bounding box of all visible entities.
///
/// # Returns
///
/// A `Bounds` containing all entities, or `None` if the scene is empty.
///
/// # Example
///
/// ```
/// let bounds = scene.compute_entity_bounds();
/// if let Some(b) = bounds {
///     camera.fit_to_bounds(&b);
/// }
/// ```
pub fn compute_entity_bounds(&self) -> Option<Bounds> {
    // implementation
}
```

### JavaScript (Web UI)

The web UI uses a modular ES Module architecture located in `rource-wasm/www/js/`:

```
js/
├── main.js              # Entry point - WASM init and module coordination
├── config.js            # Constants and extension colors
├── state.js             # Observable application state
├── wasm-api.js          # Safe WASM call wrappers
├── animation.js         # Render loop and canvas management
├── preferences.js       # localStorage handling
├── dom.js               # Centralized DOM element references
├── data-loader.js       # Repository data loading
├── github-fetch.js      # GitHub API integration
├── utils.js             # Shared utility functions
├── core/                # Core runtime modules
│   ├── animation-loop.js
│   ├── frame-scheduler.js
│   └── performance-metrics.js
├── ui/                  # UI component modules
│   └── playback-ui.js
└── features/            # Feature-specific modules
    ├── screenshot.js
    ├── fullscreen.js
    ├── theme.js
    ├── help.js
    ├── keyboard.js
    ├── playback.js
    ├── canvas-input.js
    ├── mobile-controls.js
    ├── mobile-toolbar.js
    ├── bottom-sheet.js
    ├── panels.js
    ├── immersive-mode.js
    ├── video-recording.js
    ├── font-size.js
    ├── data-input.js
    ├── hover-tooltip.js
    ├── reduced-motion.js
    └── window-events.js
```

**Guidelines:**

- Use ES modules with explicit imports/exports
- Use `const` by default, `let` when reassignment needed
- Handle all error cases with user feedback via `showToast()`
- Follow accessibility best practices (ARIA labels, keyboard navigation)
- Use `safeWasmCall()` from `wasm-api.js` for all WASM method calls
- Add new features in `features/` directory as separate modules
- Keep state in `state.js`, access via `getRource()`, `hasData()`, etc.

### CSS

- Use CSS custom properties for theming
- Support both light and dark themes
- Ensure WCAG AA color contrast (4.5:1 minimum)
- Use responsive design with mobile-first approach

## Performance Considerations

Rource is designed to handle repositories with 100k+ commits. Keep these principles in mind:

1. **Batch Operations**: Use instanced rendering, avoid per-entity draw calls
2. **Spatial Indexing**: Use quadtree for entity queries
3. **Memory Efficiency**: Use string interning for repeated values
4. **Lazy Loading**: Stream large log files instead of loading all at once

### Profiling

```bash
# Build with profiling support
cargo build --release

# Run with flamegraph (requires cargo-flamegraph)
cargo flamegraph -- --headless --output /tmp/frames .
```

## Adding New Features

### New VCS Parser

1. Create `crates/rource-vcs/src/parser/newvcs.rs`
2. Implement the `Parser` trait
3. Register in `crates/rource-vcs/src/detect.rs`
4. Add comprehensive tests
5. Update documentation

### New Rendering Backend

1. Create `crates/rource-render/src/backend/newbackend.rs`
2. Implement the `Renderer` trait
3. Add feature flag in `Cargo.toml`
4. Update backend selection logic
5. Document requirements and limitations

### New Configuration Option

1. Add field to the appropriate settings module in `rource-core/src/config/settings/`:
   - `camera.rs`, `display.rs`, `playback.rs`, `visibility.rs`, `limits.rs`
   - `input.rs`, `export.rs`, `title.rs`, `directory.rs`, `layout.rs`
   - `overlay.rs`, `filter.rs`, or `mod.rs` for new setting categories
2. Add CLI argument in `rource-cli/src/args/mod.rs`
3. Add environment variable in `rource-core/src/config/config_env.rs`
4. Add WASM binding in `rource-wasm/src/wasm_api/settings.rs`
5. Update README and help text

## Reporting Issues

When opening an issue, include:

1. **Environment**: OS, Rust version, browser (for WASM issues)
2. **Steps to Reproduce**: Minimal commands to trigger the issue
3. **Expected Behavior**: What should happen
4. **Actual Behavior**: What actually happens
5. **Logs/Output**: Any error messages or relevant output

## Review Standards

This project maintains **Expert+ quality standards**. All contributions must pass rigorous review gates:

| Gate | Requirement |
|------|-------------|
| Code Quality | Zero clippy warnings, formatted, documented |
| Test Coverage | Tests for all new/changed code |
| Performance | No regressions, benchmarks for hot paths |
| Mobile UX | Tested on mobile Safari (if UI changes) |
| Accessibility | WCAG 2.1 AA compliance (if UI changes) |
| Documentation | Roadmaps updated, metrics documented |

**Full details**: [`docs/REVIEW_STANDARDS.md`](docs/REVIEW_STANDARDS.md)

### Quick Pre-Submission Check

```bash
# Run this before every PR
cargo fmt && \
cargo clippy --all-targets --all-features -- -D warnings && \
cargo test --all && \
cargo doc --no-deps
```

## Questions?

- Check existing [issues](https://github.com/tomtom215/rource/issues)
- Read the [README](README.md) and [CLAUDE.md](CLAUDE.md)
- Review [Expert+ standards](docs/REVIEW_STANDARDS.md)
- Open a discussion for general questions

## License

By contributing, you agree that your contributions will be licensed under the GPL-3.0 License.
