# Visual Regression Testing

This document describes the visual regression testing infrastructure for Rource's rendering pipeline.

## Overview

Visual regression tests ensure pixel-perfect consistency of rendered output across changes. The system:

- Compares rendered frames against golden reference images
- Uses deterministic rendering mode for reproducibility
- Provides detailed diff images and metrics on failure
- Integrates with CI for automatic regression detection

## Architecture

### Components

```
crates/rource-render/
├── tests/
│   ├── visual_regression.rs    # Test harness and test cases
│   └── visual/
│       ├── golden/             # Reference images (committed)
│       │   ├── empty_black_frame.png
│       │   ├── solid_color_fill.png
│       │   ├── disc_rendering.png
│       │   ├── line_rendering.png
│       │   ├── rect_rendering.png
│       │   ├── alpha_blending.png
│       │   ├── ring_rendering.png
│       │   ├── color_spectrum.png
│       │   └── complex_scene.png
│       └── output/             # Test output (gitignored)
│           ├── *_actual.png    # Rendered output
│           └── *_diff.png      # Difference visualization
```

### Test Harness

The test harness (`visual_regression.rs`) provides:

1. **Pixel Comparison**: Mean Squared Error (MSE) calculation
2. **Diff Generation**: Visual highlighting of differences
3. **PNG I/O**: Pure Rust PNG encoding/decoding (no external dependencies)
4. **Golden Image Management**: Automatic creation and comparison

### Metrics

| Metric | Description | Threshold |
|--------|-------------|-----------|
| MSE | Mean Squared Error (0.0 = identical) | 0.0 (pixel-perfect) |
| PSNR | Peak Signal-to-Noise Ratio (dB) | ∞ for perfect match |
| Different Pixels | Count of differing pixels | 0 |
| Max Channel Diff | Maximum per-channel difference | 0 |

## Usage

### Running Tests

```bash
# Run all visual regression tests
cargo test -p rource-render --test visual_regression

# Run with verbose output
cargo test -p rource-render --test visual_regression -- --nocapture

# Run a specific test
cargo test -p rource-render --test visual_regression visual_disc_rendering
```

### Updating Golden Images

When making intentional visual changes:

```bash
# Update all golden images
UPDATE_GOLDEN=1 cargo test -p rource-render --test visual_regression

# Update a specific test's golden image
UPDATE_GOLDEN=1 cargo test -p rource-render --test visual_regression visual_disc_rendering
```

**Important**: Always review changes before committing updated golden images.

### Adding New Tests

1. Create a test function in `visual_regression.rs`:

```rust
#[test]
fn visual_my_new_test() {
    let mut renderer = SoftwareRenderer::new(TEST_WIDTH, TEST_HEIGHT);
    renderer.set_deterministic_mode(true);
    renderer.begin_frame();

    // Your rendering code here
    renderer.clear(Color::BLACK);
    renderer.draw_disc(Vec2::new(160.0, 120.0), 50.0, Color::RED);

    renderer.end_frame();
    assert_visual_match("my_new_test", &renderer);
}
```

2. Run with `UPDATE_GOLDEN=1` to create the golden image:

```bash
UPDATE_GOLDEN=1 cargo test -p rource-render --test visual_regression visual_my_new_test
```

3. Commit the new golden image:

```bash
git add crates/rource-render/tests/visual/golden/my_new_test.png
git commit -m "test: add visual regression test for my_new_test"
```

## Test Categories

### Current Tests

| Test | Description | Primitives Tested |
|------|-------------|-------------------|
| `empty_black_frame` | Blank black canvas | `clear()` |
| `solid_color_fill` | Single color fill | `clear()` with custom color |
| `disc_rendering` | Filled circles | `draw_disc()` |
| `line_rendering` | Lines at various angles | `draw_line()` |
| `rect_rendering` | Filled rectangles | `draw_quad()` |
| `alpha_blending` | Semi-transparent overlaps | Alpha compositing |
| `ring_rendering` | Circle outlines | `draw_circle()` |
| `color_spectrum` | Color accuracy | Multiple colors |
| `complex_scene` | Combined elements | All primitives |

### Test Coverage Goals

- **Primitives**: All rendering primitives (disc, line, quad, circle, spline, text)
- **Blending**: Alpha compositing, additive blending
- **Colors**: Full spectrum, edge cases (black, white, transparent)
- **Geometry**: Small/large shapes, boundary conditions, anti-aliasing
- **Transforms**: Scaling, rotation, translation

## Determinism

Visual regression tests require deterministic rendering. Key factors:

1. **Fixed Seed**: Any randomness uses fixed seeds
2. **Deterministic Mode**: `renderer.set_deterministic_mode(true)`
3. **Fixed Dimensions**: Standard 320x240 test viewport
4. **No Floating Point Variance**: Pure integer or fixed-point arithmetic in critical paths

### Ensuring Determinism

```rust
// Always enable deterministic mode
renderer.set_deterministic_mode(true);

// Use exact coordinates (avoid accumulated floating point errors)
let x = 100.0;  // Good: exact value
let x = 100.0 / 3.0;  // Caution: may vary across platforms
```

## CI Integration

Visual regression tests run automatically on:

- Push to `main` branch (for paths: `crates/rource-render/**`, `crates/rource-math/**`)
- Pull requests to `main` branch (same paths)
- Manual workflow dispatch

### Workflow Features

1. **Automatic Failure Detection**: Fails PR if visual differences detected
2. **Diff Artifact Upload**: Uploads diff images for review
3. **PR Comments**: Adds comment explaining failures
4. **Manual Golden Update**: Workflow dispatch option to update golden images

### Reviewing Failures

When CI fails:

1. Download the `visual-regression-diffs` artifact
2. Review `*_actual.png` (what was rendered)
3. Review `*_diff.png` (differences highlighted in red)
4. Compare against `tests/visual/golden/*.png`

If changes are intentional:

```bash
UPDATE_GOLDEN=1 cargo test -p rource-render --test visual_regression
git add crates/rource-render/tests/visual/golden/
git commit -m "chore: update golden images for <reason>"
```

## Metrics Interpretation

### MSE (Mean Squared Error)

```
MSE = Σ((expected - actual)²) / (pixels × channels)
```

| MSE Value | Interpretation |
|-----------|----------------|
| 0.0 | Pixel-perfect match |
| < 0.001 | ~1 LSB difference (imperceptible) |
| < 0.01 | Minor differences |
| > 0.01 | Visible differences |

### PSNR (Peak Signal-to-Noise Ratio)

```
PSNR = 10 × log₁₀(1 / MSE)
```

| PSNR Value | Interpretation |
|------------|----------------|
| ∞ | Perfect match |
| > 40 dB | Excellent quality |
| 30-40 dB | Good quality |
| < 30 dB | Noticeable differences |

## Troubleshooting

### Test Fails Unexpectedly

1. **Platform Differences**: Ensure deterministic mode is enabled
2. **Floating Point**: Check for platform-dependent FP behavior
3. **Random State**: Verify all randomness is seeded
4. **Font Rendering**: Text tests may vary by platform

### Golden Images Missing

```bash
# Generate all golden images
UPDATE_GOLDEN=1 cargo test -p rource-render --test visual_regression
git add crates/rource-render/tests/visual/golden/
```

### Large Diffs Despite Minor Changes

Anti-aliasing edge pixels can cause many "different" pixels. Check:
- The actual visual difference (may be imperceptible)
- Whether deterministic mode is properly enabled
- If the change affects anti-aliasing algorithm

## Future Improvements

- [ ] **Perceptual Diff**: SSIM-based comparison for perceptual similarity
- [ ] **Tolerance Mode**: Allow small MSE threshold for anti-aliasing variance
- [ ] **Multi-Resolution**: Test at multiple viewport sizes
- [ ] **Text Rendering**: Tests with embedded font for consistent text
- [ ] **WebGL/WGPU**: Visual regression for GPU backends

---

*Last updated: 2026-01-27*
*Part of TST-3 (Visual Regression Testing) from FUTURE_WORK.md*
