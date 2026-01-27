# Mutation Testing Guide

**Status**: Active
**Created**: 2026-01-27
**Purpose**: Quantify test effectiveness through mutation analysis

---

## Overview

Mutation testing measures how well our test suite detects bugs by intentionally introducing small changes (mutations) to the code and checking if tests fail. A high mutation score indicates robust tests that catch real bugs.

### Why Mutation Testing?

| Metric | What It Tells You |
|--------|-------------------|
| Code Coverage | Which lines are executed |
| Mutation Score | Which bugs would be caught |

Code coverage shows *what* is tested; mutation score shows *how well* it's tested.

---

## Quick Reference

### Running Mutation Tests Locally

```bash
# Install cargo-mutants (one-time)
cargo install cargo-mutants

# Run on rource-math (critical crate)
cargo mutants -p rource-math --timeout=60 --jobs=2

# Run on rource-vcs
cargo mutants -p rource-vcs --timeout=60 --jobs=2

# Generate JSON report
cargo mutants -p rource-math --timeout=60 --output=mutants-output
```

### Interpreting Results

| Outcome | Meaning | Good/Bad |
|---------|---------|----------|
| **Killed** | Mutant detected by tests | ✅ Good |
| **Survived** | Mutant NOT detected | ❌ Bad (test gap) |
| **Timeout** | Test took too long | ⚠️ Needs investigation |
| **Unviable** | Mutation broke compilation | ➖ Ignored |

### Target Scores

| Crate | Target Score | Priority |
|-------|--------------|----------|
| rource-math | ≥90% | Critical (numerical correctness) |
| rource-vcs | ≥85% | High (parsing correctness) |
| rource-core | ≥80% | Medium |
| rource-render | ≥75% | Lower (visual bugs less critical) |

---

## Understanding Mutations

Cargo-mutants applies these types of mutations:

### Arithmetic Mutations
```rust
// Original
let sum = a + b;

// Mutants
let sum = a - b;  // Replace + with -
let sum = a * b;  // Replace + with *
let sum = a / b;  // Replace + with /
```

### Comparison Mutations
```rust
// Original
if x > threshold {

// Mutants
if x < threshold {   // Flip comparison
if x >= threshold {  // Change boundary
if x == threshold {  // Exact match
```

### Boolean Mutations
```rust
// Original
if enabled && valid {

// Mutants
if enabled || valid {  // && → ||
if !enabled && valid;  // Negate condition
if true {              // Always true
if false {             // Always false
```

### Return Value Mutations
```rust
// Original
fn is_valid() -> bool { true }

// Mutants
fn is_valid() -> bool { false }  // Flip return
fn is_valid() -> bool { Default::default() }  // Return default
```

---

## CI Integration

Mutation tests run automatically on PRs that modify critical crates.

### Workflow Location
`.github/workflows/mutation.yml`

### Trigger Conditions
- PRs modifying `crates/rource-math/**`
- PRs modifying `crates/rource-vcs/**`
- Manual dispatch via Actions UI

### Artifacts
Mutation reports are uploaded as artifacts and available for 30 days.

---

## Improving Mutation Score

When a mutant survives, it indicates a potential bug that tests would miss.

### Step 1: Identify Survivors
```bash
# Find surviving mutants
cargo mutants -p rource-math --output=mutants-output
cat mutants-output/caught.txt  # See what's working
cat mutants-output/unviable.txt  # Compilation failures (ignore)

# survivors.txt shows the gaps
cat mutants-output/survivors.txt
```

### Step 2: Analyze the Gap

Example survivor:
```
rource-math/src/vec2.rs:150: replace `+` with `-` in Vec2::add
```

This means: if someone accidentally changed `+` to `-` in `Vec2::add`, no test would catch it.

### Step 3: Add Targeted Tests

```rust
#[test]
fn test_vec2_add_correctness() {
    let a = Vec2::new(3.0, 4.0);
    let b = Vec2::new(1.0, 2.0);
    let result = a + b;

    // Specific value assertions kill mutation "replace + with -"
    assert_eq!(result.x, 4.0);  // 3 + 1, not 3 - 1
    assert_eq!(result.y, 6.0);  // 4 + 2, not 4 - 2
}
```

### Step 4: Re-run and Verify
```bash
cargo mutants -p rource-math --timeout=60
# Verify the survivor is now killed
```

---

## Performance Considerations

Mutation testing is computationally expensive:
- Each mutant requires a full test run
- Large crates can have thousands of mutants

### Optimization Tips

1. **Use release mode tests** for faster execution:
   ```bash
   cargo mutants -p rource-math -- --release
   ```

2. **Limit parallelism** to prevent resource exhaustion:
   ```bash
   cargo mutants -p rource-math --jobs=2
   ```

3. **Set appropriate timeouts** to skip slow mutants:
   ```bash
   cargo mutants -p rource-math --timeout=60
   ```

4. **Target specific files** when debugging:
   ```bash
   cargo mutants -p rource-math --file src/vec2.rs
   ```

---

## Mutation Testing Results

### rource-math

| Date | Mutants | Killed | Survived | Score | Notes |
|------|---------|--------|----------|-------|-------|
| 2026-01-27 | ~2403 | Partial | - | In Progress | Added targeted tests for color.rs |

#### Tests Added to Kill Mutants (2026-01-27)

The following tests were added to `crates/rource-math/src/color.rs` to kill mutants identified in bit manipulation and conversion functions:

**Bit Manipulation Tests**:
| Test | Target Function | Mutation Patterns Killed |
|------|-----------------|--------------------------|
| `test_from_hex_alpha_isolated_channels` | `from_hex_alpha` | `>>` shift amount changes, `&` mask changes |
| `test_to_rgba8_bit_positions` | `to_rgba8` | `<<` shift positions, `\|` channel ordering |
| `test_to_argb8_bit_positions` | `to_argb8` | `<<` shift positions, `\|` channel ordering |
| `test_to_abgr8_bit_positions` | `to_abgr8` | `<<` shift positions, `\|` channel ordering |
| `test_from_hex_bit_patterns` | `from_hex` | Bit extraction correctness |

**Boundary and Value Tests**:
| Test | Target Function | Mutation Patterns Killed |
|------|-----------------|--------------------------|
| `test_clamp_boundaries` | `clamp` | Comparison direction (`<` vs `>`), boundary values |
| `test_contrasting_luminance_boundary` | `contrasting` | `>` threshold comparison at 0.5 |
| `test_luminance_coefficients` | `luminance` | Coefficient multiplication values |

**Formula Verification Tests**:
| Test | Target Function | Mutation Patterns Killed |
|------|-----------------|--------------------------|
| `test_premultiplied_all_channels` | `premultiplied` | `*` multiplication with alpha |
| `test_blend_over_formula` | `blend_over` | Alpha blending formula operators |
| `test_fade_alpha_multiplication` | `fade` | `*` multiplication |

**HSL Conversion Tests**:
| Test | Target Function | Mutation Patterns Killed |
|------|-----------------|--------------------------|
| `test_hsl_achromatic` | `to_hsl`/`to_color` | Saturation = 0 path |
| `test_hsl_primary_hues` | `to_hsl` | Hue calculation branches |
| `test_hsl_saturation_lightness_relation` | `to_color` | q/p calculation formulas |
| `test_hsl_hue_rotation` | `rotate_hue` | Modulo operator, negative handling |

**Total**: 19 new tests added, targeting 20+ mutation-prone code patterns.

### rource-vcs

| Date | Mutants | Killed | Survived | Score | Notes |
|------|---------|--------|----------|-------|-------|
| TBD | TBD | TBD | TBD | TBD% | Pending baseline run |

---

## Common Survival Patterns

### Pattern 1: Missing Boundary Tests
```rust
// Survives because no test checks x == threshold
if x > threshold { ... }
```
**Fix**: Add tests for boundary conditions (x = threshold, x = threshold ± 1)

### Pattern 2: Insufficient Precision Tests
```rust
// Survives because tests use approx_eq with loose tolerance
let result = expensive_calculation();
```
**Fix**: Add exact value assertions where mathematically provable

### Pattern 3: Missing Error Path Tests
```rust
// Survives because error path isn't tested
fn parse(s: &str) -> Result<T, Error> {
    if s.is_empty() { return Err(...); }  // Untested
    ...
}
```
**Fix**: Add tests for error conditions

### Pattern 4: Redundant Code
```rust
// Survives because the code is never actually needed
if unlikely_condition {
    handle_edge_case();  // Dead code?
}
```
**Fix**: Either add tests for the edge case, or remove the dead code

---

## FAQ

### Why not 100% mutation score?

Some mutations are impractical to test:
- Performance optimizations (functionally equivalent)
- Logging/debugging code
- Platform-specific paths

Target 80-90% for critical code, 70-80% for less critical.

### How often should we run mutation tests?

- **CI**: On PRs modifying critical crates
- **Manual**: Weekly or after major changes
- **Full suite**: Before releases

### What about slow tests?

Use `--timeout` to skip mutants that take too long. Timeouts are tracked separately and can be investigated later.

---

## References

- [cargo-mutants documentation](https://github.com/sourcefrog/cargo-mutants)
- [Mutation Testing Wikipedia](https://en.wikipedia.org/wiki/Mutation_testing)
- [CLAUDE.md Testing Standards](../CLAUDE.md#testing--quality-standards)
