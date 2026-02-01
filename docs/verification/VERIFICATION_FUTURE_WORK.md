# Verification Future Work

This document tracks remaining verification work items for `rource-math`, organized
by priority. Each item includes effort estimate, expected impact, and implementation
guidance.

For the current state overview, see [FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md).
For completed work history, see [VERIFICATION_CHRONOLOGY.md](VERIFICATION_CHRONOLOGY.md).

---

## Table of Contents

- [Coverage Status](#coverage-status)
- [Operation Classification](#operation-classification)
- [Priority 1: High-Value Algebraic Proofs](#priority-1-high-value-algebraic-proofs)
- [Priority 3: Partial Verification Completion](#priority-3-partial-verification-completion)
- [Priority 4: FP-Feasible Operations](#priority-4-fp-feasible-operations)
- [Priority 5: Transcendental-Blocked](#priority-5-transcendental-blocked)
- [Priority 6: Batch Operations](#priority-6-batch-operations)
- [Session Execution Guide](#session-execution-guide)
- [Coverage Projection](#coverage-projection)

---

## Coverage Status

**Current coverage**: 163/253 public operations verified (64.4%).
**Theoretical maximum** (excluding transcendental-blocked and batch operations): ~236/253 (93.3%).

## Operation Classification

| Category | Description | Count |
|----------|-------------|-------|
| **VERIFIED** | Has algebraic proofs (Verus/Coq) + Kani | 163 |
| **ALGEBRAIC GAP** | CAN be proved algebraically, no proof yet | ~13 |
| **PARTIALLY VERIFIED** | Some proofs exist but missing verification layers | ~17 |
| **FP-FEASIBLE** | Requires FP modeling; feasible via Flocq or Kani | ~13 |
| **TRANSCENDENTAL-BLOCKED** | Requires sin/cos/atan2/tan; not provable | 10 |
| **BATCH** | Batch operations; follow trivially from single-op proofs | 7 |

---

## Priority 1: High-Value Algebraic Proofs

### P1.4: Mat4 Orthographic Projection — PARTIALLY COMPLETED

**Effort**: MEDIUM | **Impact**: HIGH

Spec added to `Mat4.v`. Five proofs completed in `Mat4_Proofs.v`:
- `mat4_orthographic_trace`: trace has closed form `(2/rml + 2/tmb - 2/fmn + 1)`
- `mat4_orthographic_origin`: maps midpoint to origin
- `mat4_orthographic_diagonal`: off-diagonal structure (zero off-diagonal elements)
- `mat4_orthographic_symmetric`: symmetric bounds produce zero translation in x/y
- `mat4_orthographic_get_translation`: translation components have closed form

**Remaining**:
- NDC mapping proof: `orthographic` maps `(left, bottom, near)` to `(-1, -1, -1)` (requires `mat4_transform_vec4` spec — now available)
- `det(orthographic(...))` closed-form value

### P1.5: Mat4 look_at View Matrix

**Effort**: HIGH | **Impact**: HIGH

Prove properties of `look_at(eye, target, up)`:
- The forward/right/up vectors form an orthonormal basis
- Translation component correctly positions the camera
- Note: `normalize()` (sqrt) makes full algebraic proof difficult.
  Prove structural properties assuming unit inputs.

---

## Priority 3: Partial Verification Completion

These operations have SOME proofs but need additional verification layers.

### P3.1: Vector Length Verus Proofs

**Effort**: MEDIUM | **Types**: Vec2/3/4

Coq has `length_nonneg`, `length_zero` proofs. Add Verus integer-model proof relating
`length` to `length_squared` via sqrt. Key property: `length(v) * length(v) = length_squared(v)`.

### P3.2: Vector Normalized Verus Proofs

**Effort**: MEDIUM | **Types**: Vec2/3/4

Coq has `normalized_length_sq`. Add Verus proof: `|normalized(v)|^2 = 1` for non-zero v.

### P3.3: Vector Lerp Z-Compute Proofs — VERUS DONE, Z REMAINING

**Effort**: MEDIUM | **Types**: Vec2/3/4

Verus boundary-value lerp proofs completed. Remaining: Coq Z-based computational
bridge lerp proofs for all three vector types.

### P3.11: Utils lerp/clamp Verus Proofs

**Effort**: MEDIUM | **Types**: Utils

Coq R+Z have comprehensive proofs for scalar lerp and clamp.
Add Verus proofs for the same properties.

### P2.5 Remaining: Rect Accessors

**Effort**: LOW | **Types**: Rect

Remaining: `from_pos_size`, `position`, `size`, `to_bounds` (minor accessors).

---

## Priority 4: FP-Feasible Operations

These operations need floating-point modeling via Coq+Flocq 4.1.3 or extended Kani harnesses.

### P4.1: Vec2/3/4 floor/ceil/round

**Effort**: MEDIUM | **Operations**: 9

Prove via Flocq: `floor(x) <= x < floor(x) + 1`, `ceil(x) - 1 < x <= ceil(x)`.
Flocq provides `Zfloor`/`Zceil` for IEEE 754 floats.

### P4.2: Color Integer Conversion Functions

**Effort**: MEDIUM | **Operations**: 6

`from_hex`, `from_hex_alpha`, `from_rgba8`, `to_rgba8`, `to_argb8`, `to_abgr8`:
Prove output components are in [0.0, 1.0] range after u8/u32-to-f32 conversion.

### P4.3: Color from_rgb8/from_rgb8_const

**Effort**: LOW | **Operations**: 2

Same approach as P4.2.

### P4.4: Utils deg_to_rad/rad_to_deg Roundtrip

**Effort**: MEDIUM | **Operations**: 2

Requires modeling pi as a Flocq binary32 value. Prove finiteness and approximate
roundtrip: `|rad_to_deg(deg_to_rad(d)) - d| < epsilon`.

---

## Priority 5: Transcendental-Blocked

These operations require `sin`, `cos`, `atan2`, or `tan` and CANNOT be proved
algebraically with current tools. Kani harnesses already verify NaN-freedom
and finiteness where possible.

| Operation | Type | Blocker | Current Kani Coverage |
|-----------|------|---------|----------------------|
| `from_angle(radians)` | Vec2 | sin/cos | `from_angle_no_nan` |
| `angle(self)` | Vec2 | atan2 | None |
| `rotate(self, radians)` | Vec2 | sin/cos | `rotate_no_nan` |
| `rotation(radians)` | Mat3 | sin/cos | `rotation_no_nan` |
| `rotation_x(radians)` | Mat4 | sin/cos | `rotation_x_no_nan` |
| `rotation_y(radians)` | Mat4 | sin/cos | `rotation_y_no_nan` |
| `rotation_z(radians)` | Mat4 | sin/cos | `rotation_z_no_nan` |
| `perspective(...)` | Mat4 | tan | Blocked (Kani #2423) |
| `to_hsl(self)` | Color | Complex FP | None |
| `from_hsl(h, s, l)` | Color | Complex FP | None |

**Mitigation strategy**: Continue relying on Kani NaN-freedom harnesses.
Monitor Verus/Kani developments for transcendental function support.
Consider Coq+Flocq formalization of sin/cos error bounds if needed for publication.

---

## Priority 6: Batch Operations

Vec2 has 7 `batch_*` functions (batch_add, batch_sub, batch_scale, batch_normalize,
batch_dot, batch_lerp, batch_clamp). These apply single-operation logic element-wise.
Correctness follows trivially from the corresponding single-operation proofs.

Could add loop-invariant Kani harnesses if desired, but this is low value since
the per-element operations are already triple-verified.

---

## Session Execution Guide

For a new session focused on increasing verification coverage, follow this order:

1. **Warm-up**: Start with quick-win remaining items (P2.5 remaining, P3.3 Z-compute).
   These are `reflexivity` or `simpl; ring` proofs that build momentum.

2. **Main work**: Pick ONE item from P1 (orthographic remaining or look_at). The
   orthographic NDC mapping uses `mat4_transform_vec4` spec (now available). The
   look_at proof gives the highest academic impact per proof.

3. **Fill gaps**: Work through P3 items, prioritizing those that complete a type's
   coverage (e.g., close all Vec3 gaps).

4. **FP work** (if Flocq available): P4 items extend the FP error bounds layer.

5. **Documentation**: Update coverage tables, run `update-verification-counts.sh`.

---

## Coverage Projection

| After Priority | Operations Verified | Coverage | Delta |
|----------------|--------------------:|----------|-------|
| **Current** | **163** | **64.4% (of 253)** | — |
| After remaining P3 | ~170 | 67.2% | +13 |
| After P1.4-P1.5 (ortho, look_at) | ~172 | 68.0% | +2 |
| After P4 (FP feasible) | ~185 | 73.1% | +13 |
| **Theoretical maximum** (excl. blocked) | **~236** | **93.3%** | — |

**Note**: The operation count is 253 (including 23 Bounds operations). Reaching 100%
is not possible without transcendental function support (10 blocked operations) and
batch operation proofs (7 low-value operations). The practical target is approximately
85–90% coverage, which would require completing P1 through P4.

---

*Last updated: 2026-01-31*
*Current coverage: 163/253 (64.4%)*
*Remaining P1–P4 items: 6 priority items*
