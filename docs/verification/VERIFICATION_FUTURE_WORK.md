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

**Current coverage**: 219/256 public operations verified (85.5%).
**Theoretical maximum** (excluding transcendental-blocked and batch operations): ~239/256 (93.4%).

## Operation Classification

| Category | Description | Count |
|----------|-------------|-------|
| **VERIFIED** | Has algebraic proofs (Verus/Coq) + Kani | 219 |
| **TRANSCENDENTAL-BLOCKED** | Requires sin/cos/atan2/tan; not provable algebraically | 10 |
| **HSL-BLOCKED** | Complex conditional FP logic (to_hsl, from_hsl) | 2 |
| **FP-SPECIFIC** | FP predicates (is_finite, is_nan) — Kani covers these | 3 |
| **COMPLEX GEOMETRY** | Rect transform_by_mat3/mat4, from_points (iterator) | 3 |
| **TYPE CONVERSIONS** | Vec2 as_ivec2, as_uvec2 | 2 |
| **BATCH** | Batch operations; follow trivially from single-op proofs | 7 |
| **NEW METHODS** | Color with_lightness/with_saturation/with_hue/rotate_hue + Rect min/max | ~10 |

---

## Priority 1: High-Value Algebraic Proofs

### P1.4: Mat4 Orthographic Projection — COMPLETED

**Effort**: MEDIUM | **Impact**: HIGH | **Status**: DONE (Phase 7)

All 11 proofs completed in `Mat4_Proofs.v` (Theorems 101-111):
- `mat4_orthographic_trace`: trace has closed form
- `mat4_orthographic_origin`: maps midpoint to origin
- `mat4_orthographic_diagonal`: off-diagonal structure
- `mat4_orthographic_symmetric`: symmetric bounds produce zero translation in x/y
- `mat4_orthographic_get_translation`: translation components have closed form
- `mat4_orthographic_near_corner_ndc`: maps (left, bottom, near) to (-1, -1, -1)
- `mat4_orthographic_far_corner_ndc`: maps (right, top, far) to (1, 1, 1)
- `mat4_orthographic_midpoint_ndc`: maps midpoint to origin (0, 0, 0)
- `mat4_orthographic_det`: determinant has closed form 8/(rml*tmb*fmn)
- `mat4_orthographic_invertible`: invertible when rml, tmb, fmn non-zero
- `mat4_orthographic_w_preserved`: w-component preserved under transform

### P1.5: Mat4 look_at View Matrix ✅ COMPLETED (Phase 10)

**Effort**: HIGH | **Impact**: HIGH | **Status**: COMPLETED (2026-02-04)

Proved 17 properties of `look_at(eye, target, up)` parameterized by
pre-computed orthonormal basis (s=side, u=up, f=forward, eye=position):
- ✅ Bottom row structural property (Theorem 112)
- ✅ Eye-to-origin mapping — fundamental view matrix property (Theorems 113, 119)
- ✅ Basis mapping: forward→-Z, side→+X, up→+Y (Theorems 114-116)
- ✅ W-component preservation — affine matrix (Theorem 117)
- ✅ Standard basis at origin = identity (Theorem 118)
- ✅ Translation column encodes eye position (Theorem 120)
- ✅ Rotation orthogonality: 6 column dot-product theorems (Theorems 121-126)
- ✅ Eye shift property (Theorem 127)
- ✅ 4 Kani harnesses: finite output, degenerate input, affine structure, parallel vectors
- Note: Uses orthonormal basis parameterization to avoid sqrt.
  All 17 Coq theorems machine-checked (0 admits). 4 Kani harnesses pass.

---

## Priority 3: Partial Verification Completion

These operations have SOME proofs but need additional verification layers.

### P3.1: Vector Length Verus Proofs — BLOCKED

**Effort**: MEDIUM | **Types**: Vec2/3/4 | **Status**: BLOCKED (sqrt)

Coq has `length_nonneg`, `length_zero` proofs. Verus integer-model proof would relate
`length` to `length_squared` via sqrt. Key property: `length(v) * length(v) = length_squared(v)`.

**Blocker**: sqrt does not exist in the integer specification model. The Z-based
computational bridge uses integer arithmetic only; sqrt requires either:
- A fixed-point sqrt approximation (introduces imprecision)
- Axiomatizing sqrt properties (violates zero-axioms policy)
- Moving to FP modeling via Flocq (different approach)

### P3.2: Vector Normalized Verus Proofs — BLOCKED

**Effort**: MEDIUM | **Types**: Vec2/3/4 | **Status**: BLOCKED (sqrt)

Coq has `normalized_length_sq`. Verus proof: `|normalized(v)|^2 = 1` for non-zero v.

**Blocker**: Same as P3.1 — normalized divides by length, which requires sqrt.

### P3.3: Vector Lerp Z-Compute Proofs — COMPLETED

**Effort**: MEDIUM | **Types**: Vec2/3/4 | **Status**: DONE (Phase 9)

Verus boundary-value lerp proofs completed. Z-based computational bridge lerp proofs
added in Phase 9 for all three vector types:
- Vec2: 3 new theorems (lerp_zero_zero, lerp_two, lerp_neg_one)
- Vec3: 3 new theorems (lerp_zero_zero, lerp_two, lerp_neg_one)
- Vec4: 3 new theorems (lerp_zero_zero, lerp_two, lerp_neg_one)

### P3.11: Utils lerp/clamp Verus Proofs — COMPLETED

**Effort**: MEDIUM | **Types**: Utils | **Status**: DONE (Phase 7)

All 33 Verus proof functions exist in `utils_proofs.rs`, covering scalar lerp
and clamp properties comprehensively.

### P2.5: Rect Accessors Z-Compute — COMPLETED

**Effort**: LOW | **Types**: Rect | **Status**: DONE (Phase 9)

Added to `Rect_Compute.v` in Phase 9:
- `zrect_from_pos_size` constructor + position/size accessors
- `zrect_bounds_min/max` accessor definitions
- 8 theorems: from_pos_size roundtrips, bounds correctness, position/size determination
- 1 computational test

---

## Priority 4: FP-Feasible Operations

These operations need floating-point modeling via Coq+Flocq 4.1.3 or extended Kani harnesses.

### P4.1: Vec2/3 floor/ceil/round ✅ COMPLETED (Phase 11)

**Effort**: MEDIUM | **Operations**: 6 (Vec2: 3, Vec3: 3) | **Status**: COMPLETED (2026-02-04)

Proved via Coq's `R_Ifp` module (`Int_part`, `up`, `archimed`, `tech_up`):
- `Rfloor(x) = IZR(Int_part(x))` with `floor(x) ≤ x < floor(x) + 1`
- `Rceil(x) = -Rfloor(-x)` with `x ≤ ceil(x) < x + 1`
- `Rround(x)` = half-away-from-zero (matching Rust `f32::round()`)
- 12 Vec2 theorems (Theorems 131-142) + 12 Vec3 theorems (Theorems 111-122)
- 6 Vec2 Z-compute + 6 Vec3 Z-compute (identity on integers)
- Note: Vec4 floor/ceil/round not implemented in Rust source — no proofs needed

### P4.2: Color Integer Conversion Functions ✅ COMPLETED (Phase 8)

**Effort**: MEDIUM | **Operations**: 6 | **Status**: COMPLETED (2026-01-31)

Already completed in Phase 8 (Session ykSJI): 21 R-based + 22 Z-based theorems
for `u8_to_f32`, `f32_to_u8`, `from_u8`, `from_rgb8`, `from_hex`, `from_hex_alpha`.

### P4.3: Color from_rgb8/from_rgb8_const ✅ COMPLETED (Phase 8)

**Effort**: LOW | **Operations**: 2 | **Status**: COMPLETED (2026-01-31)

Included in P4.2 completion (Phase 8).

### P4.4: Utils deg_to_rad/rad_to_deg Roundtrip ✅ COMPLETED (Phase 11)

**Effort**: MEDIUM | **Operations**: 2 | **Status**: COMPLETED (2026-02-04)

Proved over Coq reals (R) using PI constant:
- `rdeg_to_rad(d) = d * PI / 180`, `rrad_to_deg(r) = r * 180 / PI`
- Zero, linearity, notable values (90°→π/2, 180°→π, 360°→2π)
- Exact roundtrip: `rrad_to_deg(rdeg_to_rad(d)) = d` (PI ≠ 0)
- 20 new theorems in Utils.v (Theorems 38-56 + 1 helper lemma)

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

1. **FP work** (if Flocq available): Remaining P4 items are all COMPLETED.
   Next targets: P5 (transcendental-blocked, requires monitoring tool improvements)
   or extend Vec4 with floor/ceil/round if Rust source adds these operations.

2. **Documentation**: Update coverage tables, run `update-verification-counts.sh`.

**Completed items** (no longer actionable):
- P1.4 (Mat4 orthographic) — fully done in Phase 7
- P1.5 (Mat4 look_at) — fully done in Phase 10 (17 Coq theorems + 4 Kani harnesses)
- P2.5 (Rect accessors) — done in Phase 9
- P3.3 (Vector lerp Z-compute) — done in Phase 9
- P3.11 (Utils Verus) — done in Phase 7
- P4.1 (Vec2/3 floor/ceil/round) — done in Phase 11
- P4.2 (Color integer conversions) — done in Phase 8
- P4.3 (Color from_rgb8) — done in Phase 8
- P4.4 (Utils deg_to_rad/rad_to_deg) — done in Phase 11

**Blocked items** (awaiting tool improvements):
- P3.1 (Vector length Verus) — blocked by sqrt in integer model
- P3.2 (Vector normalized Verus) — blocked by sqrt in integer model

---

## Coverage Projection

| Milestone | Operations Verified | Coverage | Delta |
|-----------|--------------------:|----------|-------|
| **Current** | **219** | **85.5% (of 256)** | — |
| After Rect/Color expansion | ~230 | 89.8% | +11 |
| After Kani NaN-freedom harnesses | ~235 | 91.8% | +5 |
| **Theoretical maximum** (excl. blocked) | **~239** | **93.4%** | — |

**Note**: The operation count is 256 (including 24 Bounds operations). Reaching 100%
is not possible without transcendental function support (10 blocked operations),
batch operation proofs (7 low-value operations), and complex geometry/iterator
operations (3 blocked). The practical target is approximately 90–93% coverage.

---

*Last updated: 2026-02-05*
*Current coverage: 219/256 (85.5%)*
*All P4 items COMPLETED; 2 blocked (P3.1, P3.2)*
