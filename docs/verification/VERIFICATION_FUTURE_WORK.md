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

**Current coverage**: 170/255 public operations verified (66.7%).
**Theoretical maximum** (excluding transcendental-blocked and batch operations): ~238/255 (93.3%).

## Operation Classification

| Category | Description | Count |
|----------|-------------|-------|
| **VERIFIED** | Has algebraic proofs (Verus/Coq) + Kani | 170 |
| **ALGEBRAIC GAP** | CAN be proved algebraically, no proof yet | ~13 |
| **PARTIALLY VERIFIED** | Some proofs exist but missing verification layers | ~17 |
| **FP-FEASIBLE** | Requires FP modeling; feasible via Flocq or Kani | ~13 |
| **TRANSCENDENTAL-BLOCKED** | Requires sin/cos/atan2/tan; not provable | 10 |
| **BATCH** | Batch operations; follow trivially from single-op proofs | 7 |

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

1. **FP work** (if Flocq available): P4 items extend the FP error bounds layer.
   P4.1 (floor/ceil/round) and P4.2/P4.3 (Color integer conversions) are the
   most impactful remaining items.

2. **Documentation**: Update coverage tables, run `update-verification-counts.sh`.

**Completed items** (no longer actionable):
- P1.4 (Mat4 orthographic) — fully done in Phase 7
- P1.5 (Mat4 look_at) — fully done in Phase 10 (17 Coq theorems + 4 Kani harnesses)
- P2.5 (Rect accessors) — done in Phase 9
- P3.3 (Vector lerp Z-compute) — done in Phase 9
- P3.11 (Utils Verus) — done in Phase 7

**Blocked items** (awaiting tool improvements):
- P3.1 (Vector length Verus) — blocked by sqrt in integer model
- P3.2 (Vector normalized Verus) — blocked by sqrt in integer model

---

## Coverage Projection

| After Priority | Operations Verified | Coverage | Delta |
|----------------|--------------------:|----------|-------|
| **Current** | **170** | **66.7% (of 255)** | — |
| After remaining P3 | ~178 | 69.8% | +8 |
| After P4 (FP feasible) | ~191 | 74.9% | +13 |
| **Theoretical maximum** (excl. blocked) | **~238** | **93.3%** | — |

**Note**: The operation count is 255 (including 23 Bounds operations). Reaching 100%
is not possible without transcendental function support (10 blocked operations) and
batch operation proofs (7 low-value operations). The practical target is approximately
85–90% coverage, which would require completing P1 through P4.

---

*Last updated: 2026-02-04*
*Current coverage: 170/255 (66.7%)*
*Remaining actionable P4 items: 4 (P4.1–P4.4); 2 blocked (P3.1, P3.2)*
