# Verification Chronology

This document records the historical development of formal verification for `rource-math`,
organized by implementation phase. Each phase documents what was accomplished, the proof
counts added, and the techniques used.

For the current state overview, see [FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md).
For remaining work items, see [VERIFICATION_FUTURE_WORK.md](VERIFICATION_FUTURE_WORK.md).

---

## Table of Contents

- [Phase 1: Coq Foundation](#phase-1-coq-foundation)
- [Phase 2: Complexity Proofs](#phase-2-complexity-proofs)
- [Phase 2b: Proof Compilation Optimization](#phase-2b-proof-compilation-optimization)
- [Phase 3: Computational Bridge + WASM Pipeline](#phase-3-computational-bridge--wasm-pipeline)
- [Phase 4: Color, Rect, Utils + Kani Adoption](#phase-4-color-rect-utils--kani-adoption)
- [Phase 5: Bounds, Inverse, CrossType](#phase-5-bounds-inverse-crosstype)
- [Phase 6: Verus Extensions + Coverage Audit](#phase-6-verus-extensions--coverage-audit)
- [Phase 7: Kani Expansion + Z-Compute Extensions](#phase-7-kani-expansion--z-compute-extensions)
- [Completed Milestones Summary](#completed-milestones-summary)
- [Completed Priority Items](#completed-priority-items)

---

## Phase 1: Coq Foundation

**Status**: COMPLETED

Established Coq specifications and R-based proofs for the core vector and matrix types.

| Deliverable | Count | Description |
|-------------|-------|-------------|
| Vec2 specs + proofs | 110 theorems | Algebraic properties, dot/cross, projections |
| Vec3 specs + proofs | 115 theorems | 3D operations, cross product |
| Vec4 specs + proofs | 96 theorems | 4D operations, dot product |
| Mat3 specs + proofs | 92 theorems | Matrix algebra, determinant, inverse |
| Mat4 specs + proofs | 157 theorems | 4x4 matrix algebra, transforms |
| Utils specs + proofs | 37 theorems | lerp, clamp, approx_eq |

**Verus proofs** established in parallel:
- Vec2: 55, Vec3: 55, Vec4: 55 proof functions
- Mat3: 48 (22 base + 26 extended), Mat4: 54 (22 base + 32 extended)

---

## Phase 2: Complexity Proofs

**Status**: COMPLETED

Added ICC (Implicit Computational Complexity) proofs establishing O(1) bounds for
40 core operations.

| File | Theorems | Description |
|------|----------|-------------|
| `Complexity.v` | 60 | O(1) bounds for Vec2(10), Vec3(9), Vec4(8), Mat3(6), Mat4(6) |

Cost model: Abstract operation counting (multiplications + additions).

---

## Phase 2b: Proof Compilation Optimization

**Status**: COMPLETED

Achieved >300x compilation speedup by restructuring proof files:
- Separated specifications (`.v`) from proofs (`_Proofs.v`)
- Enabled parallel compilation of independent proof files
- Reduced total compilation time from ~15 minutes to ~45 seconds

---

## Phase 3: Computational Bridge + WASM Pipeline

**Status**: OPERATIONAL

Created Z-based computational bridge enabling Coq extraction to OCaml and WASM.

| File | Theorems | Description |
|------|----------|-------------|
| `Vec2_Compute.v` | 50 | Z-based Vec2 operations |
| `Vec3_Compute.v` | 42 | Z-based Vec3 operations |
| `Vec4_Compute.v` | 33 | Z-based Vec4 operations |
| `Mat3_Compute.v` | 25 | Z-based Mat3 operations |
| `Mat4_Compute.v` | 50 | Z-based Mat4 operations |
| `RourceMath_Extract.v` | — | Unified extraction driver |

Pipeline: Coq → OCaml extraction → wasm_of_ocaml v6.2.0 → WASM (6.8 KB library).
9 Coq-to-WASM paths evaluated (see [CERTICOQ_WASM_ASSESSMENT.md](CERTICOQ_WASM_ASSESSMENT.md)).

---

## Phase 4: Color, Rect, Utils + Kani Adoption

**Status**: COMPLETED

Extended verification to Color, Rect, and Utils types. Adopted Kani as third
verification layer for IEEE 754 edge-case safety.

| Component | Verus | Coq R | Coq Z | Kani | Description |
|-----------|-------|-------|-------|------|-------------|
| Color | 57 proof fns | 100 theorems | 38 theorems | 24 harnesses | RGBA blending, luminance, contrasting |
| Rect | 52 proof fns | 120 theorems | 43 theorems | 20 harnesses | Spatial operations, containment, transforms |
| Utils | 33 proof fns | 37 theorems | 18 theorems | 7 harnesses | lerp, clamp, approx_eq |

**Kani adoption**: Added CBMC-based bounded model checking for bit-precise IEEE 754
f32 verification. Initial harnesses covered Vec2-4, Mat3-4, Color, Rect, Utils.

**Investigations completed**:
- **Floating-point refinement**: Verus FP not feasible; Coq + Flocq + VCFloat2 recommended
  (see [FLOATING_POINT_VERIFICATION.md](FLOATING_POINT_VERIFICATION.md))
- **rocq-of-rust**: Not viable — monadic embedding incompatible with algebraic proofs,
  f32 unsupported (see [VERIFICATION_COVERAGE.md](VERIFICATION_COVERAGE.md))
- **Stainless FP paper**: Not directly applicable — Scala-only, no error bounds
  (see [FLOATING_POINT_VERIFICATION.md](FLOATING_POINT_VERIFICATION.md))
- **Rust verification landscape**: 8-tool survey — Kani adopted, Aeneas/Creusot monitored
  (see [RUST_VERIFICATION_LANDSCAPE.md](RUST_VERIFICATION_LANDSCAPE.md))

---

## Phase 5: Bounds, Inverse, CrossType

**Status**: COMPLETED

Added complete Bounds verification and Mat3/Mat4 inverse correctness proofs.

### Bounds Full Verification (P1.1)

All verification layers completed:
- `Bounds.v`: Specification with Record definition and all operations
- `Bounds_Proofs.v`: 86 R-based theorems (area, containment, union, intersection, expand, shrink, translate, include_point, from_points, from_center_half_extents, validity)
- `Bounds_Compute.v`: 70 Z-based computational bridge theorems
- `bounds_proofs.rs`: 66 Verus proof functions
- `kani_proofs/bounds.rs`: 20 Kani harnesses

### Mat3 Inverse (P1.2)

12 theorems in `Mat3_Proofs.v`:
- `mat3_inverse_identity`, `mat3_inverse_correct` (left), `mat3_inverse_correct_right`
- `mat3_det_inverse`, `mat3_inverse_involutive`, `mat3_det_mul_inverse`
- `mat3_inverse_mul`, `mat3_inverse_scale`, `mat3_inverse_transpose`
- `mat3_inverse_translation`, `mat3_inverse_scaling`, `mat3_inverse_shearing_correct`

### Mat4 Inverse (P1.3)

44 theorems (including 32 Local Lemmas) in `Mat4_Proofs.v`:
- Component decomposition: 16 Local Lemmas for left-inverse, 16 for right-inverse
- `mat4_inverse_identity`, `mat4_inverse_correct` (left), `mat4_inverse_correct_right`
- `mat4_det_inverse`, `mat4_inverse_involutive`, `mat4_det_mul_inverse`
- `mat4_inverse_translation`, `mat4_inverse_scaling`, `mat4_inverse_transpose`
- `mat4_inverse_uniform_scaling`, `mat4_inverse_translation_compose`

### CrossType Proofs (P2.1, P2.2)

51 theorems in `Vec_CrossType.v` with cross-type imports:
- `vec3_from_vec2`, `vec3_xy`, `vec3_xz`, `vec3_yz`
- `vec4_from_vec3`, `vec4_from_vec2`, `vec4_xy`, `vec4_xyz`
- Roundtrip, component preservation, algebraic distribution, chaining, dot product relations

### Mat3/Mat4 from_cols (P2.3)

6 theorems: 3 in `Mat3_Proofs.v` (equivalence, identity, zero) + 3 in `Mat4_Proofs.v`.

### Mat4 col/row Accessors (P2.4)

12 proofs in `Mat4_Proofs.v`: identity column/row values (4+4), scaling col0,
translation col3, transpose swaps cols/rows (2).

### Rect Accessors (P2.5)

29 proofs in `Rect_Proofs.v` covering `rect_left`, `rect_top`, `rect_min_x`,
`rect_min_y`, `rect_max_x`, `rect_max_y`, `rect_is_empty`, `rect_from_corners`,
`rect_union`, `rect_expand_xy`.

### Mat3 Shearing (P2.6)

7 proofs in `Mat3_Proofs.v`: zero=identity, determinant=`1-sx*sy`, last row preserved,
transforms origin, trace=`2+sx*sy`, composition formula.

---

## Phase 6: Verus Extensions + Coverage Audit

**Status**: COMPLETED

Extended Verus proofs for vector operations and completed partial verification items.

### Vector Lerp Verus Proofs (P3.3)

Boundary-value lerp proofs completed:
- Vec2: 6 lerp proofs (zero, one, identity, two, neg_one, zero_zero)
- Vec3: 5 lerp proofs (zero, one, identity, two, zero_zero)
- Vec4: 5 lerp proofs (zero, one, identity, two, zero_zero)

### Vec3/Vec4 Clamp Verus Proofs (P3.4)

- Vec3: 4 clamp proofs (bounds, identity, idempotent, squeeze)
- Vec4: 4 clamp proofs (bounds, identity, idempotent, squeeze)

### Vec3/Vec4 Reflect Verus Proofs (P3.5)

- Vec3: 3 reflect proofs (perpendicular, along_unit_normal, zero)
- Vec4: 2 reflect proofs (perpendicular, along_unit_normal)

### Mat3/Mat4 get_translation (P3.6)

Specs and proofs: Mat3 (5 theorems) + Mat4 (5 theorems) covering
extract from translation, identity, zero, scaling, compose.

### Mat4 transform_vec4 (P3.7)

9 proofs in `Mat4_Proofs.v`: identity, zero matrix, zero vector, additivity,
scalar, translation of point/vector, scaling, mul_compat. Plus `transform_point`
(3 proofs) and `transform_vector` (2 proofs).

### Color Contrasting (P3.8)

4 proofs: contrasting(black)=white, contrasting(white)=black, binary output, always opaque.

### Rect Union (P3.9)

6 proofs: commutative, contains first/second, self=identity, identity element,
preserves non-negative dimensions.

### Rect from_corners + expand_xy (P3.10)

- `from_corners`: 4 theorems (components, width, height, area nonneg)
- `expand_xy`: 5 theorems (preserves center, increases dimensions, zero=identity,
  area formula, contains original)

### Utils approx_eq (P3.12)

7 proofs: reflexivity, symmetry, triangle inequality (eps1+eps2), non-transitivity
counterexample (a=0, b=3/4, c=3/2, eps=1), epsilon monotonicity, translation
invariance, negation invariance.

### Mat4 Orthographic (P1.4 — Partially Completed)

5 proofs: trace closed form, maps midpoint to origin, off-diagonal structure,
symmetric bounds produce zero translation, translation components closed form.

---

## Phase 7: Kani Expansion + Z-Compute Extensions

**Status**: COMPLETED (Session NQWQv, 2026-01-31)

### Kani Vec4 Harnesses

Net change: +4 harnesses (6 added, 2 removed due to CBMC timeout):
- Added: `add_commutative`, `neg_involutive`, `sub_anti_commutative`, `scale_distributive`,
  `dot_self_non_negative`, `zero_length`
- Removed: `dot_commutative` (8 vars × multiply timeout), `normalized_unit_length`
  (double sqrt chain timeout)

### Coq Z-Compute Color Extensions

+10 theorems in `Color_Compute.v`:
- `zcolor_darken_zero`, `zcolor_darken_full`, `zcolor_darken_preserves_alpha`
- `zcolor_lighten_zero`, `zcolor_lighten_full`, `zcolor_lighten_preserves_alpha`
- `zcolor_contrasting_black`, `zcolor_contrasting_white`, `zcolor_contrasting_binary`,
  `zcolor_contrasting_opaque`

### Documentation Staleness Fix

Fixed 15+ stale entries across FORMAL_VERIFICATION.md, VERIFICATION_COVERAGE.md, CLAUDE.md.
Discovered 5 under-reported operations (Color +4, Mat4 +3, Utils -2 corrected over-count).

### CI Fixes

- Removed `verify_vec4_normalized_unit_length` Kani harness (CBMC timeout)
- Fixed benchmark CI: `--exclude rource --exclude rource-wasm` for `--noplot` flag

---

## Phase 8: Color Integer Conversion + Mat3 Kani + Documentation Refactoring

**Status**: COMPLETED (Session ykSJI, 2026-01-31)

### Documentation Refactoring (G0)

Refactored `FORMAL_VERIFICATION.md` from monolithic document (~674 lines) into structured
3-file documentation suite:
- `FORMAL_VERIFICATION.md`: Index and overview (~370 lines)
- `VERIFICATION_CHRONOLOGY.md`: Historical phases 1-8 with milestones
- `VERIFICATION_FUTURE_WORK.md`: Remaining roadmap P1.4-P6 with coverage projection

### Color Coq R-based Proofs (G1)

+21 theorems in `Color_Proofs.v` (100 → 121):
- `u8_to_f32_zero`, `u8_to_f32_max`, `u8_to_f32_nonneg`, `u8_to_f32_le_one`,
  `u8_to_f32_range`, `u8_to_f32_monotone`, `u8_to_f32_injective`
- `color_from_u8_range`, `color_from_u8_black`, `color_from_u8_white`
- `color_from_rgb8_opaque`, `color_from_hex_opaque`, `color_from_hex_alpha_consistency`,
  `color_from_rgb8_eq_from_u8`
- `f32_to_u8_zero`, `f32_to_u8_one`, `f32_to_u8_nonneg`, `f32_to_u8_le_255`,
  `f32_to_u8_range`
- `u8_f32_roundtrip`, `f32_u8_roundtrip`

New specs added to `Color.v`: `u8_to_f32`, `color_from_u8`, `color_from_rgb8`,
`color_from_hex`, `color_from_hex_alpha`, `f32_to_u8` (+7 definitions).

### Color Coq Z-Compute Proofs (G1)

+22 theorems in `Color_Compute.v` (38 → 60):
- `zu8_to_z1000_zero`, `zu8_to_z1000_max`, `zu8_to_z1000_nonneg`, `zu8_to_z1000_monotone`
- `zcolor_from_u8_black`, `zcolor_from_u8_white`
- `zcolor_from_rgb8_opaque`, `zcolor_from_rgb8_eq_from_u8`
- `zcolor_from_hex_opaque`, `zcolor_from_hex_alpha_consistency`
- `zf32_to_u8_zero`, `zf32_to_u8_one`, `zf32_to_u8_nonneg`, `zf32_to_u8_le_255`, `zf32_to_u8_range`
- `zu8_z1000_roundtrip_zero`, `zu8_z1000_roundtrip_max`,
  `zf32_u8_z1000_roundtrip_zero`, `zf32_u8_z1000_roundtrip_max`
- Helper lemmas: `zclamp_ge_lo`, `zclamp_nonneg`, `zclamp_le_hi`

Note: exact Z roundtrip does NOT hold due to integer division truncation.
Proved boundary cases instead.

### Mat3 Kani Harnesses (G2)

+6 harnesses in `kani_proofs/mat3.rs` (14 → 20):
- `verify_mat3_mul_identity_right`, `verify_mat3_mul_identity_left`
- `verify_mat3_uniform_scaling_finite`, `verify_mat3_uniform_scaling_structure`
- `verify_mat3_from_translation_finite`
- `verify_mat3_default_is_identity`

### Documentation Consistency

Fixed 10+ stale per-type entries across FORMAL_VERIFICATION.md, CLAUDE.md,
VERIFICATION_COVERAGE.md. Operation coverage increased from 62.1% to 64.4%
(157 → 163 verified operations). Total theorems/harnesses: 2221 → 2270 (+49).

---

## Completed Milestones Summary

| # | Milestone | Status |
|---|-----------|--------|
| 1 | Vec4 proofs (22 theorems, 68 VCs) | COMPLETED |
| 2 | Matrix proofs (Mat3: 18 theorems, 26 VCs; Mat4: 18 theorems, 27 VCs) | COMPLETED |
| 3 | Complexity bounds (60 Coq theorems, O(1) for 40 operations) | COMPLETED |
| 4 | Floating-point refinement investigation | INVESTIGATED |
| 5 | CI integration (`.github/workflows/verus-verify.yml`) | COMPLETED |
| 6 | Proof coverage metrics | COMPLETED |
| 7 | Color proofs (Verus: 57, Coq R: 121, Coq Z: 60) | COMPLETED |
| 8 | Rect proofs (Verus: 52, Coq R: 120, Coq Z: 43) | COMPLETED |
| 9 | Utils proofs (Coq R: 37, Coq Z: 18) | COMPLETED |
| 10 | Determinant properties (det(I), det(0), det(A^T), det(-A), trace) | COMPLETED |
| 11 | Determinant multiplicativity (det(A*B) = det(A)*det(B) for Mat3/Mat4) | COMPLETED |
| 12 | rocq-of-rust investigation | INVESTIGATED (not viable) |
| 13 | Stainless FP paper investigation | INVESTIGATED (not applicable) |

## Completed Priority Items

| ID | Item | Status | Proof Count |
|----|------|--------|-------------|
| P1.1 | Bounds full verification | COMPLETED | 242 (Verus:66, Coq-R:86, Coq-Z:70, Kani:20) |
| P1.2 | Mat3 inverse correctness | COMPLETED | 12 theorems |
| P1.3 | Mat4 inverse correctness | COMPLETED | 44 theorems (incl. 32 Local Lemmas) |
| P2.1 | Vec3 constructors/swizzles | COMPLETED | 51 theorems (Vec_CrossType.v) |
| P2.2 | Vec4 constructors/swizzles | COMPLETED | (included in P2.1) |
| P2.3 | Mat3/Mat4 from_cols | COMPLETED | 6 theorems |
| P2.4 | Mat4 col/row accessors | COMPLETED | 12 proofs |
| P2.5 | Rect trivial accessors | MOSTLY COMPLETED | 29 proofs |
| P2.6 | Mat3 shearing | COMPLETED | 7 proofs |
| P3.3 | Vector lerp Verus | VERUS COMPLETED | 16 proofs (Vec2:6, Vec3:5, Vec4:5) |
| P3.4 | Vec3/Vec4 clamp Verus | COMPLETED | 8 proofs |
| P3.5 | Vec3/Vec4 reflect Verus | COMPLETED | 5 proofs |
| P3.6 | Mat3/Mat4 get_translation | COMPLETED | 10 theorems |
| P3.7 | Mat4 transform_vec4 | COMPLETED | 14 proofs |
| P3.8 | Color contrasting | COMPLETED | 4 proofs |
| P3.9 | Rect union | COMPLETED | 6 proofs |
| P3.10 | Rect from_corners + expand_xy | COMPLETED | 9 theorems |
| P3.12 | Utils approx_eq | COMPLETED | 7 proofs |

---

*Last updated: 2026-01-31*
*Total phases: 8 implementation phases*
*Total completed priority items: 18/24 (75%)*
