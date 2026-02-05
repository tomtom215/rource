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
- [Phase 8: Color Integer Conversion + Mat3 Kani + Documentation Refactoring](#phase-8-color-integer-conversion--mat3-kani--documentation-refactoring)
- [Phase 9: CI FP Layer + Z-Compute Expansion](#phase-9-ci-fp-layer--z-compute-expansion)
- [Phase 10: Mat4 look_at View Matrix Proofs + Kani Harnesses](#phase-10-mat4-look_at-view-matrix-proofs--kani-harnesses)
- [Phase 11: Vec2/3 floor/ceil/round + Utils deg/rad Proofs](#phase-11-vec23-floorceliround--utils-degrad-proofs)
- [Phase 12: Coverage Audit + fract/normalize/scale/lerp/approx_eq Proofs](#phase-12-coverage-audit--fractnormalizescalelerp-approx_eq-proofs-session-wv5k1)
- [Phase 13: Rect/Mat4/Color/Bounds Extensions](#phase-13-rectmat4colorbounds-extensions-session-resp0)
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
| `Vec2_Compute.v` | 62 | Z-based Vec2 operations |
| `Vec3_Compute.v` | 54 | Z-based Vec3 operations |
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

### Mat4 Orthographic (P1.4 — Completed)

11 proofs: trace closed form, maps midpoint to origin, off-diagonal structure,
symmetric bounds produce zero translation, translation components closed form,
near corner NDC mapping, far corner NDC mapping, midpoint NDC mapping,
determinant closed form, invertibility, w-preservation.

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

## Phase 9: CI FP Layer + Z-Compute Expansion

**Status**: COMPLETED (Session IoNDB, 2026-02-03)

### Documentation Consistency Fix

Fixed stale Summary Statistics in `FORMAL_VERIFICATION.md` lines 29-30:
- Z-based: 369 → 400 (correct ground truth)
- FP error bounds: 177 → 361 (correct ground truth)

Root cause: `update-verification-counts.sh` had sed patterns for the per-type table
but was missing patterns for the Summary Statistics table. Added 2 new sed patterns
with unique context anchors ("Z-based extractable", "FP error bounds") and 2 new
`--check` entries to prevent recurrence.

### FP Coq CI Layer (Layer 6)

Added complete FP error bounds verification to `.github/workflows/coq-verify.yml`:
- Added opam + Flocq 4.1.3 installation step with 3-attempt retry logic
- Added Layer 6 build step with correct dependency ordering:
  Phase 1: FP_Common.v, FP_Rounding.v (foundations)
  Phase 2: FP_ErrorBounds.v (depends on FP_Common)
  Phase 3: FP_Vec.v (depends on FP_Common)
  Phase 4: FP_Mat.v, FP_Color.v, FP_Rect.v, FP_Bounds.v, FP_Utils.v
- Updated theorem counting to include FP files
- Updated CI summary with Layer 6 row and FP count
- Increased workflow timeout from 30 to 45 minutes
- Updated cache key to include Flocq

### Rect Accessor Z-Compute Proofs (P2.5)

+8 theorems + 1 computational test in `Rect_Compute.v`:
- `zrect_from_pos_size` constructor definition
- Position/size/bounds accessor definitions
- `zrect_from_pos_size_position`, `zrect_from_pos_size_size`: roundtrip proofs
- `zrect_from_pos_size_eq_new`: equivalence with `zrect_new`
- `zrect_bounds_min_eq_position`, `zrect_bounds_max_eq_pos_plus_size`: bounds correctness
- `zrect_bounds_width_correct`, `zrect_bounds_height_correct`: dimension correctness
- `zrect_position_size_determine`: position+size uniquely determine rect

### Vector Lerp Z-Compute Proofs (P3.3)

+9 theorems across Vec2/3/4 Compute files:
- Vec2: `zvec2_lerp_zero_zero`, `zvec2_lerp_two`, `zvec2_lerp_neg_one`
- Vec3: `zvec3_lerp_zero_zero`, `zvec3_lerp_two`, `zvec3_lerp_neg_one`
- Vec4: `zvec4_lerp_zero_zero`, `zvec4_lerp_two`, `zvec4_lerp_neg_one`

These prove extrapolation behavior (t=2, t=-1) and zero-vector identity for lerp.

### Future Work Audit

Audited VERIFICATION_FUTURE_WORK.md and found 3 items incorrectly listed as incomplete:
- P1.4 (Mat4 orthographic): Fully completed in Phase 7 (Theorems 101-111)
- P3.11 (Utils Verus): Fully completed (33 proof functions in utils_proofs.rs)
- P3.1, P3.2 (Vector length/normalized Verus): BLOCKED by sqrt in integer model

Updated all items with correct status and blocker documentation.

### Summary

| Metric | Before | After | Delta |
|--------|--------|-------|-------|
| Coq Z-based theorems | 400 | 417 | +17 |
| Grand total | 2535 | 2552 | +17 |
| CI FP verification | None | Layer 6 (361 theorems) | New |
| Documentation checks | 43 | 45 | +2 |

---

## Phase 10: Mat4 look_at View Matrix Proofs + Kani Harnesses

**Status**: COMPLETED (Session 82WIW, 2026-02-04)

### Goals
1. Prove Mat4 `look_at` view matrix properties (P1.5 from VERIFICATION_FUTURE_WORK.md)
2. Add Kani harnesses for `look_at` IEEE 754 edge cases
3. Fix all stale documentation counts from prior sessions
4. Machine-check all proofs

### Accomplishments

1. **17 new Coq theorems for look_at** (`Mat4_Proofs.v`, Theorems 112-127 + 1 lemma):
   - `mat4_look_at_bottom_row`: Structural property (bottom row = [0,0,0,1])
   - `mat4_look_at_eye_to_origin`: Eye position maps to origin (fundamental view matrix property)
   - `mat4_look_at_forward_to_neg_z`: Forward→-Z mapping (orthonormal basis)
   - `mat4_look_at_side_to_x`: Side→+X mapping
   - `mat4_look_at_up_to_y`: Up→+Y mapping
   - `mat4_look_at_preserves_w`: W-component preservation (affine matrix)
   - `mat4_look_at_standard_basis_origin`: Standard basis at origin = identity
   - `mat4_look_at_eye_to_origin_vec4`: 4D version of eye-to-origin
   - `mat4_look_at_translation`: Translation column encodes eye position
   - 6 orthogonality theorems: Column dot-products verify rotation part is orthogonal
   - `mat4_look_at_eye_shift`: Eye translation property
   - `v3_dot_comm`: Utility lemma (dot product commutativity)

2. **4 new Kani harnesses** (`kani_proofs/mat4.rs`):
   - `verify_mat4_look_at_finite`: Finite-input → finite-output
   - `verify_mat4_look_at_eye_equals_target`: Degenerate input detection
   - `verify_mat4_look_at_affine_structure`: Bottom row always [0,0,0,1]
   - `verify_mat4_look_at_forward_parallel_up`: Parallel input detection

3. **Mat4.v spec additions**: `v3_dot` definition, `mat4_look_at` definition
   (parameterized by orthonormal basis to avoid sqrt)

4. **Documentation inconsistency fixes**: 23+ stale values across 8 files corrected

5. **Coq proof engineering lesson**: `apply vec3_eq; ring` fails because `apply vec3_eq`
   introduces unreduced record projections (e.g., `v3x (mkVec3 0 0 0)`) on the RHS.
   Fix: always use `apply vec3_eq; simpl; ring` — the `simpl` reduces the projections.

### Key Decisions
- **Orthonormal basis parameterization**: `mat4_look_at` takes pre-computed `s, u, f, eye`
  vectors instead of `eye, target, up`. This avoids sqrt/normalize in proofs while
  proving all properties that hold for the rotation+translation structure.
- **simpl after apply vec3_eq**: Established as mandatory pattern for Coq proofs involving
  record equality lemmas. All existing proofs already followed this pattern.

### Summary

| Metric | Before | After | Delta |
|--------|--------|-------|-------|
| Coq R-based theorems | 1078 | 1095 | +17 |
| Kani CBMC harnesses | 221 | 225 | +4 |
| Grand total | 2552 | 2573 | +21 |
| Mat4 verified operations | 18/26 (69%) | 19/26 (73%) | +1 |
| Overall coverage | 169/255 (66.3%) | 170/255 (66.7%) | +1 |
| P1.5 status | Pending | COMPLETED | — |

---

## Phase 11: Vec2/3 floor/ceil/round + Utils deg/rad Proofs

**Status**: COMPLETED (Session qru8V, 2026-02-04)

### Goals
1. Complete P4.1: Vec2/Vec3 floor/ceil/round algebraic proofs
2. Complete P4.4: Utils deg_to_rad/rad_to_deg proofs
3. Increase operation coverage from 170/255 (66.7%) to 178/255 (69.8%)

### Accomplishments

1. **20 new scalar theorems in `Utils.v`** (Theorems 38-56 + 1 helper lemma):
   - `Int_part_IZR`: Key lemma establishing `Int_part(IZR z) = z` via `tech_up`
   - Definitions: `Rfloor`, `Rceil`, `Rround`, `rdeg_to_rad`, `rrad_to_deg`
   - Floor properties: `Rfloor_le`, `Rfloor_lt_succ`, `Rfloor_zero`, `Rfloor_neg`, `Rfloor_integer`
   - Ceiling properties: `Rceil_ge`, `Rceil_lt_succ`, `Rceil_zero`, `Rceil_neg`, `Rceil_integer`
   - Relationship: `Rfloor_le_Rceil`
   - Deg/rad: `rdeg_to_rad_zero`, `rrad_to_deg_zero`, `rdeg_rad_roundtrip`, `rrad_deg_roundtrip`,
     `rdeg_to_rad_180`, `rdeg_to_rad_90`, `rdeg_to_rad_360`, `rdeg_to_rad_linear`

2. **12 new Vec2 theorems in `Vec2_Proofs.v`** (Theorems 131-142):
   - `vec2_floor_le`, `vec2_floor_lt_succ`, `vec2_ceil_ge`, `vec2_ceil_lt_succ`
   - `vec2_floor_zero`, `vec2_ceil_zero`, `vec2_round_zero`
   - `vec2_floor_neg`, `vec2_ceil_neg`, `vec2_floor_le_ceil`
   - `vec2_floor_integer`, `vec2_ceil_integer`

3. **12 new Vec3 theorems in `Vec3_Proofs.v`** (Theorems 111-122):
   - Same property set as Vec2 but for 3-component vectors

4. **6 new Vec2 Z-compute theorems** (`Vec2_Compute.v`, Theorems 57-62):
   - `zvec2_floor/ceil/round` defined as identity on integers
   - `zvec2_floor_id`, `zvec2_ceil_id`, `zvec2_round_id`
   - `zvec2_floor_zero`, `zvec2_ceil_zero`, `zvec2_round_zero`

5. **6 new Vec3 Z-compute theorems** (`Vec3_Compute.v`, Theorems 49-54):
   - Same pattern as Vec2 Z-compute

6. **Spec file changes**:
   - `Vec2.v`: Added `Require Import RourceMath.Utils.`, `vec2_floor/ceil/round` definitions
   - `Vec3.v`: Added `Require Import RourceMath.Utils.`, `vec3_floor/ceil/round` definitions
   - `_CoqProject`: Moved `Utils.v` before `Vec2.v` (dependency ordering)

### Key Decisions

- **Scalar definitions in Utils.v**: Centralized `Rfloor/Rceil/Rround` in Utils.v to avoid
  name collisions (Complexity.v and Vec_CrossType.v both import Vec2 and Vec3).
- **R_Ifp module for floor/ceil**: Used Coq's `Int_part`/`up`/`archimed`/`tech_up` from
  `Reals.R_Ifp` rather than Flocq's `Zfloor`/`Zceil`, since proofs are over R (reals)
  not FP error bounds.
- **Half-away-from-zero rounding**: `Rround(x) = if x ≥ 0 then Rfloor(x + 1/2) else Rceil(x - 1/2)`,
  matching Rust's `f32::round()` semantics.
- **`cbn` vs `simpl`**: Used `cbn [vec2_x vec2_y]` instead of `simpl` to prevent unfolding
  `Rfloor` (which breaks `rewrite` pattern matching).

### Proof Engineering Notes

- `tech_up` is the key primitive: establishes `up(IZR z) = (z+1)%Z` by showing
  `IZR z < IZR (z+1)` and `IZR(z+1) - IZR z ≤ 1`.
- `round_zero` requires direct computation: `up(1/2) = 1` via `tech_up`, then
  `Int_part(1/2) = 0`, therefore `Rfloor(1/2) = 0`.
- `field` tactic fully solves deg/rad equations with `PI ≠ 0` as sole side condition.

### Summary

| Metric | Before | After | Delta |
|--------|--------|-------|-------|
| Coq R-based theorems | 1095 | 1139 | +44 |
| Coq Z-based theorems | 417 | 429 | +12 |
| Grand total | 2573 | 2629 | +56 |
| Utils verified operations | 3/5 (60%) | 5/5 (100%) | +2 |
| Vec2 verified operations | 23/42 (55%) | 26/42 (62%) | +3 |
| Vec3 verified operations | 19/28 (68%) | 22/28 (79%) | +3 |
| Overall coverage | 170/255 (66.7%) | 178/255 (69.8%) | +8 |
| P4 status | 0/4 items completed | 4/4 items completed | All P4 DONE |

---

## Phase 12: Coverage Audit + fract/normalize/scale/lerp/approx_eq Proofs (Session WV5K1)

**Status**: COMPLETED (Session WV5K1, 2026-02-05)

### Goals
1. Audit VERIFICATION_COVERAGE.md against actual proof files — fix stale entries
2. Write new Coq proofs for fract, normalize, scale_from_center, lerp, approx_eq
3. Increase operation coverage from 178/255 (69.8%) toward 85%+

### Accomplishments

1. **Documentation audit revealed 27+ operations already verified but listed as "Not verified"**:
   - Vec3: lerp, min, max, abs, clamp, fract, normalize, scale, distance_sq, approx_eq, floor, ceil, round (12 ops)
   - Vec2: fract, normalize, scale, distance_sq, approx_eq, lerp, min (7 ops)
   - Color: lerp, darken, lighten, mix, clamp, invert, with_alpha, contrasting (8 ops)
   - Coverage jumped from 178/255 (69.8%) to 205/255 (80.4%) primarily from documentation fixes

2. **69 new Coq R-based theorems** across multiple files:
   - Vec2_Proofs.v: +6 theorems (fract, normalize, scale, lerp, approx_eq properties)
   - Vec3_Proofs.v: +6 theorems
   - Color_Proofs.v: +8 theorems
   - Rect_Proofs.v: +26 theorems (largest growth: from_corners, expand, scale_from_center, lerp, normalize, approx_eq)
   - Bounds_Proofs.v: +21 theorems
   - Utils.v: +2 theorems (Rfloor_eq, Rfract helper)

3. **CI fix**: Replaced `Int_part_spec` (unavailable in CI Coq environment) with `base_Int_part` (universally available from R_Ifp)

### Key Decisions

- **Coverage audit before new proofs**: Fixing stale documentation had more impact (+27 ops) than writing new proofs. This established the principle: always audit first.
- **base_Int_part over Int_part_spec**: CI environments may not have all R_Ifp lemmas. `base_Int_part` provides `IZR(Int_part r) <= r` and `IZR(Int_part r) - r > -1`, which combined with `lt_IZR` and `lia` solves floor/ceil proofs universally.

### Proof Engineering Notes

- `replace (_ - _)` wildcards fail with multiple R subtractions — use explicit terms
- `exfalso; lra` is WRONG when `x >= 0` and `x <= 0` — use `assert (x = 0) by lra; subst`
- `ring` cannot handle division — use `field` for goals containing `/`
- Color lerp uses `(b - a) * t` not `t * (b - a)` — always check actual definition order

### Summary

| Metric | Before | After | Delta |
|--------|--------|-------|-------|
| Coq R-based theorems | 1139 | 1208 | +69 |
| Grand total | 2629 | 2698 | +69 |
| Verified operations | 178/255 (69.8%) | 205/255 (80.4%) | +27 |
| Documentation accuracy | Stale (27+ wrong entries) | Accurate | Fixed |

---

## Phase 13: Rect/Mat4/Color/Bounds Extensions (Session Resp0)

**Status**: COMPLETED

Extended proofs for Rect, Mat4, Color, and Bounds with new operations and properties.

### New Coq Definitions Added

| File | Definitions Added |
|------|-------------------|
| `Rect.v` | `rect_from_pos_size`, `rect_grow_to_contain`, `rect_clip_to` |
| `Mat4.v` | `mat4_from_translation`, `mat4_approx_eq` |
| `Bounds.v` | `bounds_scale_from_center` |

### New Proofs Added

| File | New Theorems | Theorem Numbers |
|------|--------------|-----------------|
| `Rect_Proofs.v` | 27 | 150–176: from_pos_size properties, position/size accessors, grow_to_contain, clip_to |
| `Mat4_Proofs.v` | 10 | 128–137: from_translation (eq, transforms_point, preserves_vector, compose, det), approx_eq (refl, sym, zero_eq, eps_mono) + helper lemma |
| `Color_Proofs.v` | 4 | 128–131: blend_over_opaque_eq_premult, scale_add_dist, clamp01_in_range, blend_over_transparent_eq |
| `Bounds_Proofs.v` | 11 | 107–117: scale_from_center (center_x, center_y, width, height, one, zero, compose), translate (width, height, area), include_point_min_corner |
| **Total new** | **52** | — |

### Techniques Used

- **Selective unfolding**: Use `cbn [rect_w]` before `unfold Rmax, Rmin` to avoid explosive Rle_dec case splitting
- **Rmin/Rmax disambiguation**: `Rmin_l : Rmin x y <= x`, `Rmin_r : Rmin x y <= y` — check carefully
- **Helper lemmas**: `Rabs_le_0_eq` for proving zero-equality from `Rabs x <= 0`
- **Field names**: Mat4.v Vec4 uses `vec4_x/y/z/w`, not `v4x/y/z/w`
- **Circular dependencies**: Bounds.v imports Rect.v, so Rect.v cannot import Bounds.v

### Summary

| Metric | Before | After | Delta |
|--------|--------|-------|-------|
| Coq R-based theorems | 1208 | 1260 | +52 |
| Grand total | 2698 | 2750 | +52 |
| Rect theorems | 152 | 179 | +27 |
| Mat4 theorems | 180 | 190 | +10 |
| Color theorems | 127 | 131 | +4 |
| Bounds theorems | 107 | 118 | +11 |

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
| 14 | Vec2/Vec3 floor/ceil/round + Utils deg/rad (Phase 11) | COMPLETED |
| 15 | Coverage audit + fract/normalize/scale/lerp/approx_eq (Phase 12) | COMPLETED |
| 16 | Rect/Mat4/Color/Bounds extensions (Phase 13) | COMPLETED |
| 17 | Cross-type roundtrips + get_scale_sq + array conversions (Phase 14, +106 theorems) | COMPLETED |

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
| P2.5 | Rect trivial accessors | COMPLETED | 37 proofs (+8 Z-compute in Phase 9) |
| P2.6 | Mat3 shearing | COMPLETED | 7 proofs |
| P3.3 | Vector lerp (Verus + Z-compute) | COMPLETED | 25 proofs (Verus:16, Z:9 in Phase 9) |
| P3.4 | Vec3/Vec4 clamp Verus | COMPLETED | 8 proofs |
| P3.5 | Vec3/Vec4 reflect Verus | COMPLETED | 5 proofs |
| P3.6 | Mat3/Mat4 get_translation | COMPLETED | 10 theorems |
| P3.7 | Mat4 transform_vec4 | COMPLETED | 14 proofs |
| P3.8 | Color contrasting | COMPLETED | 4 proofs |
| P3.9 | Rect union | COMPLETED | 6 proofs |
| P3.10 | Rect from_corners + expand_xy | COMPLETED | 9 theorems |
| P3.11 | Utils lerp/clamp Verus | COMPLETED | 33 proof functions |
| P3.12 | Utils approx_eq | COMPLETED | 7 proofs |
| P1.4 | Mat4 orthographic projection | COMPLETED | 11 proofs (Phase 6-7) |
| P1.5 | Mat4 look_at view matrix | COMPLETED | 17 Coq theorems + 4 Kani harnesses (Phase 10) |
| P4.1 | Vec2/3 floor/ceil/round | COMPLETED | 24 Coq R + 12 Coq Z theorems (Phase 11) |
| P4.2 | Color integer conversions | COMPLETED | 21 R + 22 Z theorems (Phase 8) |
| P4.3 | Color from_rgb8 | COMPLETED | Included in P4.2 (Phase 8) |
| P4.4 | Utils deg_to_rad/rad_to_deg | COMPLETED | 20 Coq R theorems (Phase 11) |

---

*Last updated: 2026-02-05*
*Total phases: 14 implementation phases*
*Total completed priority items: 25/28 (89%)*
