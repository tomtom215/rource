# Verification Coverage Metrics

This document tracks formal verification coverage across the `rource-math` crate,
including per-module metrics, verification limitations, the floating-point
assessment, and the relationship between formal verification and testing.

For an overview of the complete verification effort (Verus + Coq), see
[FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md).

## Coverage Summary

| Module | Operations | Formally Verified | Unit Tested | Coverage |
|--------|------------|-------------------|-------------|----------|
| Vec2 | 42 | 33 (79%) | 42 (100%) | 79% |
| Vec3 | 28 | 28 (100%) | 28 (100%) | 100% |
| Vec4 | 24 | 23 (96%) | 24 (100%) | 96% |
| Mat3 | 19 | 18 (95%) | 19 (100%) | 95% |
| Mat4 | 26 | 22 (85%) | 26 (100%) | 85% |
| Color | 38 | 33 (87%) | 38 (100%) | 87% |
| Rect | 50 | 33 (66%) | 50 (100%) | 66% |
| Bounds | 24 | 24 (100%) | 24 (100%) | 100% |
| Utils (lib.rs) | 5 | 5 (100%) | 5 (100%) | 100% |
| **Total** | **256** | **219 (85.5%)** | **256 (100%)** | **85.5%** |

## Verified Operations by Module

### Vec2 (33 operations verified)
- `new`, `zero`, `add`, `sub`, `scale`, `neg`, `dot`, `cross`, `perp`, `length_squared`, `mul`
- `reflect`, `project`, `rejection`, `min_element`, `max_element`, `div`, `splat`, `element_sum`
- `min` (component-wise, commutativity, associativity, idempotency)
- `max` (component-wise, commutativity, associativity, idempotency)
- `abs` (non-negativity, idempotency, triangle inequality)
- `lerp` (boundary t=0, boundary t=1 via Coq proofs)
- `floor` (Coq: component-wise floor via Int_part, floor ≤ x < floor+1, zero, neg, integer identity)
- `ceil` (Coq: component-wise ceil via -floor(-x), x ≤ ceil < x+1, zero, neg, integer identity)
- `round` (Coq: half-away-from-zero rounding, zero preservation)
- `length` (Coq: non-negativity, zero ↔ zero vector)
- `normalized` (Coq: normalized length squared property)
- `fract` (Coq: range [0,1), zero, integer identity, floor+fract decomposition, idempotent)
- `clamp` (Coq: component-wise bounds verification)
- `distance` (Coq: non-negativity, self=0, symmetry)
- `distance_squared` (Coq: non-negativity, self=0, symmetry, translation invariance)
- `element_product` (Coq: splat, zero, scale properties)

**Not verified** (require floating-point or transcendentals):
- `from_angle`, `to_angle`, `rotate`
- `is_finite`, `is_nan`, `as_ivec2`, `as_uvec2`, batch operations

### Vec3 (28 operations verified — 100%)
- `new`, `zero`, `x`, `y`, `z`, `add`, `sub`, `scale`, `neg`, `dot`, `cross`, `length_squared`
- `reflect`, `project`, `rejection`, `min_element`, `max_element`, `div`, `splat`
- `floor` (Coq: component-wise floor via Int_part, floor ≤ x < floor+1, zero, neg, integer identity)
- `ceil` (Coq: component-wise ceil via -floor(-x), x ≤ ceil < x+1, zero, neg, integer identity)
- `round` (Coq: half-away-from-zero rounding, zero preservation)
- `length` (Coq: non-negativity, zero ↔ zero vector)
- `normalized` (Coq: normalized length squared property)
- `lerp` (Coq: boundary t=0/t=1, same vector identity, midpoint, component ranges)
- `min`, `max` (Coq: commutativity, idempotency, element bounds)
- `abs` (Coq: non-negativity, idempotency, neg invariance)
- `fract` (Coq: range [0,1), zero, integer identity, floor+fract decomposition)
- `clamp` (Coq: component-wise bounds verification)
- `distance` (Coq: non-negativity, self=0, symmetry)
- `distance_squared` (Coq: non-negativity, self=0, symmetry, translation invariance)
- `element_sum`, `element_product` (Coq: algebraic properties)

**All counted Vec3 operations verified.**

### Vec4 (23 operations verified — 96%)
- `new`, `zero`, `x`, `y`, `z`, `w`, `add`, `sub`, `scale`, `neg`, `dot`, `length_squared`, `mul`
- `min_element`, `max_element`, `div`, `splat`
- `length` (Coq: non-negativity, zero ↔ zero vector)
- `normalized` (Coq: normalized length squared property)
- `lerp` (Coq: boundary t=0/t=1, same vector identity, midpoint, component ranges)
- `min`, `max` (Coq: commutativity, idempotency, element bounds)
- `abs` (Coq: non-negativity, idempotency, neg invariance)
- `clamp` (Coq: component-wise bounds verification)
- `distance` (Coq: non-negativity, self=0, symmetry)
- `distance_squared` (Coq: non-negativity, self=0, symmetry, translation invariance)
- `element_sum`, `element_product` (Coq: algebraic properties)

**Not verified**: floating-point-specific operations (`is_finite`, `is_nan`)

### Mat3 (18 operations verified)
- `new`, `zero`, `identity`, `add`, `neg`, `scale`, `transpose`, `mul`
- `determinant`, `trace`, `translation`, `scaling`
- `get_translation`, `shearing`, `from_cols`, `inverse`
- `transform_point` (identity preservation, finite output, general decomposition proofs)
- `transform_vector` (identity preservation, finite output, general decomposition proofs)

**Not verified**: `rotation` (blocked: sin/cos transcendentals in Verus/Coq; Kani verifies NaN-freedom)

### Mat4 (22 operations verified)
- `zero`, `identity`, `add`, `neg`, `scale`, `transpose`, `mul`
- `determinant`, `trace`, `from_cols`, `inverse`
- `col` (col0-3), `row` (row0-3), `orthographic`, `get_translation`
- `transform_point` (identity, translation, scaling proofs), `transform_vector` (identity, scaling proofs), `transform_vec4` (identity, zero, additive, scalar, translation, scaling, mul_compat)
- `look_at` (17 Coq theorems: eye-to-origin, basis mapping, orthogonality, w-preservation, translation encoding; 4 Kani harnesses)
- `from_translation` (Coq: equivalence to mat4_translation, transforms point correctly, preserves vectors, composition is additive, determinant = 1)
- `approx_eq` (Coq: reflexive, symmetric, zero implies equality, epsilon monotonicity)
- `get_scale` (modeled as get_scale_sq to avoid sqrt; 18 Coq theorems: identity/scaling/translation, non-negativity, uniform, zero, sign-invariance, composition, transpose, dot-product, scalar multiply)

**Not verified**: `perspective` (blocked: tanf), `rotation_*` (blocked: sin/cos)

### Color (33 operations verified)
- `new`, `rgb`, `gray`, `with_alpha`, `fade`, `lerp`, `premultiplied`, `blend_over`, `luminance`, `clamp`, `transparent`, `black`, `white`, `clamp_component`
- `add`, `scale`, `invert`
- `mix` (commutativity, self-mixing, lerp equivalence), `darken` (identity, full, alpha preservation, composition), `lighten` (identity, full, alpha preservation, composition), `contrasting` (black→white, white→black, binary output, always opaque)
- `from_u8` (range, black, white), `from_rgb8` (opaque, equivalence), `from_hex` (opaque, alpha consistency), `from_hex_alpha`, `u8_to_f32` (zero, max, nonneg, le_one, range, monotone, injective), `f32_to_u8` (zero, one, range, roundtrip boundaries)
- `approx_eq` (Coq: reflexive, symmetric, zero implies equality, epsilon monotonicity, lerp compatibility)
- `to_rgba`/`to_rgb` (Coq: component extraction, roundtrip, interaction with scale/add/invert/fade/with_alpha)
- `from_rgba`/`from_rgb_tuple` (Coq: roundtrip, alpha default, component extraction)
- `is_light`/`is_dark` (Coq: complement, exclusivity, black is dark, gray boundary)
- `contrast` (Coq: symmetry, self=0, non-negative, black-white=1, triangle inequality)

**Not verified** (require floating-point or HSL conversions):
- `from_hsl`, `to_hsl`, `saturate`, `desaturate`
- Floating-point-specific: `is_finite`, `is_nan`

### Rect (33 operations verified)
- `new`, `zero`, `right`, `bottom`, `center_x`, `center_y`, `area`, `perimeter`
- `contains_point`, `contains_rect`, `intersects`, `union`, `translate`, `expand`, `shrink`, `is_valid`
- `intersection` (commutativity, self-intersection, area properties)
- `scale` (composition property)
- `left`, `top`, `is_empty`, `from_corners`, `expand_xy`
- `from_center` (Coq: center preservation, dimensions, area)
- `from_pos_size` (Coq: equivalence to rect_new, accessor preservation, area formula)
- `normalize` (Coq: non-negative dims, preserves right/bottom, positive identity)
- `scale_from_center` (Coq: preserves center, correct dims, identity at factor=1, area formula)
- `lerp` (Coq: boundary t=0/t=1, same rect identity, width/height formulas)
- `approx_eq` (Coq: reflexive, symmetric, zero implies equality, epsilon monotonicity)
- `to_bounds` (Coq: min/max extraction, roundtrip with bounds_to_rect, width/height/area/center preservation, validity, translation commutes)
- `merge` (Coq: alias for union, commutativity)
- `clip_to` (Coq: alias for intersection)
- `grow_to_contain` (Coq: containment guarantee, idempotency on interior point)
- `size`/`position` (Coq: accessor equivalence proofs)

**Not verified** (require floating-point or complex geometry):
- `from_points`, iterator-based operations
- Complex geometry: `transform_by_mat3`, `transform_by_mat4`

### Bounds (24 operations verified — 100%)
- `new`, `from_points`, `from_center_half_extents`, `from_center_size`
- `width`, `height`, `size`, `center`, `half_extents`, `area`
- `contains`, `contains_bounds`, `intersects`, `intersection`, `union`
- `include_point`, `expand`, `shrink`, `translate`
- `is_valid`, `is_empty`
- `to_rect` (Coq: x/y/w/h extraction, area preservation, right/bottom edges, center preservation, valid rect)
- `from_rect` (Coq: min/max extraction, roundtrip with to_rect, width/height/area/center preservation, validity, zero, translation/expand commute, containment equivalence)
- `approx_eq` (Coq: reflexive, symmetric, zero implies equality, epsilon monotonicity)
- Additional Coq-only: `scale_from_center` (7 theorems: preserves center, scales dims, identity/zero/compose)

**All Bounds operations verified.**

### Utils (5 operations verified — 100%)
- `lerp` (18+ theorems: boundary values, affine form, symmetry, monotonicity, composition, injectivity)
- `clamp` (12+ theorems: range, identity, lower/upper bounds, idempotent, monotone, center distance)
- `approx_eq` (7+ theorems: reflexivity, symmetry, triangle inequality, non-transitivity counterexample, translation/negation invariance, epsilon monotonicity)
- `deg_to_rad` (Coq: zero, 90°=π/2, 180°=π, 360°=2π, linearity, deg→rad→deg roundtrip)
- `rad_to_deg` (Coq: zero, rad→deg→rad roundtrip)

**All Utils operations verified.**

## Verification Limitations

Operations that **cannot be formally verified** with current Verus capabilities:

| Category | Reason | Examples |
|----------|--------|----------|
| Floating-point | Verus uses integer specs | `length()`, `normalized()`, `sin/cos` |
| Transcendentals | No SMT support | `from_angle()`, `to_angle()`, `rotate()` |
| Type conversions | Platform-specific | `as_ivec2()`, `as_uvec2()` |
| NaN handling | IEEE 754 semantics | `is_nan()`, `is_finite()` |

## Prioritized Verification Roadmap

| Priority | Module | Operations | Rationale | Status |
|----------|--------|------------|-----------|--------|
| ~~1~~ | ~~Color~~ | ~~Constructor, alpha, blend, lerp, luminance~~ | ~~Color correctness critical for visualization~~ | DONE (Verus: 57, Coq R: 121, Coq Z: 60) |
| ~~2~~ | ~~Rect~~ | ~~`contains`, `intersects`, `union`, transforms~~ | ~~Spatial logic used in collision detection~~ | DONE (Verus: 52, Coq R: 126, Coq Z: 43) |
| ~~3~~ | ~~Utils (lib.rs)~~ | ~~`lerp`, `clamp`, `deg_to_rad`, `rad_to_deg`, `approx_eq`~~ | ~~Foundational operations~~ | DONE (Coq R: 57, Coq Z: 18) — 100% coverage |
| 4 | Mat3/Mat4 | `determinant`, `trace` properties | Mathematical foundations | DONE (basic: det(I), det(0), det(A^T), det(-A), trace properties) |
| 5 | Color | HSL <-> RGB conversion | Requires transcendentals | Blocked (floating-point) |

## Relationship to Testing

Formal verification and testing serve complementary purposes:

| Aspect | Testing | Formal Verification |
|--------|---------|---------------------|
| Coverage | Sample-based | Exhaustive |
| Confidence | Statistical | Mathematical certainty |
| Floating-point | Direct testing | Models exact arithmetic |
| Effort | Lower | Higher |
| Maintenance | Test code | Proof maintenance |

The project maintains both:
- **100% test coverage** for `rource-math` via tarpaulin (runtime behavior)
- **Formal proofs** for core properties (mathematical correctness)

## Floating-Point Refinement Investigation

### Investigation Summary (2026-01-28)

We investigated Verus's current floating-point support to assess feasibility of verifying
operations like `length()`, `normalized()`, and `lerp()`.

### Current Verus Floating-Point Support

| Component | Support Level | Description |
|-----------|---------------|-------------|
| `vstd::float` module | Basic | Properties of floating point values |
| `FloatBitsProperties` trait | Available | Bit-level extraction for f32/f64 |
| Arithmetic verification | Limited | Not well-supported per recent research |
| Transcendental functions | None | sin/cos/sqrt not verifiable |

### Technical Challenges

1. **Rounding semantics**: IEEE 754 rounding modes create non-determinism that SMT solvers struggle with
2. **Exception handling**: NaN propagation, infinities, and denormals complicate proofs
3. **No algebraic structure**: Floating-point arithmetic is not associative or distributive
4. **Formula explosion**: Verification formulas become very large and slow

### Research References

- Yang, C., et al. "AutoVerus: Automated Proof Generation for Rust Code." arXiv:2409.13082, 2024.
  - Notes floating-point as "not well supported by Rust/Verus"
- Friedlos, L. "Verifying Rust Programs Using Floating-Point Numbers and Bitwise Operations." ETH Zurich thesis.
  - States "guarantees for programs using floating-points are generally rather low"

### Recommendation

For rource-math, we recommend:

1. **Integer specifications remain primary**: Continue using `int` specs for algebraic properties
2. **Bit-level properties only**: Use `FloatBitsProperties` for verifying representation invariants
3. **Refinement types**: Document the integer->f32 translation assumptions explicitly
4. **Monitor Verus development**: Check quarterly for improved floating-point support
5. **Coq + Flocq + VCFloat2 for FP accuracy**: See [FLOATING_POINT_VERIFICATION.md](FLOATING_POINT_VERIFICATION.md) for the recommended path to verifying floating-point operations via Coq's mature FP ecosystem (all Coq 8.18 compatible)

### What CAN Be Verified with Floating-Point

| Property | Verifiable | Notes |
|----------|------------|-------|
| Bit layout (sign, exponent, mantissa) | Yes | Via `FloatBitsProperties` |
| is_nan, is_infinite predicates | Yes | Bit patterns |
| Comparison with NaN handling | Partial | Requires careful specification |
| Basic arithmetic correctness | No | Rounding non-determinism |
| Transcendental accuracy | No | No SMT theory support |

### Conclusion

**Floating-point formal verification in Verus is not mature enough for production use.**
Our current approach of proving properties over `int` specifications and documenting
the f32 translation assumptions is the recommended best practice per Verus maintainers.

The 30.2% of operations not formally verified (those requiring floating-point or
transcendentals) will remain covered by:
- Unit tests (100% coverage)
- Property-based testing
- Manual review for IEEE 754 compliance

### Stainless Paper Investigation (2026-01-30)

We investigated "Verifying Floating-Point Programs in Stainless" (Gilot et al.,
arXiv:2601.14059, January 2026) which extends the Stainless verifier with IEEE 754
floating-point support using Z3 + cvc5 + Bitwuzla portfolio solving.

**Key findings**: The paper is **not directly applicable** to rource-math because:
(1) it is Scala-only, (2) Z3 is the weakest solver for FP queries (78–85% vs cvc5's
89–100%), (3) it does not verify error bounds (only NaN/safety), (4) it cannot prove
algebraic properties over floating-point, and (5) it produces no Coq proof certificates.

The paper's value for our project is as a landscape survey confirming that **Coq + Flocq +
VCFloat2** is the more appropriate path for rource-math's needs. See
[FLOATING_POINT_VERIFICATION.md](FLOATING_POINT_VERIFICATION.md) for the full analysis
and recommended roadmap to reach ~70–75% coverage.

## rocq-of-rust Investigation (2026-01-30)

### Investigation Summary

We investigated [rocq-of-rust](https://github.com/formal-land/rocq-of-rust) (formerly
coq-of-rust) as a potential tool to close the specification-to-implementation gap by
machine-translating Rust source code to Rocq (Coq) for verification.

### Tool Profile

| Property | Value |
|----------|-------|
| Repository | github.com/formal-land/rocq-of-rust |
| Commits | 3,005+ |
| Stars | 1.1k+ |
| Rust toolchain | nightly-2024-12-07 (Rust ~1.85) |
| Rocq version | 9.0.x (rocq-core >= 9.0 & < 9.1) |
| Translation level | THIR (Typed High-Level IR) |
| Embedding style | Shallow (monadic) |

### Test Results

We successfully built the translator binary and ran it on a minimal Vec2 subset
(10 functions: new, zero, splat, add, sub, scale, neg, dot, cross, length_squared
plus Add/Sub/Neg operator traits).

| Step | Result |
|------|--------|
| Build translator binary | Success (nightly-2024-12-07 + rustc-dev) |
| rource-math compiles with nightly-2024-12-07 | Yes (no 1.93-specific features) |
| Translation of Vec2 subset | Success (619-line Rocq file in 91ms) |
| Output compilation in Rocq 9.0 | **BLOCKED** (opam repos return HTTP 503) |
| Bridge to existing Coq 8.18 proofs | **NOT FEASIBLE** (see below) |

### Critical Blockers

**1. Fundamentally different representation**

Our Coq proofs use clean algebraic specifications:
```coq
Record Vec2 := { vx: R; vy: R }.
Definition vec2_add a b := mk_vec2 (vx a + vx b) (vy a + vy b).
```

rocq-of-rust generates a monadic shallow embedding modeling Rust's memory model:
```coq
Definition add (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  ltac:(M.monadic
    (let self := M.alloc (| Ty.path "lib::Vec2", self |) in
     Value.mkStructRecord "lib::Vec2" [] []
       [("x", M.call_closure (| Ty.path "f32", BinOp.Wrap.add, [...] |)); ...]))
```

Bridging these representations would require writing refinement proofs showing the
monadic operations reduce to algebraic operations — requiring deep expertise in
rocq-of-rust's monad semantics and enormous proof engineering effort.

**2. f32 literals are `UnsupportedLiteral`**

All floating-point constants (0.0, 1.0, etc.) translate to opaque `UnsupportedLiteral`
placeholders. The tool cannot represent f32 values, making mathematical property
verification impossible at the generated level.

**3. Structural `Admitted` axioms**

Every function association binding uses `Admitted`:
```coq
Global Instance AssociatedFunction_new : M.IsAssociatedFunction.C Self "new" new.
Admitted.
```
While these are structural (not mathematical) axioms about Rust's type system,
they mean the generated code is NOT zero-admits — violating our PEER REVIEWED
PUBLISHED ACADEMIC standard.

**4. Dependency infrastructure unavailable**

The generated code requires `RocqOfRust.RocqOfRust` which depends on:
- `coq-coqutil` (MIT bedrock2), `coq-hammer`, `rocq-smpl`
- All require Coq/Rocq opam repos (coq.inria.fr, rocq-prover.org) which return HTTP 503

**5. Version mismatch: Rocq 9.0 vs Coq 8.18**

Our 2156 existing Coq theorems use Coq 8.18. The generated code targets Rocq 9.0.
Bridging requires migrating one or both sides.

### Comparison: rocq-of-rust vs Our Approach

| Criterion | rocq-of-rust | Our Manual Specs |
|-----------|-------------|-----------------|
| Spec-to-impl correspondence | Machine-generated | Manual (trusted) |
| Representation | Monadic (memory model) | Algebraic (mathematical) |
| f32 support | `UnsupportedLiteral` | Modeled as R (reals) or Z (integers) |
| Admits | Structural `Admitted` axioms | Zero admits |
| Proof style | Systems-level | Mathematical properties |
| Compilability | Blocked (infra) | All 2156 Coq theorems compile |
| Best suited for | Smart contracts, protocols | Pure math functions |

### Recommendation

**rocq-of-rust is NOT viable for rource-math** due to:
1. The monadic representation is unsuitable for algebraic property verification
2. f32 literals are unsupported
3. The dependency infrastructure is unavailable
4. The bridging effort would be enormous with uncertain feasibility

**Our current approach remains optimal**: clean algebraic specifications in Coq 8.18
with manual correspondence to Rust implementations, verified by 2156 machine-checked
Coq theorems (1366 R-based + 429 Z-based + 361 FP) with zero admits. The spec-to-implementation gap is documented as a known
limitation and mitigated by:
- Systematic specification writing following Rust implementation structure
- 100% unit test coverage verifying runtime behavior
- Dual verification (Verus + Coq) providing cross-validation
- Code review of specification correspondence

**Future monitoring**: Re-evaluate when:
- rocq-of-rust adds f32 literal support
- Coq/Rocq opam infrastructure stabilizes
- A "mathematical extraction" mode is added (bypassing the monadic embedding)
- Rocq 9.x migration is undertaken for our proof base

## Rust Verification Landscape Survey (2026-01-30)

We investigated four additional Rust formal verification tools to assess whether they
address any capability gaps in our current Verus + Coq architecture. See
[RUST_VERIFICATION_LANDSCAPE.md](RUST_VERIFICATION_LANDSCAPE.md) for the full assessment.

### Tools Investigated

| Tool | Category | FP Support | Recommendation |
|------|----------|------------|----------------|
| **Kani** (Amazon) | Bounded model checker (CBMC) | YES (bit-precise) | **ADOPT** for edge-case safety |
| **Aeneas** (Inria) | MIR → pure functional translation | Unknown | **MONITOR** for spec-to-impl bridge |
| **Creusot** (Inria) | MIR → Why3 → SMT portfolio | Via Why3 ieee_float | **MONITOR** for FP via Why3 |
| **hax** (Cryspen) | THIR → F*/Rocq/Lean | No (backends lack FP) | NOT APPLICABLE (crypto-focused) |

### Key Findings

1. **Kani** is the only tool that directly verifies floating-point edge cases
   (NaN, overflow, infinity) at the bit level. It complements our algebraic proofs
   (Verus/Coq) with runtime safety guarantees for f32 operations.

2. **Aeneas** produces **pure functional** code (unlike rocq-of-rust's monadic
   embedding), making it the most promising tool for closing the spec-to-impl gap.
   However, f32 support is unconfirmed.

3. **Creusot** overlaps with Verus for algebraic proofs but offers portfolio SMT
   solving (CVC5 outperforms Z3 on FP queries) and potential Coq proof export.
   FP support via Why3's `ieee_float` theory is undocumented.

4. **hax** explicitly states "most backends do not have any support for floats"
   (VSTTE 2024 paper). Not applicable to graphics math verification.

### Updated Verification Architecture

```
Current (3-layer):  Verus (algebra) + Coq (proofs) + Kani (IEEE 754)  → 2856 theorems, 59.3% ops
Target (4-layer):   + Flocq (FP accuracy bounds)                      → ~1100+ theorems, ~75% ops
Future (5-layer):   + Aeneas (spec-to-impl bridge)                    → machine-generated specs
```

### Kani Integration (2026-01-30)

Kani (Amazon's CBMC-based bounded model checker) was adopted as the third
verification layer, providing bit-precise IEEE 754 edge-case verification
that neither Verus nor Coq can directly offer.

**Kani Harness Summary:**

| Module | Harnesses | Properties Verified |
|--------|-----------|---------------------|
| Utils | 11 | lerp NaN-freedom, clamp bounded, approx_eq reflexive, deg/rad finite, lerp endpoint zero, approx_eq symmetry, lerp endpoint one, clamp idempotent, lerp no-NaN, approx_eq finite, clamp range |
| Vec2 | 28 | length ≥ 0, length_sq ≥ 0, normalized no-NaN, dot finite, cross finite, project zero-guard + no-NaN, distance ≥ 0, rotate no-NaN, from_angle no-NaN, lerp no-NaN, distance_sq ≥ 0, abs ≥ 0, floor/ceil/round finite, min/max componentwise, clamp bounded, perp finite, approx_eq reflexive, add commutative, neg involutive, sub anti-commutative, scale distributive, element_sum finite, mul componentwise, div finite |
| Vec3 | 29 | length ≥ 0, normalized no-NaN, dot finite, cross finite, project zero-guard + no-NaN, distance ≥ 0, distance_sq ≥ 0, lerp no-NaN, abs ≥ 0, floor/ceil/round finite, min/max componentwise, clamp bounded, reflect finite, approx_eq reflexive, add commutative, neg involutive, sub anti-commutative, scale distributive, element_sum finite, mul componentwise, div finite, min/max element finite, splat components, element_product finite, rejection finite |
| Vec4 | 25 | length ≥ 0, normalized no-NaN, dot finite, lerp no-NaN, abs ≥ 0, min/max componentwise, clamp bounded, approx_eq reflexive, add commutative, neg involutive, sub anti-commutative, scale distributive, length_sq non-negative, dot self non-negative, zero length, splat components, mul componentwise, div finite, min_element finite, max_element finite, element_sum finite, mul commutative, sub anti-commutative algebraic, element_product finite |
| Mat3 | 23 | determinant finite, inverse(zero)=None, inverse(I)=Some, transform_point finite, rotation no-NaN, identity preserves point, transpose involutive, translation/scaling/shearing finite, transform_vector finite, get_translation roundtrip, get_scale finite, approx_eq reflexive, mul identity right/left, uniform_scaling finite/structure, from_translation finite, default is identity, from_cols correct, det_neg no-NaN, trace finite |
| Mat4 | 32 | determinant finite, inverse(zero)=None, inverse(I)=Some, orthographic finite, identity det=1, zero det=0, transpose involutive, translation/scaling finite, rotation_x/y/z no-NaN, transform_point finite, identity preserves point, approx_eq reflexive, transform_vector finite, identity preserves vector, get_translation roundtrip, uniform_scaling structure, from_translation equiv, translation det=1, col/row correct, from_cols correct, translation_transforms_point, translation_preserves_vector, mul_identity left/right, look_at finite, look_at eye=target fallback, look_at affine structure, look_at forward parallel up |
| Color | 25 | to_rgba8 normalized, luminance range, blend_over no-NaN, from_hex normalized, lerp no-NaN, clamp bounded, premultiplied no-NaN, fade no-NaN, with_alpha preserves RGB, to_argb8/abgr8 normalized, from_hex_alpha/rgba8 normalized, contrasting valid, approx_eq reflexive, scale finite, invert finite, mix no-NaN, add clamped, darken/lighten finite, from_rgba8 to_rgba8 roundtrip, from_hex to_rgba8 consistent, array roundtrip, gray finite |
| Rect | 27 | area ≥ 0, center finite, contains origin, perimeter ≥ 0, from_center_size center, translate preserves size, expand finite, is_valid positive dims, self-intersection, contains_self, scale_from_center finite/componentwise, approx_eq reflexive, from_corners valid, grow_to_contain finite, normalize finite, lerp finite, expand_xy finite, shrink finite, right/bottom correct, to_bounds finite, intersection finite, union finite |
| Bounds | 25 | area ≥ 0, width/height ≥ 0, center finite, size finite, contains min, contains_bounds self, intersects self, translate preserves size, expand/shrink finite, from_points valid, from_center_half_extents finite, is_valid/is_empty complementarity, include_point contains, union contains both, approx_eq reflexive, to_rect finite, from_center_size finite, half_extents finite, union commutative, intersection finite, new finite |
| **Total** | **225** | **All verified, 0 failures** |

**Known limitation**: `Mat4::perspective()` uses `f32::tan()` which delegates to C `tanf` —
unsupported by Kani's CBMC backend (tracked: github.com/model-checking/kani/issues/2423).

**IEEE 754 edge cases discovered during Kani development:**
1. `lerp(f32::MAX, -f32::MAX, 0.0)` → NaN: intermediate `(b-a)` overflows to `-inf`, then `-inf * 0.0 = NaN`
2. `Vec2::project()` with denormalized onto vector → NaN: `length_squared > 0.0` passes but `dot / length_squared` overflows to `±inf`, then `inf * 0.0 = NaN`
3. `Rect::intersects(self)` fails when `width < ULP(x)`: the strict inequality `x + width > x` is false in IEEE 754 when width is smaller than the unit of least precision at x. At `|x| = 1e6`, `ULP ≈ 0.12`, so `width > 1.0` is required for the self-intersection property to hold.
4. `Rect::from_center_size()` center roundoff: `cx - w/2 + w/2 ≠ cx` due to catastrophic cancellation when `|cx| >> w`. At `|cx| < 1e6`, roundoff bounded by `2e6 * 1.2e-7 ≈ 0.24`.

All edge cases are IEEE 754-compliant behavior requiring bounded input domains for guaranteed safety.

---

*Last verified: 2026-02-05*
*Formal verification coverage: 219/256 operations (85.5%)*
*Kani IEEE 754 harnesses: 225 (all verified, 0 failures)*
*Unit test coverage: 256/256 operations (100%)*
*Unverifiable operations: ~77 (floating-point, transcendentals, type conversions)*
*Landscape survey: 8 tools investigated (6 new + 2 current), Kani adopted*
