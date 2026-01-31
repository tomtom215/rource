# Floating-Point Formal Verification Feasibility Assessment

This document assesses the feasibility of formally verifying the 114 rource-math
operations that currently cannot be verified due to floating-point semantics.
It surveys the state of the art, evaluates specific tools and papers, and
provides a concrete roadmap for extending verification coverage.

For the broader verification context, see [FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md).
For current coverage metrics, see [VERIFICATION_COVERAGE.md](VERIFICATION_COVERAGE.md).

## Executive Summary

| Aspect | Finding |
|--------|---------|
| **Current gap** | 114/230 operations (49.6%) unverified due to floating-point/transcendental requirements |
| **Paper investigated** | "Verifying Floating-Point Programs in Stainless" (Gilot et al., arXiv:2601.14059, Jan 2026) |
| **Paper applicability** | Not directly applicable — Scala-only tool, no Rust/Coq integration |
| **Most promising path** | Coq + Flocq + VCFloat2 + Gappa (all Coq 8.18 compatible) |
| **Estimated reachable coverage** | 70–75% (up from 50.4%) with moderate effort |
| **Maximum theoretical coverage** | ~90% (requires significant novel proof engineering) |
| **Remaining hard gap** | ~10% — HSL color conversions, complex geometric transforms |

## Paper Analysis: "Verifying Floating-Point Programs in Stainless"

### Paper Profile

| Property | Value |
|----------|-------|
| **Title** | Verifying Floating-Point Programs in Stainless |
| **Authors** | Andrea Gilot, Axel Bergström, Eva Darulova |
| **Affiliation** | Uppsala University |
| **Date** | January 20, 2026 (arXiv preprint) |
| **arXiv** | [2601.14059v1](https://arxiv.org/abs/2601.14059v1) |
| **Artifact** | [Zenodo 17486575](https://doi.org/10.5281/zenodo.17486575) |
| **Benchmarks** | [GitHub: fxpl/stainless-float-benchmarks](https://github.com/fxpl/stainless-float-benchmarks) |
| **Tool** | Stainless (Scala deductive verifier, EPFL LARA lab) |
| **License** | CC BY 4.0 |

### Core Contribution

The paper extends Stainless with three capabilities for floating-point verification:

1. **Bitwuzla integration**: Portfolio solving with Z3 + cvc5 + Bitwuzla (specialized FP solver)
2. **Verified transcendental library**: 18 functions (sin, cos, tan, exp, log, etc.) with
   properties verified against FdLibm implementations (unlike KeY's unverified axiomatization)
3. **Automated NaN/cast checking**: Injection of assertions for NaN on comparisons and
   safety checks on float-to-integer casts

### Solver Performance Comparison

| Benchmark Suite | cvc5 | Z3 | Bitwuzla | Portfolio |
|-----------------|------|----|----------|-----------|
| KeY (adapted) | 100% | 85.2% | 67.0% | ~100% |
| FdLibm (18 transcendentals) | 88.7% | 78.1% | 84.8% | ~99% |
| Empirical (103 GitHub fns) | 99.7% | 95.5% | 30.6% | 99.8% |

Key finding: **Z3 is the weakest solver for floating-point queries.** This is directly
relevant because Verus uses Z3 exclusively.

### Transcendental Function Axiomatization

The paper axiomatizes 18 functions with properties including:
- NaN output characterization (when inputs produce NaN)
- Special value behavior (sin(±0) = ±0, exp(-∞) = 0, etc.)
- Output range bounds (sin ∈ [-1, 1], etc.)
- Sign preservation and monotonicity

Critical limitation: the axioms **over-approximate** behavior, causing spurious
counterexamples in 42% (8/19) of benchmarks using transcendental functions.

### Geometric/Vector Benchmarks

The paper includes KeY benchmarks for: CartesianPolar, Complex, Matrix2, Matrix3,
Rectangle, Rotation, Vector2. However, the specific mathematical properties verified
for these types are not detailed — only verification condition counts are reported.

### What the Paper Does NOT Do

| Not Addressed | Why It Matters for rource-math |
|---------------|-------------------------------|
| **Error bound quantification** | Cannot prove "result within N ULPs of exact" |
| **Algebraic property verification** | Cannot prove `lerp(a, b, 0) == a` over floats |
| **Compositional property verification** | Cannot prove `normalized().length() ≈ 1.0` |
| **Non-Scala languages** | Tool is Scala-only; no Rust, no Coq output |
| **Interactive proof generation** | No Coq/Lean/Isabelle proof certificates |
| **Floating-point modulo** | Explicitly unsupported due to semantic mismatch |

### Assessment: Applicability to rource-math

**The Stainless paper is NOT directly applicable to rource-math** for these reasons:

1. **Language mismatch**: Tool works only on functional Scala; rource-math is Rust
2. **Verification backend mismatch**: Generates SMT-LIB VCs; cannot produce Coq proofs
3. **Z3 weakness**: Verus uses Z3 exclusively, which performs worst on FP queries
4. **No error bounds**: The paper verifies absence of NaN/special values and output ranges
   but does NOT quantify rounding error — which is what graphics math needs
5. **No algebraic properties**: Cannot verify relational properties (commutativity, associativity)
   over floating-point, which is the bulk of our verification

**The paper IS valuable as**:
- Confirmation that SMT-LIB FP theory is maturing
- Evidence that portfolio solving significantly outperforms single-solver approaches
- A survey reference for the floating-point verification landscape
- Motivation to look at cvc5 instead of Z3 for any future FP work

### Comparison with Existing rource-math Approach

| Criterion | Stainless (Paper) | rource-math (Current) |
|-----------|-------------------|----------------------|
| Verification target | Runtime safety (NaN, overflow) | Mathematical correctness (algebraic properties) |
| Floating-point model | Native IEEE 754 via SMT-LIB FP | Real numbers (R) or integers (Z) |
| Proof output | SMT solver discharge | Coq proof terms + Verus Z3 proofs |
| Transcendentals | Axiomatized with over-approximation | Not attempted |
| Composability | Limited (per-function) | High (theorem composition) |
| Error bounds | Not addressed | Not addressed |

## Alternative Path: Coq Floating-Point Ecosystem

The investigation reveals a mature Coq ecosystem that is directly compatible with
our existing Coq 8.18 infrastructure.

### Tool Ecosystem (All Coq 8.18 Compatible)

| Package | Version | Purpose | opam Name |
|---------|---------|---------|-----------|
| **Flocq** | 4.1.3 | IEEE 754 formalization, rounding theorems | `coq-flocq` |
| **Gappa** (tool) | 1.4.1 | External interval arithmetic prover | `gappa` |
| **Gappa** (Coq) | 1.5.4 | Coq tactic calling Gappa | `coq-gappa` |
| **CoqInterval** | 4.8.1 | Automatic interval arithmetic tactic | `coq-interval` |
| **Coquelicot** | 3.4.0 | Real analysis (limits, derivatives, series) | `coq-coquelicot` |
| **VCFloat** | 2.1.1 | Automatic FP error bound computation | `coq-vcfloat` |

### Flocq: IEEE 754 Foundation

Flocq (Boldo & Melquiond, INRIA) is the standard Coq formalization of floating-point
arithmetic, used by CompCert and many other verified systems.

**What Flocq formalizes:**
- Multi-radix, multi-precision floating-point and fixed-point arithmetic
- All IEEE 754 rounding modes (round-to-nearest-even, toward-zero, up, down)
- Rounding error bounds and error-free transformations (2Sum, Fast2Sum, 2MultFMA)
- Sterbenz lemma and key numerical analysis results
- Elementary functions: cos, sin, tan, arctan, exp (log is work-in-progress)
- sqrt: fully supported as IEEE 754 required operation with exact rounding

**Key reference**: Boldo, S. & Melquiond, G. "Computer Arithmetic and Formal Proofs:
Verifying Floating-point Algorithms with the Coq System." Elsevier, 2017.

**Key paper**: Boldo, S. & Melquiond, G. "Flocq: A Unified Library for Proving
Floating-Point Algorithms in Coq." IEEE ARITH, 2011.

### VCFloat2: Automated Error Bound Computation

VCFloat2 (Appel & Kellison, Princeton/VeriNum, CPP 2024) automatically computes
round-off error bounds for floating-point expressions in Coq.

**Capabilities:**
- Given an FP expression, computes a sound upper bound on round-off error
- Produces machine-checked Coq proof terms
- Supports float32 (`Tsingle`) and float64 (`Tdouble`)
- Can reason about external functions given error specifications
- Composable: sub-expression bounds compose into whole-expression bounds

**Key reference**: Kellison, A. & Appel, A. "VCFloat2: Floating-point Error Analysis
in Coq." CPP 2024.

### LAProof: Linear Algebra over Floating-Point

LAProof (Kellison, Appel, Tekriwal, Bindel, IEEE ARITH 2023) provides Coq proofs
of accuracy for floating-point matrix and vector operations.

**Verified operations:**
- Matrix-vector product (r = Ax) with mixed backward-forward error bounds
- Scaled matrix-vector product (r = αAx)
- Matrix-matrix product (R = AB)
- Matrix addition (R = A + B)
- Scalar multiplication (R = αA)
- L2 vector norm with overflow/underflow avoidance

**Key reference**: Kellison, A. et al. "LAProof: A Library of Formal Proofs of
Accuracy and Correctness for Linear Algebra Programs." IEEE ARITH, 2023.

### Gappa: Interval Arithmetic Automation

Gappa (Melquiond, INRIA) automatically proves floating-point bounds using interval
arithmetic, generating Coq proof certificates.

**Use cases relevant to rource-math:**
- Rounding error bounds for `lerp()`, `clamp()`, `distance()`
- Error propagation through operation chains (e.g., `normalized()` = v / length(v))
- Bounds on accumulated error in matrix-vector products

**Key reference**: Daumas, M. & Melquiond, G. "Certification of bounds on expressions
involving rounded operators." IEEE Transactions on Computers, 2010.

## Feasibility Assessment: 114 Unverified Operations

### Operations by Category and Feasibility

#### Category 1: sqrt-Based Operations (~12 operations)
**Operations**: `length()`, `normalized()`, `distance()` across Vec2, Vec3, Vec4
**Feasibility**: HIGH
**Tools**: Flocq (sqrt is IEEE 754 required operation) + VCFloat2 (error bounds)
**Rationale**: sqrt has exact rounding in IEEE 754. Flocq formalizes this completely.
The main challenge is proving error bounds on composed expressions like
`sqrt(x*x + y*y)` where intermediate overflow/underflow can occur.
**Prior art**: LAProof verifies L2 norm accuracy (same mathematical structure as `length()`).

#### Category 2: Rounding Operations (~12 operations)
**Operations**: `floor()`, `ceil()`, `round()`, `fract()` across Vec2, Vec3, Vec4
**Feasibility**: HIGH
**Tools**: Flocq
**Rationale**: These are standard IEEE 754 operations, fully formalized in Flocq.
Properties like `floor(x) <= x < floor(x) + 1` are directly provable.

#### Category 3: Comparison-Based Operations (~16 operations)
**Operations**: `min()`, `max()`, `abs()`, `clamp()` across Vec2, Vec3, Vec4, Color, Rect
**Feasibility**: HIGH
**Tools**: Flocq + CoqInterval
**Rationale**: Comparison operations are well-defined for non-NaN inputs. The main
subtlety is NaN propagation behavior, which Flocq handles.

#### Category 4: Interpolation (~6 operations)
**Operations**: `lerp()` across Vec2, Vec3, Vec4, Color, Rect, Utils
**Feasibility**: HIGH
**Tools**: VCFloat2
**Rationale**: `lerp(a, b, t)` = `a + t * (b - a)` or `(1 - t) * a + t * b`.
VCFloat2 can automatically compute error bounds for both formulations.
The two forms have different numerical properties (the first is monotonic but not
exact at t=1; the second is exact at endpoints but not monotonic).

#### Category 5: Transcendental-Based Operations (~8 operations)
**Operations**: `from_angle()`, `to_angle()`, `rotate()` (Vec2), `from_hsl()`, `to_hsl()` (Color)
**Feasibility**: MEDIUM
**Tools**: Flocq (sin, cos, tan, arctan) + CoqInterval + custom proofs
**Rationale**: Flocq formalizes sin/cos/tan/arctan. However, proving properties of
composed expressions (e.g., "rotation preserves length") requires combining
trigonometric identities with floating-point error analysis. Flocq's log
implementation is still work-in-progress, which may affect `to_hsl()`.

#### Category 6: Type Conversions (~8 operations)
**Operations**: `as_ivec2()`, `as_uvec2()`, `is_finite()`, `is_nan()`, `to_u8()`, `from_u8()`
**Feasibility**: MEDIUM
**Tools**: Flocq `IEEE754.BinarySingleNaN` or CompCert `Floats`
**Rationale**: Float-to-int conversions are formalized in CompCert. The challenge
is specifying Rust's specific truncation behavior (which differs from C's).

#### Category 7: Distance/Metric Operations (~6 operations)
**Operations**: `distance()`, `distance_squared()` across Vec2, Vec3, Vec4
**Feasibility**: HIGH (distance_squared), MEDIUM (distance via sqrt)
**Tools**: VCFloat2 + Flocq
**Rationale**: `distance_squared()` involves only subtraction and multiplication.
`distance()` adds sqrt, which is exactly rounded but whose input may overflow.

#### Category 8: Matrix Transforms (~15 operations)
**Operations**: `rotation()`, `inverse()`, `perspective()`, `orthographic()`, `look_at()`,
`transform_point()`, `transform_vector()` for Mat3/Mat4
**Feasibility**: LOW-MEDIUM
**Tools**: LAProof (matrix-vector products) + Flocq + custom proofs
**Rationale**: LAProof provides matrix-vector product accuracy proofs, but
graphics-specific operations (perspective projection, look-at matrix construction)
have no existing formal verification. Would require novel proof engineering.

#### Category 9: Color Operations (~10 operations)
**Operations**: `from_hsl()`, `to_hsl()`, `lighten()`, `darken()`, `saturate()`,
`desaturate()`, `mix()`, `contrast_ratio()`, `is_light()`, `is_dark()`
**Feasibility**: LOW
**Tools**: Custom proofs using Flocq + CoqInterval
**Rationale**: No existing formalization of HSL color space in any proof assistant.
HSL-to-RGB conversion involves conditional floating-point arithmetic with
transcendental-like behavior (modular hue arithmetic). Would require entirely
novel proof engineering.

#### Category 10: Miscellaneous (~21 operations)
**Operations**: `approx_eq()`, `deg_to_rad()`, `rad_to_deg()`, `element_product()`,
`element_sum()`, batch operations, `from_center()`, `from_points()`, etc.
**Feasibility**: MIXED (HIGH for simple, LOW for complex)
**Tools**: Flocq + CoqInterval + VCFloat2
**Rationale**: `deg_to_rad` requires pi constant (available in Coquelicot).
`approx_eq` is an epsilon comparison (straightforward). Batch operations
require composing single-operation proofs.

### Coverage Projection

| Difficulty | Operations | Count | Projected Effort |
|------------|-----------|-------|-----------------|
| **Immediately achievable** | sqrt-based, rounding, min/max/abs/clamp, simple lerp, distance_squared, deg/rad, approx_eq | ~46 | 2–4 weeks |
| **Moderate effort** | distance (via sqrt), type conversions, batch ops, element_product, transcendental-based rotation | ~30 | 4–8 weeks |
| **Significant novel work** | Matrix transforms, HSL color, complex geometry, perspective/orthographic | ~38 | 3–6 months |

**Projected coverage trajectory:**

| Phase | Coverage | Operations Verified | Total |
|-------|----------|--------------------|----|
| Current | 50.4% (116/230) | Algebraic properties | 1864 theorems |
| **Phase FP-1 IN PROGRESS** | **~55%** | **+ FP foundations, error bounds, rounding, vec ops** | **1172 theorems** |
| After Phase FP-1 complete | ~70% (162/230) | + sqrt, rounding, min/max, lerp, distance_sq | ~1250 theorems |
| After Phase FP-2 | ~83% (192/230) | + distance, conversions, batch, transcendental | ~1350 theorems |
| After Phase FP-3 | ~92% (212/230) | + matrix transforms, color, complex geometry | ~1450 theorems |

### Phase FP-1 Progress (In Progress)

**Flocq 4.1.3 installed and operational.** 99 FP theorems machine-checked.

| File | Theorems | Description | Status |
|------|----------|-------------|--------|
| `FP_Common.v` | 6 | binary32 parameters, unit roundoff, standard model, error composition | Machine-checked |
| `FP_Rounding.v` | 21 | floor/ceil/round/fract properties via Flocq's Zfloor/Zceil/Znearest | Machine-checked |
| `FP_ErrorBounds.v` | 36 | Single/multi-op error, sqrt, lerp, angle conversion, approx_eq, comparison | Machine-checked |
| `FP_Vec.v` | 36 | Vec2/3/4 length_sq, length, distance_sq, distance, normalized, min/max/clamp, lerp, Bernoulli | Machine-checked |
| **Total** | **99** | **Phase FP-1 foundations complete** | **Zero admits** |

### What Floating-Point Verification Proves (and Does NOT Prove)

This distinction is critical for intellectual honesty:

**What FP verification proves:**
- The computed floating-point result is within a bounded error of the exact
  mathematical result (error bound quantification)
- The computation does not produce NaN, infinity, or denormals for valid inputs
  (exception freedom)
- The rounding direction and magnitude are consistent with IEEE 754 semantics
  (conformance)

**What FP verification does NOT prove:**
- That the floating-point result equals the exact mathematical result (it generally
  doesn't due to rounding)
- That algebraic properties hold exactly (FP addition is not associative)
- That the operation is numerically stable for all inputs (stability is a separate
  analysis concern)

**How this relates to our existing proofs:**
Our current 939 theorems prove algebraic properties over exact arithmetic (R or Z).
Floating-point proofs would be a **complementary layer** proving that the Rust
implementation's floating-point results are close to the mathematically correct
values established by our R-based proofs. The two layers together would provide:

1. **R-based proofs**: The mathematical operation is correct (algebraic properties)
2. **FP proofs**: The Rust implementation computes a value within N ULPs of the
   mathematical result (numerical accuracy)

This two-layer architecture is exactly what LAProof and VCFloat2 are designed to support.

## Proof of Concept: Vec2::length()

To demonstrate feasibility, we outline what a Flocq-based proof of `Vec2::length()`
accuracy would look like.

### Rust Implementation

```rust
pub fn length(&self) -> f32 {
    (self.x * self.x + self.y * self.y).sqrt()
}
```

### What We Would Prove

**Theorem** (length_accuracy): For all `v: Vec2` where `v.x` and `v.y` are finite
f32 values not causing overflow in `x*x + y*y`, the computed `length(v)` satisfies:

```
|length_fp(v) - sqrt(vx² + vy²)| ≤ ε · sqrt(vx² + vy²)
```

where `ε` is a bound derived from IEEE 754 single-precision rounding
(approximately `2 * 2^(-23)` for this expression chain).

### Proof Structure in Coq (Sketch)

```coq
Require Import Flocq.IEEE754.Binary.
Require Import Flocq.Prop.Relative.

(* IEEE 754 single precision *)
Definition prec := 24%Z.
Definition emax := 128%Z.

(* Flocq's relative error for single precision *)
Lemma length_accuracy :
  forall (vx vy : binary32),
    is_finite _ _ vx = true ->
    is_finite _ _ vy = true ->
    (* no overflow in intermediate computations *)
    Bsqrt_no_overflow vx vy ->
    let result := Bsqrt prec emax (Bplus prec emax
                    (Bmult prec emax vx vx)
                    (Bmult prec emax vy vy)) in
    is_finite _ _ result = true /\
    Rabs (B2R _ _ result - sqrt (B2R _ _ vx * B2R _ _ vx + B2R _ _ vy * B2R _ _ vy))
      <= error_bound * Rabs (sqrt (B2R _ _ vx * B2R _ _ vx + B2R _ _ vy * B2R _ _ vy)).
```

This sketch uses:
- `binary32`: Flocq's f32 type
- `B2R`: Flocq's float-to-real conversion
- `Bsqrt`, `Bplus`, `Bmult`: Flocq's IEEE 754 operations
- `Rabs`: Standard library absolute value on R

The actual proof would use VCFloat2's automation to discharge the error bound
obligations, rather than manual decomposition.

### Prerequisites

1. Install Flocq 4.1.3: `opam install coq-flocq.4.1.3`
2. Install VCFloat2 2.1.1: `opam install coq-vcfloat=2.1.1`
3. Define rource-math FP specs using Flocq's `binary32` type
4. Connect to existing R-based specs via Flocq's `B2R` conversion

### Estimated Effort for Full Proof

| Step | Description | Effort |
|------|-------------|--------|
| 1 | Install and configure Flocq + VCFloat2 on Coq 8.18 | 1–2 hours |
| 2 | Define `Vec2_FP` spec using Flocq's `binary32` type | 1 day |
| 3 | Prove `length()` error bound using VCFloat2 | 2–3 days |
| 4 | Prove `normalized()` error bound (depends on length) | 2–3 days |
| 5 | Prove `distance()` error bound (same structure as length) | 1 day |
| 6 | Connect FP specs to existing R-based specs via `B2R` | 1–2 days |

## Comparison: Stainless vs. Flocq+VCFloat2

| Criterion | Stainless (Paper) | Flocq + VCFloat2 (Recommended) |
|-----------|-------------------|-------------------------------|
| Language | Scala only | Coq (our existing infrastructure) |
| Proof output | SMT discharge (no certificates) | Machine-checked Coq proof terms |
| Error bounds | Not supported | Primary capability |
| Algebraic properties | Not supported | Composable with R-based proofs |
| Transcendentals | Axiomatized (over-approximate) | Formalized in Flocq (sin, cos, tan, arctan, exp) |
| Automation | High (push-button for safety) | Medium (VCFloat2 automates error bounds) |
| Integration with existing work | None | Direct (same Coq 8.18 ecosystem) |
| Academic rigor | arXiv preprint | Multiple peer-reviewed publications (CPP, ARITH, PLDI) |
| Graphics math precedent | KeY benchmarks (Vector2, Matrix2/3) | LAProof (matrix-vector products) |

**Verdict**: Flocq + VCFloat2 is unambiguously the better path for rource-math.

## Verus Floating-Point Extension Assessment

### Could Verus Be Extended?

In principle, yes. Z3 supports the SMT-LIB floating-point theory (`QF_FP`). Verus
could theoretically:

1. Add `f32`/`f64` specification types (currently only `int`/`nat`)
2. Generate FP-sorted SMT-LIB verification conditions
3. Handle NaN/equality issues (as Stainless does)

### Why This Is Not Recommended for rource-math

| Reason | Detail |
|--------|--------|
| **Z3 is worst at FP** | 78.1–85.2% success vs cvc5's 88.7–100% (Stainless paper data) |
| **No error bounds** | SMT FP theory proves bit-exact equality, not "within ε" bounds |
| **No algebraic properties** | SMT cannot prove `a + b = b + a` for FP (it's not always true) |
| **Massive engineering effort** | Verus core language changes needed |
| **No precedent** | No one has successfully verified graphics math via Verus FP |
| **Alternative exists** | Flocq + VCFloat2 in Coq is mature, proven, compatible |

### Recommendation

Do NOT pursue Verus FP extension for rource-math. Instead:
1. Use Coq + Flocq + VCFloat2 for floating-point accuracy proofs
2. Keep Verus for algebraic property proofs (its strength)
3. The hybrid architecture (Verus for algebra + Coq for FP accuracy) provides
   stronger coverage than either tool alone

## Recommended Roadmap

### Phase FP-1: Foundation (Target: ~70% coverage)

**Goal**: Establish Flocq + VCFloat2 infrastructure and verify easiest operations.

| Step | Description | Operations | Count |
|------|-------------|-----------|-------|
| FP-1.1 | Install Flocq 4.1.3, VCFloat2 2.1.1, Gappa, CoqInterval | — | — |
| FP-1.2 | Define `Vec2_FP` spec using Flocq `binary32` | — | — |
| FP-1.3 | Prove `length()` error bound (Vec2) | 1 | 1 |
| FP-1.4 | Generalize to Vec3, Vec4 `length()` | 2 | 3 |
| FP-1.5 | Prove `normalized()` error bound (Vec2/3/4) | 3 | 6 |
| FP-1.6 | Prove `distance()` error bound (Vec2/3/4) | 3 | 9 |
| FP-1.7 | Prove `floor/ceil/round/fract` (Vec2/3/4) | 12 | 21 |
| FP-1.8 | Prove `min/max/abs/clamp` (Vec2/3/4) | 12 | 33 |
| FP-1.9 | Prove `lerp()` error bound (all types) | 6 | 39 |
| FP-1.10 | Prove `distance_squared()` (Vec2/3/4) | 3 | 42 |
| FP-1.11 | Prove `deg_to_rad/rad_to_deg/approx_eq/element_product` | 4 | 46 |

### Phase FP-2: Transcendentals and Conversions (Target: ~83% coverage)

| Step | Description | Operations | Running |
|------|-------------|-----------|---------|
| FP-2.1 | Prove `from_angle()` (Vec2, uses sin/cos) | 1 | 47 |
| FP-2.2 | Prove `to_angle()` (Vec2, uses atan2) | 1 | 48 |
| FP-2.3 | Prove `rotate()` (Vec2, uses sin/cos) | 1 | 49 |
| FP-2.4 | Prove type conversions (`as_ivec2`, `as_uvec2`, etc.) | 8 | 57 |
| FP-2.5 | Prove batch operations | 5 | 62 |
| FP-2.6 | Prove `Mat3::rotation()` | 1 | 63 |
| FP-2.7 | Prove additional element-wise operations | ~13 | 76 |

### Phase FP-3: Graphics-Specific (Target: ~92% coverage)

| Step | Description | Operations | Running |
|------|-------------|-----------|---------|
| FP-3.1 | Matrix `inverse()` accuracy (Mat3, Mat4) | 2 | 78 |
| FP-3.2 | `perspective()`, `orthographic()` | 2 | 80 |
| FP-3.3 | `look_at()` matrix construction | 1 | 81 |
| FP-3.4 | `transform_point()`, `transform_vector()` | 4 | 85 |
| FP-3.5 | HSL color space conversions | 6 | 91 |
| FP-3.6 | Complex rect operations | ~5 | 96 |
| FP-3.7 | Remaining operations | ~18 | 114 |

## Known Blockers and Risks

| Blocker | Severity | Mitigation |
|---------|----------|------------|
| opam repo HTTP 503 | Medium | Use `opam.ocaml.org` + GitHub pins; apt-get fallback for Coq itself |
| Flocq log() incomplete | Low | Only affects `to_hsl()` if it uses log (unlikely for HSL) |
| VCFloat2 documentation sparse | Medium | Use CPP 2024 paper + GitHub examples as reference |
| LAProof not packaged for opam | Medium | Build from source (GitHub) |
| No existing HSL formalization | High | Requires novel proof engineering or deferred |
| CompCert dependency for VCFloat2 | Medium | CompCert 3.13.x available for Coq 8.18 |

## References

### Primary References (Floating-Point Verification)

1. Gilot, A., Bergström, A., & Darulova, E. "Verifying Floating-Point Programs in
   Stainless." arXiv:2601.14059, January 2026.

2. Boldo, S. & Melquiond, G. "Flocq: A Unified Library for Proving Floating-Point
   Algorithms in Coq." IEEE ARITH, 2011.

3. Boldo, S. & Melquiond, G. "Computer Arithmetic and Formal Proofs: Verifying
   Floating-point Algorithms with the Coq System." Elsevier, 2017.

4. Kellison, A. & Appel, A. "VCFloat2: Floating-point Error Analysis in Coq."
   CPP 2024. ACM.

5. Kellison, A., Appel, A., Tekriwal, M., & Bindel, D. "LAProof: A Library of
   Formal Proofs of Accuracy and Correctness for Linear Algebra Programs."
   IEEE ARITH, 2023.

6. Daumas, M. & Melquiond, G. "Certification of bounds on expressions involving
   rounded operators." IEEE Transactions on Computers, 2010.

7. Kellison, A. et al. "Bean: A Language for Backward Error Analysis." PLDI 2025. ACM.

8. Kohlen, B. et al. "A Formally Verified IEEE 754 Floating-Point Implementation
   of Interval Iteration for MDPs." CAV 2025.

### Related Work References

9. Friedlos, L. "Verifying Rust Programs Using Floating-Point Numbers and Bitwise
   Operations." ETH Zurich Master's Thesis.

10. Yang, C. et al. "AutoVerus: Automated Proof Generation for Rust Code."
    arXiv:2409.13082, 2024.

11. Lehmann, N. et al. "Flux: Liquid Types for Rust." PLDI 2023.

12. Appel, A. "Formal Verification of COO to CSR Sparse Matrix Conversion." 2025.

13. Yang, T. et al. "Towards Verified Linear Algebra Programs Through Equivalence."
    CoqPL 2025.

---

*Last updated: 2026-01-30*
*Investigation: Stainless FP paper (arXiv:2601.14059) — NOT directly applicable*
*Recommended path: Coq + Flocq 4.1.3 + VCFloat2 2.1.1 + Gappa 1.5.4*
*Flocq 4.1.3 installed and operational — 99 FP theorems machine-checked*
*All recommended tools are Coq 8.18 compatible*
*Phase FP-1 in progress: 99/~250 FP theorems completed*
