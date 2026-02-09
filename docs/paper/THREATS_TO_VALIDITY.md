# Threats to Validity

This document provides a comprehensive analysis of threats to validity for the
rource-math formal verification effort, suitable for inclusion in Section 7
(Discussion) of the academic paper.

---

## 1. Specification Fidelity (Internal Validity)

### Threat: Manual Specification May Not Match Implementation

All Coq and Verus specifications were written manually by inspecting the Rust
implementation. This manual translation process is the single largest trust
assumption in our verification effort. If a specification incorrectly models
the implementation, the proven properties may not apply to the actual code.

### Assessment

We audited all 219 verified operations and classified them into three
correspondence categories:

| Category | Count | % | Risk Level |
|----------|-------|---|------------|
| **S** (Structural match) | ~130 | 59% | Low: field-by-field translation, obvious by inspection |
| **E** (Semantic equivalence) | ~60 | 27% | Low-Medium: same algorithm, different formulation |
| **C** (Careful attention) | ~29 | 13% | Medium: FP modeling, sqrt, rounding, literal precision |

For 86% of operations (categories S and E), the correspondence is
straightforward and verifiable by inspection. The remaining 13% involve
floating-point modeling decisions that are documented and mitigated
(see Section 3 below).

### Mitigations

1. **Dual specification**: Both Verus (integer model) and Coq (real model)
   independently specify the same operations. Specification errors would need
   to appear in *both* independent translations.

2. **Unit test cross-validation**: All 219 verified operations have
   corresponding unit tests (2900+ tests total) that empirically validate
   runtime behavior. A specification error that causes the spec to diverge
   from actual behavior would need to also evade unit test detection.

3. **Systematic translation methodology**: Specifications follow the Rust
   implementation structure (same field order, same algorithm, same control
   flow). This systematic approach reduces the likelihood of semantic drift.

4. **10-operation end-to-end audit**: We conducted a detailed audit of 10
   representative operations spanning all correspondence categories, examining
   exact Rust code, Coq spec, Verus proof, and Kani harness side by side.
   Result: 7/10 have no meaningful gap; 3/10 have documented and quantified
   gaps (see `docs/paper/TEN_OPERATION_AUDIT.md`).

### Residual Risk

Manual specification remains the primary threat to validity. We acknowledge
that machine-checked translation (e.g., via Aeneas or rocq-of-rust) would
provide stronger guarantees. Current tools do not support f32 types
adequately for our use case (see `docs/verification/VERIFICATION_COVERAGE.md`
for detailed assessment of rocq-of-rust and Aeneas).

---

## 2. Floating-Point Abstraction Gap (Construct Validity)

### Threat: Proofs Over R Do Not Guarantee Properties Over f32

The Coq R-based layer proves properties over mathematical real numbers (R).
The Rust implementation computes over IEEE 754 binary32 (f32). These are
fundamentally different algebraic structures:

| Property | R (reals) | f32 (IEEE 754 binary32) |
|----------|-----------|-------------------------|
| Associativity of + | Yes | No |
| Commutativity of + | Yes | Yes (for finite values) |
| x + 0 = x | Yes | Yes (except -0.0 + 0.0 = 0.0) |
| x + e > x for e > 0 | Yes | No (when e < ULP(x)) |
| Division by zero | Undefined | ±Infinity or NaN |
| Overflow | Impossible | Saturates to ±Infinity |

### Assessment

This gap is real and cannot be fully eliminated. It is the fundamental
limitation of algebraic verification for floating-point code.

### Mitigations (Three-Layer Defense)

| Layer | Tool | What It Provides |
|-------|------|------------------|
| 1. Algebraic correctness | Coq (R) + Verus (int) | Property holds for exact arithmetic |
| 2. Error quantification | Coq (Flocq, 361 thms) | `\|f32_op(x,y) - R_op(x,y)\| <= eps` for bounded inputs |
| 3. Bit-precise safety | Kani (CBMC, 272 harnesses) | f32 operation is finite (no NaN/overflow) for bounded domain |

Together, these three layers establish:
- The *ideal* property holds (layer 1)
- The *f32 deviation* from ideal is bounded (layer 2)
- The *f32 result* is well-defined (layer 3)

### Concrete Evidence: 4 IEEE 754 Bugs

Kani discovered 4 concrete bugs where algebraic proofs are correct but f32
behavior diverges:

| Bug | Operation | Why Algebraic Proof Doesn't Catch It |
|-----|-----------|--------------------------------------|
| 1 | `lerp(MAX, -MAX, 0.0)` -> NaN | `a + t*(b-a)` is correct for R; `b-a` overflows for f32 |
| 2 | `Vec2::project(denorm)` -> NaN | `dot/len_sq` correct for R; overflows to inf for f32 |
| 3 | `Rect::intersects(self)` -> false | `x + w > x` always true for R when w>0; false for f32 when w < ULP(x) |
| 4 | `from_center_size` roundoff | `cx - w/2 + w/2 = cx` for R; catastrophic cancellation for f32 |

These bugs validate the necessity of the triple-verification approach.

### Residual Risk

For the 29 Category-C operations, the gap between R and f32 is non-trivial.
While Flocq bounds quantify the deviation, we cannot guarantee that every
user-visible behavior matches the specification for all inputs. Users must
respect the bounded input domains documented with each Kani harness.

---

## 3. Bounded Model Checking Completeness (Internal Validity)

### Threat: Kani Verifies Bounded Domains, Not Universal Properties

Kani/CBMC uses bounded model checking: it exhaustively verifies all inputs
within a specified domain but does not provide universal quantification.
A property verified for `|x| < 1e6` may fail at `|x| = 1e7`.

### Assessment

The bounds used in Kani harnesses are chosen based on the rource-math library's
intended use case (graphics/visualization):

| Domain Parameter | Kani Bound | Justification |
|------------------|------------|---------------|
| Vec2/Vec3/Vec4 components | `\|x\| < 1e6` | Screen coordinates + margin |
| Color components | `0.0 <= x <= 1.0` | Normalized color space |
| Rect dimensions | `0 < w,h < 1e4` | Viewport dimensions |
| Matrix elements | `\|m\| < 1e4` | Transform matrices |
| Interpolation parameter t | `0.0 <= t <= 1.0` | Standard interpolation range |

### Mitigations

1. **Domain documentation**: Each Kani harness documents its input bounds
   and the rationale for those bounds.

2. **Conservative bounds**: Bounds are chosen to be larger than typical use
   cases, providing margin for edge-case behavior.

3. **Complementary universal proofs**: Coq and Verus proofs provide universal
   quantification (for all values in R or int). Kani provides bounded
   verification at the implementation level.

### Residual Risk

Users who exceed the documented input bounds may encounter behavior not
covered by Kani verification. This is inherent to bounded model checking
and is documented as a known limitation.

---

## 4. Unverified Operations (External Validity)

### Threat: 14.5% of Operations Are Not Formally Verified

37 out of 256 public operations lack formal proofs.

### Breakdown

| Category | Count | Examples | Blocker |
|----------|-------|---------|---------|
| Transcendentals | 10 | `sin`, `cos`, `atan2`, `rotation` | No SMT/Coq theory for f32 transcendentals |
| HSL conversions | 2 | `from_hsl`, `to_hsl` | Transcendental dependencies |
| Batch operations | 7 | `mul_add`, `select` | Trivially follow from single-op proofs |
| FP predicates | 3 | `is_finite`, `is_nan` | Bit-level predicates (Kani covers these) |
| Complex geometry | 3 | `transform_by_mat3/4`, `from_points` | Multi-step composition or iterators |
| Type conversions | 2 | `as_ivec2`, `as_uvec2` | Platform-specific integer semantics |
| New methods | ~10 | `with_lightness`, `min`/`max` on Rect | Recently added, proofs pending |

### Mitigations

1. **Unit test coverage**: All 37 unverified operations have unit tests (100%
   test coverage maintained).

2. **Kani partial coverage**: FP predicates (`is_finite`, `is_nan`) and
   transcendental users (`rotation`) have Kani NaN-freedom harnesses.

3. **Mathematical triviality**: 7 batch operations follow trivially from
   already-proven single-operation properties.

4. **Documented rationale**: Each unverified operation has a documented reason
   for its exclusion, not an oversight.

### Residual Risk

Transcendental functions (10 operations) represent a fundamental gap that
cannot be closed with current tools. This is a known open problem in formal
verification of floating-point programs.

---

## 5. Proof Engineering Methodology (Construct Validity)

### Threat: Verus Z3 Proofs Are Solver-Dependent

Verus proofs rely on Z3's decision procedures. Unlike Coq's constructive
proofs, Z3 proofs are not independently verifiable proof objects. If Z3
contains a soundness bug, proofs may be invalid.

### Assessment

| Aspect | Verus/Z3 | Coq |
|--------|----------|-----|
| Proof type | SMT certificate (solver-dependent) | Constructive term (kernel-checked) |
| Trusted base | Z3 solver + Verus VIR compiler | Coq kernel (small, well-audited) |
| Soundness track record | Z3 has had soundness bugs | Coq kernel has been stable for decades |
| Reproducibility | May depend on Z3 version | Deterministic |

### Mitigations

1. **Dual verification**: The majority of properties verified by Verus (498
   proof fns) have corresponding Coq theorems (1366 R-based + 471 Z-based
   theorems), though the mapping is not strictly 1:1 due to differing
   specification granularity. A Z3 soundness bug would need to coincide
   with a Coq proof error for a shared property to be incorrectly verified.

2. **Different proof strategies**: Verus uses `nonlinear_arith` and custom
   lemma decomposition; Coq uses tactics (`ring`, `field`, `lra`, custom
   `Ltac`). The probability of both tools having correlated soundness bugs
   for the same property is extremely low.

3. **Kani cross-validation**: Kani/CBMC provides a third independent check
   using bounded model checking with SAT/SMT solving, further reducing
   correlated failure risk.

### Residual Risk

We cannot fully eliminate dependence on tool soundness. This is a
fundamental limitation shared by all mechanized verification efforts.
Our triple-verification approach minimizes this risk through diversity.

---

## 6. Compilation and Extraction (External Validity)

### Threat: Coq-to-WASM Pipeline Has Unverified Steps

The extraction pipeline from Coq specifications to executable WASM has
unverified components:

| Stage | Tool | Verified? |
|-------|------|-----------|
| Coq Z-based specs | Coq 8.18 | Yes (kernel-checked) |
| Coq -> OCaml extraction | Standard Extraction | **No** (known unverified) |
| OCaml -> WASM | wasm_of_ocaml 6.2.0 | **No** |

### Mitigations

1. **Standard Extraction track record**: Coq's standard extraction has been
   used by CompCert and Fiat-Crypto for production code generation for over
   a decade with no known semantic bugs.

2. **MetaCoq alternative**: We have tested MetaCoq Verified Extraction
   (Sozeau et al., PLDI 2024) on a subset of our types (9 ZVec2 operations).
   Full migration to verified extraction is feasible but blocked by MetaCoq's
   compilation time (~15 minutes for our development).

3. **WASM test suite**: The extracted WASM library includes a test driver
   (`test_extracted.wasm`, 42.2 KB) that validates output correctness.

### Residual Risk

The extraction pipeline is the weakest link in the end-to-end verification
chain. We are transparent about this limitation and document the exact trust
boundaries.

---

## 7. Generalizability (External Validity)

### Threat: Results May Not Generalize Beyond Graphics Math

rource-math is a specific domain (graphics/visualization math with 9 types).
The triple-verification methodology may not generalize to:

- **Higher-dimensional types**: Scaling beyond 4x4 matrices
- **Non-pure functions**: Operations with side effects or state
- **Dynamic data structures**: Linked lists, trees, graphs
- **Concurrent code**: Shared mutable state

### Assessment

The methodology is most applicable to pure mathematical libraries with
algebraic properties. The core insight (SMT + ITP + BMC complement each
other) is domain-independent, but the specific techniques (lemma
decomposition for polynomial identities, layered Coq architecture, Flocq
error bounds) are tailored to numerical computation.

### Mitigations

1. **Clearly scoped claims**: We claim triple verification for a *math
   library*, not for arbitrary Rust code.

2. **Generalizable contributions**: The lemma decomposition technique (C2),
   layered Coq architecture (C3), and tool comparison methodology (C1) are
   applicable beyond our specific domain.

### Residual Risk

Replication studies on other domains (e.g., cryptographic math, scientific
computing, game physics) would strengthen the generalizability claim. We
encourage such work.

---

## 8. Count Methodology (Construct Validity)

### Threat: Theorem/Harness Counts May Be Inflated

Our headline count (2968 theorems/harnesses) could be questioned if
individual theorems are trivial or if counting methodology is inconsistent.

### Counting Rules

| Tool | What We Count | Extraction Method |
|------|---------------|-------------------|
| Verus | `proof fn` declarations | `grep -c 'proof fn' *.rs` |
| Coq (R) | `Theorem` + `Lemma` + `Local Lemma` | `grep -cE '^(Theorem\|Lemma\|Local Lemma)' *.v` |
| Coq (Z) | Same as above in `*_Compute.v` | Same grep pattern |
| Coq (FP) | Same as above in `FP_*.v` | Same grep pattern |
| Kani | `#[kani::proof]` attributes | `grep -rc '#\[kani::proof\]' crates/rource-math/src/kani_proofs/` |

### Assessment of Triviality

Not all theorems are equally deep. Distribution by complexity:

| Complexity | Approximate Count | Example |
|------------|-------------------|---------|
| Trivial (1-2 tactic) | ~15% | `vec2_add_comm` (unfold, ring) |
| Standard (3-10 tactic) | ~55% | `rect_intersection_comm` (unfold, case split, lra) |
| Non-trivial (10+ tactic) | ~25% | `mat4_mul_assoc` (300+ lemma calls) |
| Deep (custom automation) | ~5% | FP error composition, complexity proofs |

### Mitigations

1. **Automated counting**: `scripts/update-verification-counts.sh` extracts
   counts directly from source files using grep, ensuring reproducibility.

2. **Per-type breakdown**: Counts are reported per type and per tool, not
   just as a single aggregate number.

3. **Zero admits**: We report zero admits, which is independently verifiable
   by checking for `admit` / `Admitted` / `assume!` in the source files.

### Residual Risk

Theorem count is a proxy metric. A more meaningful metric might be
"specification coverage" (what percentage of the mathematical behavior space
is covered), but no standard methodology exists for measuring this.

---

## Summary of Residual Risks

| Threat | Severity | Mitigation Level | Residual Risk |
|--------|----------|-------------------|---------------|
| Manual specification | High | Strong (dual verification, unit tests) | Medium: machine translation not feasible |
| FP abstraction gap | High | Strong (Flocq + Kani + 3-layer) | Low: gap is quantified and documented |
| Bounded domains | Medium | Adequate (conservative bounds) | Low: exceeding bounds documented |
| Unverified operations | Medium | Adequate (unit tests, Kani partial) | Low: transcendentals are known open problem |
| Solver dependence | Low | Strong (triple verification) | Very low: correlated failure unlikely |
| Extraction pipeline | Medium | Moderate (MetaCoq partial) | Medium: unverified steps remain |
| Generalizability | Medium | Adequate (scoped claims) | Medium: replication needed |
| Count methodology | Low | Strong (automated, per-type) | Very low: reproducible extraction |

---

## Comparison with Related Work Threats

| Project | Primary Threat | How We Compare |
|---------|----------------|----------------|
| Fiat-Crypto | Extraction correctness | Same risk; we also use standard extraction |
| CompCert | Unverified parser + assembler | Similar trust boundary approach |
| mathlib4 | No executable code connection | We additionally connect to executable Rust |
| LAProof | Manual C-to-Coq spec | Same risk; our Rust-to-Coq gap is similar |
| Stainless FP | Solver-dependent only | We mitigate with Coq (solver-independent) |

---

*Created: 2026-02-06*
*Based on: SPEC_IMPL_CORRESPONDENCE.md, TEN_OPERATION_AUDIT.md, VERIFICATION_COVERAGE.md*
*All counts verified against metrics/verification-counts.json*
