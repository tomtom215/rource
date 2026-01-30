# Rust Formal Verification Landscape Assessment

This document surveys the broader Rust formal verification ecosystem to identify
tools that could address capability gaps in rource-math's current verification
architecture. Each tool is assessed for applicability to our specific use case:
mathematical types (Vec2-4, Mat3-4, Color, Rect) with f32 fields.

For the current verification architecture, see [FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md).
For coverage metrics, see [VERIFICATION_COVERAGE.md](VERIFICATION_COVERAGE.md).
For floating-point feasibility, see [FLOATING_POINT_VERIFICATION.md](FLOATING_POINT_VERIFICATION.md).

## Executive Summary

| Tool | Category | FP Support | Spec-to-Impl Bridge | Recommendation |
|------|----------|------------|---------------------|----------------|
| **Verus** (current) | SMT/Z3 | No (int specs) | Manual specs | KEEP (algebraic proofs) |
| **Coq** (current) | Proof assistant | Via Flocq (planned) | Manual specs | KEEP (machine-checked proofs) |
| **Kani** (adopted) | Bounded model checker | YES (bit-precise) | No (assertion-based) | **ADOPTED** (45 harnesses, 0 failures) |
| **Aeneas** | Functional translation | Unknown | YES (pure functional) | **MONITOR** (spec-to-impl) |
| **Creusot** | Deductive verifier | Via Why3 ieee_float | Inline annotations | **MONITOR** (Why3 FP) |
| **hax** | Extraction tool | No (backends lack FP) | YES (THIR extraction) | NOT APPLICABLE |
| **rocq-of-rust** (investigated) | Monadic extraction | No (UnsupportedLiteral) | Monadic (unsuitable) | NOT VIABLE |
| **Stainless** (investigated) | Scala verifier | NaN/safety only | N/A (Scala-only) | NOT APPLICABLE |

## Current Capability Gaps

Our verification architecture (Verus + Coq) achieves 1073 theorems across 8 types
with zero admits. The identified gaps are:

| Gap | Description | Blocked Operations | Impact |
|-----|-------------|-------------------|--------|
| **G1: Floating-point** | Cannot verify FP operations (sqrt, sin/cos, rounding) | 114/230 (49.6%) | 50.4% coverage ceiling |
| **G2: Spec-to-impl** | Manual Coq specs (trusted, not machine-generated) | All 230 | Specification trustworthiness |
| **G3: Edge cases** | No NaN/overflow/infinity verification | ~40 FP operations | Runtime safety |
| **G4: Transcendentals** | No sin/cos/tan/atan2 verification | ~8 operations | Rotation, angle functions |

## Tool 1: Kani (Bounded Model Checker)

### Profile

| Property | Value |
|----------|-------|
| **Repository** | [github.com/model-checking/kani](https://github.com/model-checking/kani) |
| **Maintainer** | Amazon Web Services |
| **Version** | 0.67.0 (January 2026) |
| **Backend** | CBMC (C Bounded Model Checker) |
| **Commits** | 2,390+ |
| **Stars** | 2,200+ |
| **Rust version** | Requires Rust 1.58+ |
| **License** | MIT / Apache-2.0 |
| **CI integration** | GitHub Actions via `model-checking/kani-github-action` |

### What It Does

Kani is a **bit-precise model checker** that exhaustively checks all possible input
values (up to a bound) rather than sampling. It compiles Rust to CBMC's intermediate
representation, which is then solved via SAT/SMT. This is fundamentally different
from Verus (deductive, unbounded) and Coq (interactive theorem proving).

### Floating-Point Support

**YES** — Kani provides bit-precise verification of floating-point operations:

- CBMC models IEEE 754 semantics at the bit level
- Verifies absence of NaN, infinity, and overflow for valid inputs
- Can check `to_int_unchecked` safety for f32/f64 → integer conversions
- Recent improvement (v0.59.0): does not report arithmetic overflow for
  FP operations producing ±Inf (configurable)
- Has verified `to_int_unchecked` for f16, f32, f64, f128 (December 2024 blog post)

### Applicability to rource-math

**Addresses Gap G3 (edge cases)** directly:

| Capability | Applicability | Example |
|------------|--------------|---------|
| NaN detection | HIGH | Verify `vec2.length()` never produces NaN for finite inputs |
| Overflow detection | HIGH | Verify `dot()` doesn't overflow for bounded inputs |
| Infinity check | HIGH | Verify `normalized()` doesn't produce Inf for non-zero inputs |
| Assertion checking | HIGH | Verify `lerp(a, b, t)` returns finite for finite a, b, 0≤t≤1 |
| Functional correctness | MEDIUM | Verify `clamp(v, lo, hi)` returns value in [lo, hi] (bounded) |
| Algebraic properties | LOW | Cannot prove universally quantified properties |

**Example harness for rource-math:**

```rust
#[kani::proof]
fn verify_vec2_length_no_nan() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(x.abs() < 1e18);
    kani::assume(y.abs() < 1e18);
    let v = Vec2::new(x, y);
    let len = v.length();
    assert!(len.is_finite() || (x == 0.0 && y == 0.0 && len == 0.0));
    assert!(!len.is_nan());
    assert!(len >= 0.0);
}
```

### Limitations

| Limitation | Impact on rource-math |
|-----------|----------------------|
| **Bounded** — only checks inputs up to a bound | Cannot prove universal properties (∀ x, P(x)) |
| **No algebraic proofs** — checks assertions, not theorems | Complements but doesn't replace Verus/Coq |
| **Scalability** — complex FP expressions may timeout | Mat4 determinant (16 fields) may be challenging |
| **No proof certificates** — verification result, not Coq term | Cannot extend our 1567-theorem corpus |

### Recommendation: **ADOPT**

Kani directly addresses Gap G3 (edge case verification) which neither Verus nor Coq
can handle. It provides bit-precise floating-point verification that complements our
algebraic proofs. Recommended integration:

1. Add Kani harnesses for safety-critical FP operations (~40 operations)
2. Integrate into CI via GitHub Actions
3. Focus on: `length()`, `normalized()`, `distance()`, `lerp()`, `determinant()`,
   `inverse()`, `clamp()`, and type conversion operations
4. Document as a third verification layer alongside Verus and Coq

**Estimated coverage improvement:** +~40 operations verified for edge-case safety
(these operations would be "partially verified" — algebraic properties via Verus/Coq,
edge-case safety via Kani).

## Tool 2: Aeneas (Functional Translation)

### Profile

| Property | Value |
|----------|-------|
| **Repository** | [github.com/AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas) |
| **Frontend** | [Charon](https://github.com/AeneasVerif/charon) (Rust MIR extraction) |
| **Maintainer** | Inria (Son Ho, Jonathan Protzenko) |
| **Commits** | 4,378+ |
| **Stars** | 543+ |
| **Backends** | F*, Coq, HOL4, Lean (Lean and HOL4 most mature) |
| **Publications** | ICFP 2022 (functional translation), ICFP 2024 (borrow checker soundness) |
| **Users** | Microsoft SymCrypt (cryptographic library verification) |
| **License** | Apache-2.0 |

### What It Does

Aeneas translates safe Rust programs from MIR to **purely functional code** via
a multi-stage pipeline:

1. **Charon**: Extracts Rust MIR into LLBC (Low-Level Borrow-aware Code)
2. **Symbolic execution**: Computes a precise borrow graph at every program point
3. **Functional translation**: Produces pure lambda calculus (no memory model)
4. **Backend emission**: Generates F*, Coq, HOL4, or Lean code

Key properties of the translation:
- **Value-based semantics**: No memory, addresses, or pointer arithmetic
- **Ownership-centric**: Borrows enforced via semantic criterion, not separation logic
- **Forward/backward functions**: Forward computes results, backward handles borrows
- **No annotations needed**: Translation is fully automatic

### Critical Difference from rocq-of-rust

| Aspect | Aeneas | rocq-of-rust |
|--------|--------|-------------|
| Semantics | Value-based (pure functional) | Memory-based (monadic) |
| Output style | `let result = f(a, b)` | `M.alloc; M.call_closure; M.read` |
| Memory model | Eliminated by translation | Preserved in output |
| f32 support | Unknown (not documented) | `UnsupportedLiteral` |
| Admits | None in translation | Structural `Admitted` |
| Proof style | Natural mathematical reasoning | Monadic reasoning required |

Aeneas's **pure functional** output is fundamentally different from rocq-of-rust's
**monadic** output. The functional form is much closer to our existing Coq specs:

```
Our manual Coq spec:    vec2_add a b := mk_vec2 (vx a + vx b) (vy a + vy b)
Aeneas (expected):      vec2_add a b := { x := a.x + b.x; y := a.y + b.y }
rocq-of-rust (actual):  add ε τ α := M.monadic (M.alloc ... M.call_closure ...)
```

### Floating-Point Support

**Unknown/Undocumented.** The Charon tracking issue for unsupported Rust features
(#142) does not list f32/f64 as unsupported, but no positive confirmation exists
either. The tool's focus is on safe Rust programs used in cryptography (integers),
not floating-point-heavy numerical code.

**Risk assessment:**
- Charon extracts MIR types, which include f32/f64 as primitive types
- The LLBC representation should include float operations
- The functional translation may handle f32 as an abstract/opaque type
- Verification of FP properties would depend on the backend's FP theory

### Applicability to rource-math

**Potentially addresses Gap G2 (spec-to-impl bridge):**

| Scenario | Feasibility | Effort |
|----------|------------|--------|
| Extract Vec2/Vec3/Vec4 to Lean/Coq | MEDIUM | 1-2 weeks if f32 handled |
| Connect to existing Coq proofs | MEDIUM | Bridge functional output to R-based specs |
| Verify algebraic properties | HIGH (if extraction works) | Proofs on extracted code |
| Full rource-math extraction | LOW-MEDIUM | Many types, trait impls, complex code |

### Blockers

1. **f32 support unconfirmed** — May produce opaque types for floats
2. **Coq backend less mature** than Lean/HOL4
3. **Requires nightly Rust** (Charon uses rustc internals)
4. **No existing precedent** for graphics math verification

### Recommendation: **MONITOR**

Aeneas is the most promising tool for closing the spec-to-impl gap due to its pure
functional translation (vs. rocq-of-rust's monadic approach). However:

1. **Blocked on f32 support confirmation** — Check Charon source for `FloatTy` handling
2. If f32 is handled, attempt extraction of a minimal Vec2 subset
3. Compare generated Coq output to our manual specs for bridgeability
4. Re-evaluate quarterly as the tool matures

## Tool 3: Creusot (Deductive Verifier via Why3)

### Profile

| Property | Value |
|----------|-------|
| **Repository** | [github.com/creusot-rs/creusot](https://github.com/creusot-rs/creusot) |
| **Maintainer** | Inria (Xavier Denis, Claude Marché, Jacques-Henri Jourdan) |
| **Version** | 0.9.0 (January 2026) |
| **Backend** | Why3 platform → SMT solvers (CVC5, Z3, Alt-Ergo) + Coq |
| **Commits** | 4,331+ |
| **Stars** | 1,500+ |
| **Spec language** | Pearlite (Rust annotation language) |
| **Publications** | PhD thesis + HAL reports |
| **License** | LGPL-2.1 |

### What It Does

Creusot translates Rust MIR to Coma (Why3's intermediate verification language),
then dispatches verification conditions to SMT solvers. Users write specifications
as Pearlite annotations in Rust source code (similar to Verus).

### Floating-Point Support

**Potentially available via Why3's `ieee_float` theory**, but Creusot integration
is undocumented:

- Why3 provides comprehensive `Float32` and `Float64` types with IEEE 754 axioms
- Operations: add, sub, mul, div, FMA, sqrt, rounding, conversions
- Five rounding modes (RNE, RNA, RTP, RTN, RTZ)
- Special value predicates (is_nan, is_infinite, is_finite, is_normal)
- Used successfully in SPARK (Ada) and Frama-C (C) for industrial FP verification
- Creusot currently maps `i64 → Int` via the `@` view operator, but no documented
  `f32 → Float32` mapping exists

**Key question:** Does Creusot map Rust's `f32` to Why3's `Float32`? If yes,
this could enable deductive FP verification (complementing our Coq+Flocq path).
If no, this is an unimplemented feature.

### Comparison to Verus

| Aspect | Verus | Creusot |
|--------|-------|---------|
| Spec language | Verus annotations (Rust-like) | Pearlite (Rust-like) |
| SMT solver | Z3 only | CVC5, Z3, Alt-Ergo (portfolio) |
| Proof assistant fallback | None | Coq (via Why3) |
| FP theory | Basic (`vstd::float`) | Why3 `ieee_float` (comprehensive) |
| Maturity | 2023+ (OOPSLA 2023) | 2022+ (PhD thesis) |
| Community | Growing (Microsoft, academic) | Established (Inria, Toccata) |

### Applicability to rource-math

**Potentially addresses Gap G1 (floating-point) if Why3 integration exists:**

| Scenario | Feasibility | Note |
|----------|------------|------|
| Integer algebraic proofs | HIGH | Similar to Verus, overlapping capability |
| FP safety verification | MEDIUM | Requires f32→Float32 mapping in Creusot |
| FP error bound proofs | LOW | Why3 `ieee_float` has no VCFloat2-like automation |
| Multiple solver strategies | HIGH | CVC5 outperforms Z3 on FP queries (89-100% vs 78-85%) |

### Recommendation: **MONITOR**

Creusot offers two potential advantages over Verus:
1. **Portfolio SMT solving** (CVC5 outperforms Z3 on FP queries)
2. **Coq proof export** via Why3 (could integrate with our Coq corpus)

However, it largely overlaps with Verus for algebraic proofs, and its FP
capabilities via Why3 are undocumented. Monitor for:
- Explicit f32→Float32 Creusot integration
- Portfolio solving for FP-heavy verification conditions
- Coq proof export quality and usability

## Tool 4: hax (formerly hacspec v2)

### Profile

| Property | Value |
|----------|-------|
| **Repository** | [github.com/cryspen/hax](https://github.com/cryspen/hax) |
| **Maintainer** | Cryspen (Bhargavan et al.) |
| **Version** | 0.3.6 (January 2026) |
| **Commits** | 5,517+ |
| **Stars** | 369+ |
| **Backends** | F* (stable), Rocq (partial), Lean (active dev), SSProve, ProVerif |
| **Translation level** | THIR (Typed High-Level IR) |
| **Focus** | Cryptographic and security-critical Rust code |
| **Publication** | VSTTE 2024 paper; ePrint 2025/142 |

### What It Does

hax extracts Rust's THIR (Typed High-Level IR) to formal verification backends.
Its pipeline: Rust source → rustc THIR (JSON) → OCaml engine → F*/Rocq/Lean/etc.

### Floating-Point Support

**NOT SUPPORTED.** The hax paper explicitly states:

> "Literals include strings, integers, booleans, and floating point numbers
> (although **most of our backends do not have any support for floats**)."
> — Bhargavan et al., VSTTE 2024

The frontend AST recognizes f32/f64, but the proof backends cannot reason about
floating-point values. This is a fundamental limitation stemming from the backends'
focus on integer-based cryptographic code.

### Applicability to rource-math

**NOT APPLICABLE.** hax's design is optimized for:
- Cryptographic protocol verification (TLS, MLS)
- Integer-heavy computations (field arithmetic, hash functions)
- Security-critical code (not numerical/graphics code)

rource-math's f32-heavy types are outside hax's design scope.

### Recommendation: **NOT APPLICABLE**

hax is an excellent tool for cryptographic Rust verification but does not address
any of rource-math's capability gaps due to the lack of floating-point backend support.

## Comparative Summary

### Tool Capabilities Matrix

| Capability | Verus | Coq | Kani | Aeneas | Creusot | hax |
|-----------|-------|-----|------|--------|---------|-----|
| Algebraic proofs | **YES** | **YES** | Limited | YES | YES | YES |
| Universal quantification (∀) | **YES** | **YES** | No (bounded) | YES | YES | YES |
| Machine-checked proofs | Yes (Z3) | **YES** | Yes (SAT) | YES | Yes (SMT) | Yes |
| Floating-point | No | Via Flocq | **YES** | Unknown | Via Why3 | No |
| NaN/overflow detection | No | No | **YES** | No | Possibly | No |
| Spec-to-impl bridge | Manual | Manual | No | **YES** | Inline | YES |
| Coq proof output | No | **YES** | No | **YES** | Via Why3 | Partial |
| CI integration | Yes | Yes | **YES** | Possible | Possible | Possible |
| Bounded model checking | No | No | **YES** | No | No | No |

### Gap Coverage Matrix

| Gap | Verus | Coq | Kani | Aeneas | Creusot | hax |
|-----|-------|-----|------|--------|---------|-----|
| G1: Floating-point | — | Flocq (planned) | **Partial** (edge cases) | Unknown | **Possible** | — |
| G2: Spec-to-impl | — | — | — | **YES** | — | — |
| G3: Edge cases | — | — | **YES** | — | — | — |
| G4: Transcendentals | — | Flocq (sin/cos/tan) | — | — | — | — |

### Recommended Architecture (4-Layer)

```
┌─────────────────────────────────────────────────────────────────────┐
│                  rource-math Verification Architecture               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Layer 1: Algebraic Correctness (CURRENT)                           │
│  ├── Verus (266 proof functions)                                    │
│  │   └── Int specs → Z3 → algebraic properties                     │
│  └── Coq (1007 theorems)                                             │
│      └── R-based + Z-based → machine-checked proofs                │
│                                                                     │
│  Layer 2: Edge Case Safety (NEW — Kani)                             │
│  └── Kani (bounded model checker)                                   │
│      └── f32 bit-precise → NaN/overflow/infinity checking          │
│      └── 134 harnesses for FP-intensive operations                 │
│                                                                     │
│  Layer 3: Floating-Point Accuracy (PLANNED — Flocq)                │
│  └── Coq + Flocq + VCFloat2                                        │
│      └── IEEE 754 error bounds → "within N ULPs" proofs           │
│      └── ~46 operations (Phase FP-1)                               │
│                                                                     │
│  Layer 4: Spec-to-Impl Bridge (FUTURE — Aeneas, pending)           │
│  └── Aeneas functional translation                                  │
│      └── MIR → pure functional Coq/Lean → bridge to Layer 1       │
│      └── Blocked on: f32 support confirmation                      │
│                                                                     │
│  Testing Layer: Unit + Property + Chaos (CURRENT)                   │
│  └── cargo test (2700+ tests, 100% operation coverage)            │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## Action Items

### Immediate (This Session or Next)

1. **Kani evaluation**: Install Kani, write 3-5 proof harnesses for core operations
   (`length()`, `normalized()`, `dot()`, `determinant()`), assess scalability
2. **Aeneas f32 check**: Inspect Charon source for `FloatTy` handling; attempt
   minimal Vec2 extraction to confirm whether f32 fields are supported

### Near-Term (1-2 Months)

3. **Kani CI integration**: Add Kani harnesses to CI pipeline for ~40 FP operations
4. **Creusot FP investigation**: Check if Creusot maps f32 to Why3 Float32
5. **Flocq installation**: Begin Phase FP-1 (see FLOATING_POINT_VERIFICATION.md)

### Medium-Term (3-6 Months)

6. **Aeneas spec bridge**: If f32 works, extract rource-math types and bridge
   generated Coq output to existing R-based proofs
7. **Creusot evaluation**: If FP mapping exists, evaluate for FP-heavy operations
8. **Kani expansion**: Extend to all 114 FP operations

## Previously Investigated Tools

| Tool | Date | Finding | Document |
|------|------|---------|----------|
| **rocq-of-rust** | 2026-01-30 | NOT VIABLE — monadic embedding, f32 unsupported, structural admits | [VERIFICATION_COVERAGE.md](VERIFICATION_COVERAGE.md) |
| **Stainless** | 2026-01-30 | NOT APPLICABLE — Scala-only, no error bounds, Z3 weakest at FP | [FLOATING_POINT_VERIFICATION.md](FLOATING_POINT_VERIFICATION.md) |

## References

### Primary References (Tools Investigated)

1. Ho, S. & Protzenko, J. "Aeneas: Rust Verification by Functional Translation."
   ICFP 2022. ACM. [arXiv:2206.07185](https://arxiv.org/abs/2206.07185)

2. Ho, S., Fromherz, A., & Protzenko, J. "Sound Borrow-Checking for Rust via
   Symbolic Semantics." ICFP 2024. ACM.

3. Denis, X. "Creusot: A Foundry for the Deductive Verification of Rust Programs."
   Inria/CNRS. [hal-03737878](https://inria.hal.science/hal-03737878v1/document)

4. Bhargavan, K. et al. "hax: Verifying Security-Critical Rust Software using
   Multiple Provers." VSTTE 2024. [ePrint 2025/142](https://eprint.iacr.org/2025/142)

5. VanHattum, A. et al. "Verifying Dynamic Trait Objects in Rust." ICSE 2022.
   (Kani artifact)

6. CBMC: C Bounded Model Checker. [github.com/diffblue/cbmc](https://github.com/diffblue/cbmc)

### Additional References

7. Lattuada, A. et al. "Verus: Verifying Rust Programs using Linear Ghost Types."
   OOPSLA 2023. (Our current tool)

8. Boldo, S. & Melquiond, G. "Flocq: A Unified Library for Proving Floating-Point
   Algorithms in Coq." IEEE ARITH, 2011. (Planned tool)

9. Kellison, A. & Appel, A. "VCFloat2: Floating-point Error Analysis in Coq."
   CPP 2024. (Planned tool)

10. Friedlos, L. "Verifying Rust Programs Using Floating-Point Numbers and Bitwise
    Operations." ETH Zurich Master's Thesis. (Prusti FP investigation)

---

*Last updated: 2026-01-30*
*Tools investigated: 8 (Verus, Coq, Kani, Aeneas, Creusot, hax, rocq-of-rust, Stainless)*
*Recommendation: ADOPT Kani for edge-case safety; MONITOR Aeneas for spec-to-impl bridge*
*Current architecture: 2-layer (Verus + Coq); Target: 4-layer (+ Kani + Flocq)*
