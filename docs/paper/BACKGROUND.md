# Section 2: Background

*Draft for CPP 2027 submission. Target length: ~2 pages.*

---

## 2.1 The Target: rource-math

rource-math is a production Rust math library providing 256 public operations
across 9 types for a graphics visualization application. The types span
four domains:

| Domain | Types | Key Operations |
|--------|-------|----------------|
| Geometry | Vec2, Vec3, Vec4 | add, dot, cross, normalize, lerp, project |
| Transforms | Mat3, Mat4 | multiply, transpose, inverse, determinant, transform |
| Color | Color | blend, lerp, luminance, HSL conversion, clamp |
| Spatial | Rect, Bounds | contains, intersects, union, intersection, expand |

All operations use IEEE 754 binary32 (f32) arithmetic. The library is
`#![no_std]`-compatible and ships as both a native Rust crate and a
WebAssembly module. All functions are pure (no side effects, no mutable
global state), making them well-suited for formal verification.

The library's MSRV (Minimum Supported Rust Version) is 1.93, and it
maintains 2876+ unit tests.

## 2.2 Verus

Verus [Lattuada et al., OOPSLA 2023] is a tool for verifying Rust programs
using SMT-based automated reasoning. Verus extends Rust with ghost code
annotations — preconditions (`requires`), postconditions (`ensures`), loop
invariants, and proof functions — that are erased at compile time. The
verification conditions are discharged by Z3.

For rource-math, Verus specifications model f32 fields as mathematical
integers (`int`), enabling Z3's `nonlinear_arith` tactic for polynomial
reasoning. This integer abstraction is sound for algebraic properties
(commutativity, associativity, distributivity) but does not model
floating-point rounding, overflow, or NaN propagation.

**Example** — Vec2 addition commutativity in Verus:
```rust
proof fn vec2_add_commutative(a: SpecVec2, b: SpecVec2)
    ensures spec_vec2_add(a, b) == spec_vec2_add(b, a)
{
    // Discharged automatically by Z3
}
```

Verus verification is fast (typically <1 second per proof function) but
limited by Z3's capabilities: nonlinear integer arithmetic with more than
~50 terms can cause timeouts, and no floating-point theory is available.

## 2.3 Coq

Coq [Coq Development Team, 2024] is an interactive theorem prover based on
the Calculus of Inductive Constructions. Unlike SMT-based tools, Coq proofs
are constructive proof terms checked by a small, trusted kernel. This
provides the strongest available guarantee of proof correctness.

For rource-math, we use Coq in three layers:

**Layer 1 (R-abstract)**: Specifications model f32 fields as mathematical
reals (R), using Coq's standard library real number theory. Properties
proven over R include commutativity, associativity, identity elements,
inverses, and domain-specific properties (e.g., Porter-Duff alpha blending
correctness). Proofs use tactics including `ring`, `field`, `lra`
(linear real arithmetic), and custom `Ltac` automation.

**Layer 2 (Z-computational)**: A parallel set of specifications models
fields as integers (Z) with scaled arithmetic (e.g., 1000x fixed-point
for color values). These specifications support Coq's extraction mechanism,
producing executable OCaml code.

**Layer 3 (FP error bounds)**: Using Flocq 4.1.3 [Boldo and Melquiond,
2011], we establish IEEE 754 error bounds for f32 operations. Flocq
provides a formalization of IEEE 754 arithmetic in Coq, including rounding
modes, error bounds for basic operations, and composition rules for
multi-operation error analysis.

## 2.4 Kani

Kani [Bae et al., ICSE-SEIP 2024] is a bit-level model checker for Rust
developed by Amazon Web Services. Kani translates Rust code (via the MIR
intermediate representation) to the CBMC bounded model checking framework,
which encodes the program as a Boolean satisfiability problem and checks
all executions within bounded domains.

For rource-math, Kani's critical advantage is that it operates directly
on the Rust implementation with f32 semantics. Unlike Verus or Coq, Kani
does not require a separate specification language or number type
abstraction. A Kani proof harness annotated with `#[kani::proof]`
executes the actual Rust function on symbolic f32 inputs and checks
assertions.

**Example** — Verifying Vec2::add produces no NaN:
```rust
#[kani::proof]
fn verify_vec2_add_commutative() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    kani::assume(ax.is_finite() && ay.is_finite());
    kani::assume(ax.abs() < 1e6 && ay.abs() < 1e6);
    let a = Vec2::new(ax, ay);
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    kani::assume(bx.is_finite() && by.is_finite());
    kani::assume(bx.abs() < 1e6 && by.abs() < 1e6);
    let b = Vec2::new(bx, by);
    let r1 = a + b;
    let r2 = b + a;
    assert!(r1.x == r2.x && r1.y == r2.y);
}
```

Kani's limitation is bounded domain: it verifies all inputs within the
specified bounds (e.g., `|x| < 1e6`) but cannot provide universal
quantification. This complements Coq's universal proofs over R.

## 2.5 IEEE 754 Binary32 and the Verification Gap

IEEE 754 binary32 (f32) represents numbers as a 1-bit sign, 8-bit exponent,
and 23-bit significand, providing approximately 7 decimal digits of
precision. Key properties relevant to verification:

| Property | Mathematical Reals | IEEE 754 f32 |
|----------|-------------------|--------------|
| Associativity of + | Always | Fails for most triple combinations |
| x + eps > x (eps > 0) | Always | Fails when eps < ULP(x) |
| x * 0 = 0 | Always | NaN * 0 = NaN |
| 1/0 | Undefined | +Infinity |
| sqrt(-1) | Undefined | NaN |

The unit in the last place (ULP) at magnitude M is approximately
`M * 2^{-23} ≈ M * 1.19e-7`. For a screen coordinate of 10,000, the ULP
is approximately 0.001 — meaning that geometric operations at this scale
have inherent precision limits.

This gap between mathematical reals and f32 is the central challenge our
triple-verification methodology addresses:
- **Verus/Coq over R/int**: Proves the property holds for ideal arithmetic
- **Coq + Flocq**: Bounds how far f32 results deviate from ideal
- **Kani over f32**: Verifies the f32 result is well-defined (finite, non-NaN)

## 2.6 Flocq: IEEE 754 Formalization in Coq

Flocq (Floats for Coq) [Boldo and Melquiond, 2011] provides a comprehensive
formalization of IEEE 754 floating-point arithmetic in Coq. Key components
used in our development:

- **Generic format**: Parameterized by precision and exponent range, instantiated
  to binary32 (24-bit significand, 8-bit exponent)
- **Rounding modes**: `round_mode` with `mode_NE` (round-to-nearest-even) as default
- **Error bounds**: `error_le_half_ulp` establishing that single-operation rounding
  error is bounded by half a ULP
- **Composition**: Rules for propagating error bounds through sequences of operations

Our 361 FP theorems build on Flocq's foundations to establish operation-specific
error bounds for rource-math's vector, matrix, color, and spatial operations.

---

*Word count: ~900 (target: ~1000-1200 for 2-page background section)*
*References: [Lattuada+23] Verus OOPSLA, [Coq Team 2024], [Bae+24] Kani ICSE,
[Boldo+11] Flocq, [IEEE 2019] IEEE 754-2019*
