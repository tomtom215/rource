# Section 1: Introduction

*Draft for CPP 2027 submission. Target length: ~2 pages (conference format).*

---

## Opening: The Problem

Graphics and visualization software depends fundamentally on the correctness
of its underlying math library. Vector operations, matrix transformations,
color blending, and spatial queries form the computational substrate upon
which every rendered frame is built. Yet these libraries are rarely
formally verified: developers rely on unit tests and manual review to
catch bugs in operations that execute millions of times per frame.

This testing-only approach has well-known limitations. Unit tests verify
sample inputs, not all inputs. Property-based tests improve coverage but
still operate within a probabilistic framework. Neither approach can detect
subtle floating-point edge cases that arise only for specific IEEE 754
binary32 representations — such as `lerp(f32::MAX, -f32::MAX, 0.0)`
producing NaN due to intermediate overflow, or a rectangle failing to
intersect itself when its width is smaller than the unit of least precision
at its x-coordinate.

## The Verification Challenge for Math Libraries

Formal verification of math libraries presents a fundamental tension.
*Algebraic verification tools* (SMT solvers, interactive theorem provers)
excel at proving mathematical properties — commutativity, associativity,
distributivity, identity elements — but they operate over idealized number
systems (reals, integers) that do not model IEEE 754 floating-point
semantics. *Bit-precise verification tools* (bounded model checkers)
operate directly on the implementation's floating-point representation but
cannot establish universal mathematical properties, only check bounded
input domains. Neither approach alone is sufficient for a production
floating-point math library.

This tension is not merely theoretical. In our development, we proved
`Vec2::add` is commutative in Coq over mathematical reals (R) and in Verus
over mathematical integers, yet Kani's bit-precise model checking revealed
that the same operation produces NaN when applied to extreme f32 values.
The algebraic proof is correct — but it does not guarantee the
implementation behaves as expected for all IEEE 754 inputs.

## Our Approach: Triple Verification

We address this tension through *triple verification*: applying three
complementary formal verification tools to the same production Rust math
library, each covering a different aspect of correctness.

1. **Verus** (Z3-based SMT verification): 498 proof functions verifying
   algebraic properties — vector space axioms, matrix ring structure,
   interpolation identities — over integer specifications. Verus operates
   within the Rust language itself, using ghost code annotations.

2. **Coq** (interactive theorem prover): 2,198 machine-checked theorems
   across three layers — 1,366 theorems proving mathematical correctness
   over real numbers (R), 471 theorems in a computational bridge over
   integers (Z) enabling verified extraction, and 361 theorems establishing
   IEEE 754 error bounds via Flocq. The Coq proofs have zero admits.

3. **Kani** (CBMC-based bounded model checker): 272 proof harnesses
   verifying bit-precise IEEE 754 f32 behavior — NaN-freedom, finiteness,
   overflow safety, and postconditions — directly on the Rust implementation
   without any specification abstraction.

Together, these three tools yield 2,968 machine-checked theorems and proof
harnesses with zero admits, covering 219 of 256 public operations (85.5%)
across 9 types: Vec2, Vec3, Vec4, Mat3, Mat4, Color, Rect, Bounds, and
utility functions.

## Contributions

We make the following contributions:

1. **A triple-verification methodology** combining SMT verification (Verus),
   interactive theorem proving (Coq), and bounded model checking (Kani) for
   a single production library. No prior work combines these three approaches.
   (Section 3)

2. **A lemma decomposition technique** for polynomial identities in Verus
   when Z3's `nonlinear_arith` tactic fails. We demonstrate this on 3x3 and
   4x4 matrix multiplication associativity, requiring 145-300+ helper lemma
   calls per proof. (Section 4.1)

3. **A layered Coq architecture** separating R-abstract specifications,
   Z-computational bridge, and OCaml/WASM extraction into independent
   compilation units, achieving >300x compilation speedup over monolithic
   development. (Section 4.2)

4. **Discovery of 4 IEEE 754 edge-case bugs** through Kani bounded model
   checking that algebraic proofs (Verus/Coq) fundamentally cannot detect,
   demonstrating that algebraic verification is necessary but not sufficient
   for floating-point code. (Section 4.3)

5. **361 machine-checked floating-point error bounds** via Coq + Flocq for
   graphics operations (vector, matrix, color, spatial), establishing formal
   error bounds for operations where algebraic proofs hold over R but
   deviate for f32. (Section 4.4)

6. **An operational Coq-to-WebAssembly extraction pipeline** producing a
   6.8 KB verified library from the Z-based computational bridge, with a
   9-path landscape survey of Coq-to-WASM compilation approaches. (Section 5)

## Paper Outline

Section 2 provides background on Verus, Coq, Kani, and IEEE 754 floating-point.
Section 3 presents the triple-verification architecture.
Section 4 details the verification methodology and key techniques.
Section 5 describes the extraction pipeline to WebAssembly.
Section 6 presents evaluation results.
Section 7 discusses threats to validity and limitations.
Section 8 compares with related work.
Section 9 concludes.

All proofs, harnesses, and benchmarks are publicly available and
reproducible from a clean build.

---

*Word count: ~680 (target: ~800-1000 for 2-page conference introduction)*
*References to add: Verus [Lattuada+23], Coq [Coq Team], Kani [Amazon], Flocq [Boldo+11],
IEEE 754 [IEEE 2019], CompCert [Leroy 2009], Fiat-Crypto [Erbsen+19]*
