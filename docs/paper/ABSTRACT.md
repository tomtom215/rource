# Paper Abstract

## Title

**Triple-Verified: Hybrid Formal Verification of a Production Rust Math Library
using Verus, Coq, and Kani**

## Abstract (247 words)

Graphics and visualization software relies on math libraries for correctness
of vector, matrix, color, and spatial operations, yet these libraries are
rarely formally verified. We present the first triple-verified Rust math
library, combining three complementary formal verification approaches to
achieve 2,968 machine-checked theorems and proof harnesses with zero admits
across 10 types and 256 public operations.

Our hybrid architecture pairs Verus (SMT-based algebraic proofs, 498 proof
functions), Coq (machine-checked proofs with R-based and Z-based layers,
2,198 theorems including 361 IEEE 754 error bounds via Flocq), and Kani
(CBMC-based bit-precise IEEE 754 model checking, 272 harnesses). This
combination addresses a fundamental tension: algebraic proofs cannot detect
floating-point edge cases, while bit-precise model checking cannot establish
mathematical properties.

We report several contributions: (1) a systematic methodology for combining
three verification tools on a single library; (2) a decomposition technique
for polynomial identities when SMT nonlinear arithmetic fails; (3) a layered
Coq architecture enabling >300x compilation speedup; (4) discovery of 4
concrete IEEE 754 bugs through Kani that algebraic proofs cannot detect;
(5) machine-checked floating-point error bounds for graphics operations; and
(6) an operational Coq-to-WebAssembly extraction pipeline producing a 6.8 KB
verified library.

The library achieves 85.5% formal verification coverage (219/256 operations),
with the remaining 14.5% blocked by transcendental functions or complex
geometry. All proofs are publicly available and reproducible.

## Keywords

Formal verification, Rust, Verus, Coq, Kani, IEEE 754, floating-point,
math library, WebAssembly, proof engineering

## Target Venues

- **Primary**: CPP 2027 (Certified Programs and Proofs)
- **Secondary**: ITP 2027 (Interactive Theorem Proving)
- **Stretch**: PLDI 2027 (Programming Language Design and Implementation)
