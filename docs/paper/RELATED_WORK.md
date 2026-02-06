# Related Work Comparison

This document provides a systematic comparison of rource-math's formal
verification effort with related projects. All data points are sourced from
published papers or official project pages, with explicit notes where exact
counts are unavailable.

---

## Compact Comparison Matrix

| Project | Domain | Prover(s) | Theorem Count | FP? | Extraction? | Spec-to-Impl |
|---------|--------|-----------|---------------|-----|-------------|---------------|
| **rource-math** | Geometry/graphics | Verus+Coq+Kani | **2,968** (0 admits) | **Yes** (Flocq, 361 thms) | WASM (6.8 KB) | Triple: SMT+ITP+BMC |
| Fiat-Crypto | Crypto arithmetic | Coq | Large (80 prime fields) | No | C, Rust, Go, Zig | Verified partial eval |
| CompCert | C compiler | Coq | ~3,723 lemmas (v1.9.1) | Compilation only | OCaml | Simulation diagrams |
| mathlib4 | General mathematics | Lean 4 | **257,069** | No | No | Abstract definitions |
| LAProof | LA error bounds | Coq (Flocq) | ~200+ (est.) | **Yes** (IEEE 754) | C via VST | Flocq ftype + MathComp |
| VCFloat2 | FP error automation | Coq (Flocq) | 17 FPBench cases | **Yes** | No | Shallow-embedded FP |
| Stainless FP | Scala FP programs | SMT portfolio | 105 benchmarks, 2032 VCs | **Yes** (SMT FP) | No (in-place) | Contract-based |
| RustBelt | Rust type soundness | Coq (Iris) | Large (meta-theory) | No | No | Semantic types |
| RefinedRust | Unsafe Rust | Coq (Iris+Radium) | Vec: ~1,200 lines auto-Coq | No | MIR to Coq | Refinement types |
| hax/hacspec | Crypto protocols | F*, Coq, ProVerif | N/A (protocol-level) | Limited/No | Rust to F*/Coq | hacspec subset |

---

## Detailed Comparison

### 1. Fiat-Crypto (MIT CSAIL)

**Paper**: Erbsen et al., "Simple High-Level Code For Cryptographic Arithmetic," IEEE S&P 2019.
Also: CryptOpt, PLDI 2023 (Distinguished Paper).

- **Domain**: Verified big-integer modular field arithmetic for cryptography
- **Proof system**: Coq (Gallina + extraction)
- **Theorem count**: Exact count unavailable; development takes "about one hour to build in serial" with 3.5-4 GB RAM (S&P 2019, Section V). Targets 80 prime fields.
- **FP support**: No. Integer-only (big-integer modular arithmetic).
- **Extraction**: Coq extracts to OCaml/Haskell compiler binaries that generate C, Rust, Go, Zig, Java, and bedrock2 code. Deployed in BoringSSL (Chrome, Android).
- **Spec-to-impl**: Verified partial evaluation pipeline: high-level functional specs are transformed into low-level code via proven-correct partial evaluation.

**Key difference**: Fiat-Crypto targets cryptographic integer arithmetic with a code-generation pipeline; no floating-point, no geometric types. rource-math verifies a concrete Rust library with triple verification and IEEE 754 FP error bounds.

### 2. CompCert (Inria)

**Paper**: Leroy, "Formal verification of a realistic compiler," CACM 2009. 2021 ACM Software System Award.

- **Domain**: Verified optimizing C compiler
- **Proof system**: Coq
- **Theorem count**: ~3,723 lemmas across 143 theory files in v1.9.1 (Klein et al., "Challenges and Experiences in Managing Large-Scale Proofs")
- **LOC**: ~100,000 lines of Coq (6 person-years). Original: 42,000 lines (76% proof, 14% algorithms, 10% semantics).
- **FP support**: Compiles FP code preserving semantics, but does NOT prove FP error bounds.
- **Extraction**: Coq → OCaml produces the compiler executable.
- **Spec-to-impl**: Simulation diagrams between 20 compilation passes across 11 intermediate languages. ~90% of compiler algorithms proved correct.

**Key difference**: CompCert proves compilation preserves semantics; rource-math proves mathematical operations satisfy algebraic/geometric/FP properties. CompCert does not prove FP error bounds.

### 3. mathlib4 (Lean Community)

**Paper**: The mathlib community, "The Lean Mathematical Library," CPP 2020.

- **Domain**: General formalized mathematics
- **Proof system**: Lean 4
- **Theorem count**: **257,069 theorems**, 124,201 definitions (live count, Feb 2026)
- **LOC**: ~2 million lines of Lean code, 759 contributors
- **FP support**: No. Works with abstract `Real`, `Rat`, `Complex`.
- **Extraction**: Lean 4 compiles to C, but definitions not designed for numerical extraction.

**Key difference**: mathlib is vastly larger (257K vs 2,968 theorems) but operates in abstract mathematics with no connection to executable code or IEEE 754 semantics.

### 4. LAProof (Kellison, Appel, Tekriwal, Bindel)

**Paper**: "LAProof: A Library of Formal Proofs of Accuracy and Correctness for Linear Algebra Programs," IEEE ARITH 2023.

- **Domain**: Formal FP error bounds for BLAS-level linear algebra
- **Proof system**: Coq (Flocq + VCFloat + MathComp)
- **Theorem count**: Exact count unavailable; covers inner product, scaled matrix-vector multiply, matrix-matrix multiply, scaled vector/matrix addition.
- **FP support**: **Yes — core focus.** IEEE 754 backward/mixed error bounds via Flocq, accounting for underflow. "No assumptions except a low-level formal model of IEEE-754 arithmetic."
- **Connects to C via VST** (Verified Software Toolchain).

**Key difference**: LAProof provides deeper FP error analysis for a narrower set of BLAS operations. rource-math covers 10 geometric types with triple verification and broader property coverage. rource-math's FP layer (361 theorems) is inspired by LAProof's methodology.

### 5. VCFloat2 (Kellison & Appel)

**Paper**: "VCFloat2: Floating-Point Error Analysis in Coq," CPP 2024.

- **Domain**: Automated FP round-off error analysis framework
- **Proof system**: Coq (built on Flocq)
- **Benchmark count**: 17 FPBench benchmarks with competitive error bounds
- **FP support**: **Yes — core purpose.** Automates computation of sound FP error bounds.

**Key difference**: VCFloat2 is a proof automation tool, not a verified library. rource-math's FP layer (361 theorems) uses the same Flocq foundation but proves specific error bounds manually. VCFloat2 could potentially automate future rource-math FP proofs.

### 6. Stainless FP (Gilot, Bergstrom, Darulova)

**Paper**: "Verifying Floating-Point Programs in Stainless," arXiv:2601.14059, January 2026.

- **Domain**: FP verification for Scala
- **Proof system**: SMT-based (Z3, cvc5, Bitwuzla portfolio)
- **Benchmark count**: 105 benchmarks, 2,032 verification conditions
- **FP support**: **Yes — core purpose.** SMT-LIB FP theory.
- **Limitations**: No FP modulo, no transcendentals, Scala-only. Solver-dependent proofs (not machine-checked in a proof assistant).

**Key difference**: Stainless uses SMT solvers (solver-dependent, not machine-checked). rource-math's triple verification provides stronger guarantees: SMT + proof assistant + bounded model checker. rource-math's Coq FP layer (361 theorems) is fully machine-checked.

### 7. RustBelt (Jung, Jourdan, Krebbers, Dreyer)

**Paper**: "RustBelt: Securing the Foundations of the Rust Programming Language," POPL 2018.

- **Domain**: Semantic soundness of Rust type system
- **Proof system**: Coq (Iris higher-order concurrent separation logic)
- **Proved**: Fundamental theorem (well-typing implies safety) + verification of Arc, Rc, Cell, RefCell, Mutex, RwLock, mem::swap, thread::spawn, etc.
- **FP support**: No. Focuses on ownership, borrowing, concurrency.

**Key difference**: RustBelt proves language-level meta-theory; rource-math proves library-level functional correctness. The projects are complementary, operating at different levels of the verification stack.

### 8. RefinedRust (Gaher, Sammler, Jung, Krebbers, Dreyer)

**Paper**: "RefinedRust: A Type System for High-Assurance Verification of Rust Programs," PLDI 2024 (Distinguished Artifact Award).

- **Domain**: Semi-automated foundational verification of safe and unsafe Rust
- **Proof system**: Coq (Iris + Lithium automation + Radium operational semantics)
- **Evaluated**: Verified Rust `Vec` implementation (120 lines Rust, 76 lines annotations, ~1,200 lines auto-generated Coq)
- **FP support**: No. Focuses on pointer-manipulating unsafe code.

**Key difference**: RefinedRust verifies pointer-manipulating unsafe code; rource-math verifies mathematical correctness of safe code with FP error bounds.

### 9. hax/hacspec (Cryspen)

**Paper**: Bhargavan et al., "hax: Verifying Security-Critical Rust Software Using Multiple Provers," VSTTE 2024.

- **Domain**: Cryptographic protocol verification
- **Proof system**: Multiple backends: F* (primary), Coq/Rocq, SSProve, ProVerif
- **FP support**: Limited/No. VSTTE 2024 paper: "most backends do not have any support for floats."

**Key difference**: hax targets security properties (secrecy, authentication), not mathematical correctness. No FP support. The multi-backend approach is similar in spirit to rource-math's triple verification.

---

## Key Differentiators of rource-math

1. **Triple verification architecture**: No other surveyed project simultaneously employs SMT verification (Verus/Z3), interactive theorem proving (Coq), AND bounded model checking (Kani/CBMC) on the same codebase.

2. **IEEE 754 FP error bounds in a geometry library**: LAProof and VCFloat2 provide FP verification for linear algebra, but neither targets concrete Rust implementations of geometric/graphics types.

3. **Concrete implementation verification**: Unlike mathlib4 (abstract math) or RustBelt (type system meta-theory), rource-math verifies properties of a shipped Rust library.

4. **Zero admits at scale**: 2,968 machine-checked theorems/harnesses across four verification systems, all with zero admits.

5. **Multi-domain property coverage**: Algebraic, geometric, semantic, AND floating-point error properties — all verified for the same types.

---

## Note on Missing Counts

For Fiat-Crypto, LAProof, VCFloat2, RustBelt, and RefinedRust, exact theorem
counts were not available from published papers. These could be obtained by
cloning repositories and running `coqwc`/`grep -c`, or by contacting authors.

---

*All citations verified via published papers or official project pages*
*Research conducted: 2026-02-06*
