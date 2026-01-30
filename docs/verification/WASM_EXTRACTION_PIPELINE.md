# Coq-to-WASM Extraction Pipeline

This document details the Coq-to-WASM extraction pipeline for rource-math, including
the tool ecosystem, CertiCoq-WASM assessment, ICC complexity framework, Coq-to-Rocq
migration strategy, and the full implementation roadmap.

For an overview of the complete verification effort (Verus + Coq), see
[FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md). For the comprehensive 9-path
landscape survey, see [CERTICOQ_WASM_ASSESSMENT.md](CERTICOQ_WASM_ASSESSMENT.md).

## Motivation

Verus excels at algebraic property verification but has limitations:
- No mature floating-point support
- No complexity bounds proofs (O(1), O(n))
- No verified compilation to WASM

To achieve **PEER REVIEWED PUBLISHED ACADEMIC** standards, we use a hybrid
architecture combining Verus with the Coq ecosystem.

## Tool Ecosystem

| Tool | Purpose | Maturity | Integration |
|------|---------|----------|-------------|
| **Verus** | Algebraic properties | Production | Active (327 proof fns) |
| **Coq** | Mathematical proofs, complexity | Production | Active (887 theorems) |
| **wasm_of_ocaml** | OCaml -> WASM compilation | Production (v6.2.0) | Active (Path 1, 6.8 KB lib) |
| **MetaCoq Verified Extraction** | Verified Coq -> OCaml | Research (PLDI'24) | Built from source (Path 2) |
| **CertiCoq-WASM** | Coq -> Verified WASM | Research (CPP 2025) | Deferred (Path 4, needs 8.20) |
| **coq-rust-extraction** | Coq -> Rust extraction | Early research (v0.1.1) | Deferred (needs 8.20+) |
| **WasmCert-Coq** | WASM formalization | Production | CertiCoq-WASM dependency |
| **ICC/Coq** | Complexity bounds | Research | Active (60 theorems) |
| **RefinedRust** | Unsafe code verification | Research (PLDI 2024) | Optional |

## Pipeline Status (Phase 3)

**Status**: Full landscape survey complete. 9 paths evaluated, 3 viable today.
Recommended pipeline: Standard Extraction + wasm_of_ocaml (production-ready).
Pipeline operational: All 8 types (Vec2-4, Mat3-4, Color, Rect + Utils) extracted to OCaml and compiled to WASM.

### CertiCoq-WASM Blockers (3 independent)

1. **R type incompatible with extraction** - Coq Reals are axiomatized, non-extractable
2. **Coq version mismatch** - CertiCoq-WASM requires Coq 8.20; project uses 8.18
3. **Purpose mismatch** - Existing specs are proofs; CertiCoq-WASM compiles programs

### Alternative Paths Identified (Full Survey)

| Path | Pipeline | Coq 8.18? | Verification | Status |
|------|----------|-----------|--------------|--------|
| **1 (Recommended)** | Coq -> OCaml -> wasm_of_ocaml -> WASM | **Yes** | Unverified extraction | Production |
| **2 (Academic)** | Coq -> MetaCoq -> OCaml -> wasm_of_ocaml -> WASM | **Yes** | Partially verified (PLDI'24) | Research |
| **4 (Strongest)** | Coq -> CertiCoq-WASM -> WASM | No (8.20) | Fully verified (CPP'25) | Deferred |

### Layered Verification Architecture

| Layer | File(s) | Type System | Purpose |
|-------|---------|-------------|---------|
| 1 (Abstract) | Vec2.v, Vec3.v, Vec4.v, Mat3.v, Mat4.v, Color.v, Rect.v, Utils.v + *_Proofs.v | R (reals) | Mathematical correctness |
| 2 (Computational) | Vec2-4_Compute.v, Mat3-4_Compute.v, Color_Compute.v, Rect_Compute.v, Utils_Compute.v | Z (integers) | Extractable operations (all 8 types) |
| 3 (Extraction) | RourceMath_Extract.v -> wasm_of_ocaml | OCaml -> WASM | Executable code (8 types, 160+ theorems) |

### Completed Early Tasks

- [x] CertiCoq-WASM feasibility assessment
- [x] Comprehensive 9-path landscape survey (see `CERTICOQ_WASM_ASSESSMENT.md`)
- [x] Vec2_Compute.v - Z-based computational bridge (25 theorems, 0 admits)
- [x] Vec2_Extract.v - Standard Coq extraction to OCaml demonstrated
- [x] Complexity.v warning fixes (11 notation-overridden warnings eliminated)
- [x] Layered verification architecture documented
- [x] wasm_of_ocaml identified as production-ready Path 1 (v6.2.0, Jane Street)
- [x] MetaCoq Verified Extraction identified as Path 2 (PLDI'24, Coq 8.18 compatible)

## Phase 3 Deliverables

| Deliverable | Status | Details |
|-------------|--------|---------|
| Vec3_Compute.v | Done | 31 theorems, Z-based, 1.6s compilation |
| Vec4_Compute.v | Done | 22 theorems, Z-based, 1.6s compilation |
| Mat3_Compute.v | Done | 25 theorems, Z-based, 3.0s compilation |
| Mat4_Compute.v | Done | 21 theorems + 16 local component lemmas, 5.5s compilation |
| Color_Compute.v | Done | 22 theorems, Z-based fixed-point (1000-scale) |
| Rect_Compute.v | Done | 22 theorems, Z-based, boolean predicates |
| Utils_Compute.v | Done | 14 theorems, zlerp/zclamp with computational examples |
| Vec3_Extract.v - Mat4_Extract.v | Done | Individual extraction modules |
| Color_Extract.v | Done | Extracts ZColor operations to OCaml |
| Rect_Extract.v | Done | Extracts ZRect operations to OCaml |
| RourceMath_Extract.v | Done | Unified extraction of all 8 types (160+ theorems) |
| test_extracted.ml | Done | OCaml test driver, all tests pass |
| wasm_of_ocaml pipeline | Done | Library: 6.8 KB WASM, test: 42.2 KB WASM |
| MetaCoq build from source | Done | All 8 components built, bypasses opam 503 |

## Path 1: wasm_of_ocaml (Production)

### Completed

- [x] Install wasm_of_ocaml toolchain (OCaml + Dune + Binaryen)
- [x] Compile vec2_extracted.ml -> WASM via wasm_of_ocaml
- [x] Extend computational bridge to all types (Vec3/4, Mat3/4, Color, Rect, Utils)

### Pending

- [ ] Benchmark extracted WASM vs wasm-pack WASM

## Path 2: MetaCoq Verified Extraction (Academic)

### Completed

- [x] Install MetaCoq for Coq 8.18 (built from source, all 8 components)
- [x] Install MetaCoq to Coq user-contrib (`make install`)
- [x] Test verified extraction on Vec2_Compute.v (9 operations erased successfully)

### Pending

- [ ] Document TCB reduction for academic publication

> **Note**: MetaCoq was successfully built from source by cloning the `coq-8.18`
> branch from `github.com/MetaCoq/metacoq` and building all 8 components. This
> bypasses the Coq opam repository HTTP 503 errors. The coq-equations dependency
> was pinned directly from GitHub source (`mattam82/Coq-Equations#v1.3-8.18`).
> Build order: utils -> common -> template-coq -> pcuic -> template-pcuic ->
> safechecker -> erasure -> erasure-plugin.

## Path 4: CertiCoq-WASM (Deferred)

### Pending (Deferred to Coq 8.20)

- [ ] Upgrade Coq to 8.20 and verify all proofs
- [ ] Install CertiCoq-WASM via opam
- [ ] Benchmark all three pipelines

## CertiCoq-WASM Details

[CertiCoq-WASM](https://github.com/womeier/certicoqwasm) provides verified compilation
from Coq to WebAssembly, presented at CPP 2025.

**Key Features:**
- Mechanized with respect to WasmCert-Coq formalization
- Produces WebAssembly programs with reasonable performance
- Verified against WebAssembly 1.0 standard
- Implements Coq's primitive integer operations as efficient WASM instructions

**Relevance to Rource:**
- Rource's WASM target (`rource-wasm`) could use verified compilation
- Critical math operations could be extracted via Coq -> CertiCoq-WASM
- End-to-end verification: Rust -> Coq proof -> Verified WASM

## Implicit Computational Complexity (ICC)

[ICC](https://en.wikipedia.org/wiki/Implicit_computational_complexity) characterizes
complexity classes through program structure rather than explicit resource counting.

### Coq-Based ICC Tools

| Tool | Capability | Reference |
|------|------------|-----------|
| Quasi-interpretations | Polynomial-time proofs | [Moyen et al.](https://lipn.fr/~moyen/walgo/papers/FHMMN-Coq.pdf) |
| Time Credits | O notation in Separation Logic | [Guéneau et al.](http://gallium.inria.fr/~agueneau/publis/gueneau-chargueraud-pottier-coq-bigO.pdf) |
| L calculus | Complexity mechanization | [ITP 2021 Cook-Levin](https://drops.dagstuhl.de/storage/00lipics/lipics-vol193-itp2021/LIPIcs.ITP.2021.20/LIPIcs.ITP.2021.20.pdf) |

### Application to rource-math

```
vec2_add: O(1)     --> Prove via ICC: constant-time structure
mat4_mul: O(1)     --> Prove via ICC: fixed 64 multiplications
label_collision: O(n) --> Prove via ICC: linear iteration
```

## Rust-to-Coq Bridge: coq-of-rust

[coq-of-rust](https://github.com/formal-land/coq-of-rust) translates Rust to Coq
for formal verification.

**Capabilities:**
- Works at THIR intermediate representation
- Supports 99% of Rust By Example code
- Enables Coq proofs about Rust semantics

**Integration Path:**
```bash
# Translate rource-math to Coq
coq-of-rust crates/rource-math/src/vec2.rs -o proofs/coq/vec2.v

# Prove complexity bounds in Coq
coqc proofs/coq/vec2_complexity.v

# Extract verified WASM via CertiCoq-WASM
certicoq -wasm proofs/coq/vec2.v -o verified_vec2.wasm
```

## Coq -> Rocq Rebranding (Critical Context)

The Coq Proof Assistant was officially renamed to **The Rocq Prover** with
version 9.0 (released March 2025). This rebranding affects the entire ecosystem:

### Key Changes

| Aspect | Coq (Legacy) | Rocq (Current) |
|--------|-------------|----------------|
| Name | The Coq Proof Assistant | The Rocq Prover |
| Versions | 8.x (up to 8.20) | 9.x (9.0, 9.1) |
| Opam package | `coq` | `rocq-prover` (= `rocq-core` + `rocq-stdlib`) |
| Opam repo | `coq.inria.fr/opam/released` | `rocq-prover.org/opam/released` |
| Standard library | `From Coq` | `From Stdlib` |
| MetaCoq | `MetaCoq/metacoq` | `MetaRocq/metarocq` |
| Build system | `coq_makefile` | `rocq makefile` (coq_makefile compat shim) |
| Binary | `coqc` | `rocq` (coqc compat shim via `coq-core`) |

### Impact on Rource

1. **Both opam repos return HTTP 503**: The old `coq.inria.fr/opam/released` and new
   `rocq-prover.org/opam/released` repos are periodically unavailable. The default
   `opam.ocaml.org` repo has core packages (`rocq-core`, `rocq-stdlib`, `coq`) but
   NOT MetaCoq/MetaRocq or coq-equations (beyond 1.3+8.18).

2. **Our Coq 8.18 is valid**: The `coq-core` compatibility shim exists up to v9.1.0,
   maintaining backward compatibility. Our proofs using `From Coq` namespace work with
   both Coq 8.18 and via the compatibility layer in Rocq 9.x.

3. **MetaRocq 1.4.1 exists for Rocq 9.1**: The latest MetaRocq (Dec 2024) targets
   Rocq 9.1, but requires `From MetaRocq` namespace (breaking change from `From MetaCoq`).

### Migration Strategy (Documented Decision)

| Timeline | Action | Rationale |
|----------|--------|-----------|
| **Current** | Stay on Coq 8.18 + MetaCoq (built from source) | Working, tested, 796 theorems compile |
| **Near-term** | Migrate to Rocq 9.0 when opam repos stabilize | `rocq-prover 9.0.0` available on opam.ocaml.org |
| **Medium-term** | Migrate to Rocq 9.1 + MetaRocq 1.4.1 | Latest, with full opam packages |

### Namespace Migration Required for Rocq 9.x

```coq
(* Coq 8.18 (current) *)
From Coq Require Import Reals.
From MetaCoq.ErasurePlugin Require Import Loader.

(* Rocq 9.x (future) *)
From Stdlib Require Import Reals.
From MetaRocq.ErasurePlugin Require Import Loader.
```

> **Rocq Migration Note**: The Coq Proof Assistant has been renamed to The Rocq
> Prover (v9.0+, March 2025). MetaCoq is now MetaRocq (v1.4.1 for Rocq 9.1).
> A future migration from Coq 8.18 to Rocq 9.x is planned. See migration
> strategy above for namespace changes.

## Phase 4: Publication (Q4 2026)

- [ ] Write academic paper on hybrid verification
- [ ] Submit to appropriate venue (CPP, PLDI, or POPL)
- [ ] Open-source all proof artifacts

## References

4. Meier, W., Pichon-Pharabod, J., Spitters, B. "CertiCoq-Wasm: A Verified WebAssembly
   Backend for CertiCoq." CPP 2025.
5. Forster, Y., Sozeau, M., Tabareau, N. "Verified Extraction from Coq to OCaml."
   PLDI 2024. Distinguished Paper Award.
6. Guéneau, A., Charguéraud, A., Pottier, F. "A Fistful of Dollars: Formalizing
   Asymptotic Complexity Claims via Deductive Program Verification." ESOP 2018.
7. Jung, R., et al. "RustBelt: Securing the Foundations of the Rust Programming
   Language." POPL 2018.
8. Sammler, M., et al. "RefinedRust: A Type System for High-Assurance Verification
   of Rust Programs." PLDI 2024.
9. wasm_of_ocaml (Jérôme Vouillon, Tarides): https://github.com/ocsigen/js_of_ocaml
10. MetaRocq Verified Extraction: https://github.com/MetaRocq/rocq-verified-extraction
11. coq-rust-extraction (AU-COBRA): https://github.com/AU-COBRA/coq-rust-extraction

---

*Last verified: 2026-01-29*

**Computational Bridge (Phase 3 + Phase 3 Continued + Phase 4):**
*8 Compute files: Vec2(38), Vec3(42), Vec4(33), Mat3(25), Mat4(21), Color(28), Rect(24), Utils(8) = 219 theorems over Z*
*8 Extract files + 1 unified extraction (RourceMath_Extract.v)*
*OCaml test driver: all tests pass*
*WASM pipeline: Library 6.8 KB, test driver 42.2 KB (via wasm_of_ocaml v6.2.0)*
*Architecture: Layered (R-abstract / Z-computational / extraction)*
*Landscape Survey: 9 Coq-to-WASM paths evaluated (see CERTICOQ_WASM_ASSESSMENT.md)*
*Recommended Path: Standard Extraction + wasm_of_ocaml (production-ready, Coq 8.18 compatible)*
*Alternative Path: MetaCoq Verified Extraction (PLDI'24, partially verified, Coq 8.18 compatible)*
*CertiCoq-WASM: Assessed, deferred to Coq 8.20 availability (strongest verification)*
*MetaCoq: Built from source, installed, verified extraction tested (9 ZVec2 ops erased)*
*Rocq Rebranding: Coq renamed to Rocq Prover (v9.0+, March 2025); migration planned*
*Status: Full pipeline operational, all 8 types extractable to WASM*
