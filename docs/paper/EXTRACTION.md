# Section 5: Verified Extraction to WebAssembly

*Draft for CPP 2027 submission. Target length: ~1.5 pages.*

---

## 5.1 Pipeline Overview

We implemented an end-to-end pipeline from Coq specifications to a
deployable WebAssembly library:

```
Coq (Z-based specs)  →  Standard Extraction  →  OCaml source
                                                      ↓
                                              wasm_of_ocaml v6.2.0
                                                      ↓
                                              WebAssembly (6.8 KB)
```

The pipeline extracts all 8 primary types (Vec2-4, Mat3-4, Color, Rect,
Bounds) plus utility functions from the Z-based computational bridge
(Layer 2), producing executable integer-arithmetic implementations.

## 5.2 The Z-Based Computational Bridge

Standard Coq extraction cannot handle R (real numbers) — they extract to
an abstract OCaml type with no computational content. The Z-based
computational bridge solves this by providing integer implementations
of all operations:

```coq
(* R-based (Layer 1): mathematical, not extractable *)
Definition vec2_add (a b : Vec2) : Vec2 :=
  mk_vec2 (vx a + vx b) (vy a + vy b).

(* Z-based (Layer 2): integer, extractable *)
Definition zvec2_add (a b : ZVec2) : ZVec2 :=
  mk_zvec2 (zvx a + zvx b) (zvy a + zvy b).
```

For operations involving division or fractional results (e.g., color
normalization, interpolation), the Z-based layer uses scaled fixed-point
arithmetic:

```coq
(* Color uses 1000-scale fixed-point *)
Definition zcolor_luminance (c : ZColor) : Z :=
  (2126 * zcr c + 7152 * zcg c + 722 * zcb c) / 10000.
```

The 471 Z-based theorems verify that the integer implementations preserve
the essential properties of their R-based counterparts.

## 5.3 Extraction to OCaml

The extraction file `RourceMath_Extract.v` produces OCaml source:

```coq
Require Import RourceMath.Vec2_Compute.
Require Import RourceMath.Color_Compute.
(* ... all _Compute modules ... *)

Extraction Language OCaml.
Extraction "rource_math_extracted" zvec2_add zvec2_sub zvec2_scale ...
```

The extracted OCaml file (`rource_math_extracted.ml`) contains pure
functions operating on OCaml integers. A test driver
(`test_extracted.ml`) validates the extracted code against expected outputs.

## 5.4 OCaml to WebAssembly

We compile the extracted OCaml to WebAssembly using `wasm_of_ocaml` v6.2.0
(the WebAssembly variant of `js_of_ocaml`):

| Stage | Input | Output | Size |
|-------|-------|--------|------|
| Extraction | Coq Z-based specs | `rource_math_extracted.ml` | OCaml source |
| OCaml compilation | `.ml` → bytecode | `.byte` | ~200 KB |
| WASM compilation | `.byte` → `.wasm` | `rource_math_lib.wasm` | **6.8 KB** |
| Test compilation | test driver `.ml` | `test_extracted.wasm` | 42.2 KB |

The 6.8 KB WASM library is remarkably compact — smaller than many
JavaScript utility libraries — because it contains only integer arithmetic
operations with no runtime dependencies.

## 5.5 Landscape Survey

We surveyed 9 possible paths from Coq to WebAssembly:

| Path | Maturity | Verified? | Coq Version | Viable? |
|------|----------|-----------|-------------|---------|
| 1. Standard Extraction → OCaml → wasm_of_ocaml | Production | No | 8.18 | **Yes (adopted)** |
| 2. MetaCoq Verified Extraction → wasm_of_ocaml | Research | Partially | 8.18 | **Yes (tested)** |
| 3. CertiCoq → WASM (direct) | Research | Yes | 8.20+ | No (version incompatible) |
| 4. Standard Extraction → C → Emscripten | Hacky | No | 8.18 | Feasible but fragile |
| 5. Extraction → Haskell → GHCJS | Abandoned | No | 8.18 | No (GHCJS unmaintained) |
| 6. Extraction → OCaml → js_of_ocaml | Production | No | 8.18 | JS only, not WASM |
| 7. Extraction → Scheme → Chez → WASM | Experimental | No | 8.18 | No (no WASM backend) |
| 8. Manual WASM rewrite | — | No | — | Defeats purpose |
| 9. CertiCoq-WASM (CPP 2025) | New | Yes | 8.20+ | Future (version bump needed) |

We adopted Path 1 (production-ready) and tested Path 2 (MetaCoq) on a
subset (9 ZVec2 operations). Path 9 (CertiCoq-WASM) is the most promising
future path for fully verified extraction but requires migrating to Coq 8.20+.

## 5.6 Trust Boundaries

| Component | Trust Level | Notes |
|-----------|-------------|-------|
| Coq Z-based proofs | Machine-checked (kernel) | Zero admits |
| Standard Extraction | Trusted (unverified) | 20+ year track record (CompCert, Fiat-Crypto) |
| OCaml compiler | Trusted (partially verified by CompCert) | Standard toolchain |
| wasm_of_ocaml | Trusted (unverified) | v6.2.0, actively maintained |
| WASM runtime | Trusted (browser engines) | Sandboxed execution |

The weakest link is standard Coq extraction, which is known to be unverified.
MetaCoq Verified Extraction (Sozeau et al., PLDI 2024) can partially address
this gap, and we have demonstrated feasibility on a subset of our types.

---

*Word count: ~750 (target: ~800-1000 for 1.5-page extraction section)*
*Figures needed: Pipeline diagram, WASM size comparison chart*
