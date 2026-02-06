# Section 6: Evaluation

*Draft for CPP 2027 submission. Target length: ~2 pages.*

---

## 6.1 Research Questions

We evaluate the triple-verification approach along four dimensions:

- **RQ1**: What verification coverage does the approach achieve?
- **RQ2**: What is the verification effort (person-time, proof size)?
- **RQ3**: How do the three tools complement each other?
- **RQ4**: What are the performance characteristics of the verified library?

## 6.2 RQ1: Verification Coverage

### Operation Coverage

| Type | Total Ops | Verified Ops | Coverage |
|------|-----------|-------------|----------|
| Vec2 | 42 | 33 | 79% |
| Vec3 | 28 | 28 | 100% |
| Vec4 | 24 | 23 | 96% |
| Mat3 | 19 | 18 | 95% |
| Mat4 | 26 | 22 | 85% |
| Color | 38 | 33 | 87% |
| Rect | 50 | 33 | 66% |
| Bounds | 24 | 24 | 100% |
| Utils | 5 | 5 | 100% |
| **Total** | **256** | **219** | **85.5%** |

Three types achieve 100% verification coverage (Vec3, Bounds, Utils).
The lowest coverage is Rect (66%), due to 17 unverified operations
including iterator-based (`from_points`), complex geometry
(`transform_by_mat3/mat4`), and recently-added methods.

### Unverified Operations Breakdown

| Blocker | Count | Percentage |
|---------|-------|------------|
| Transcendental functions (sin, cos, atan2) | 10 | 27% |
| New methods (proofs pending) | ~10 | 27% |
| Batch operations (trivially follow) | 7 | 19% |
| FP predicates (Kani covers) | 3 | 8% |
| Complex geometry | 3 | 8% |
| HSL color conversion | 2 | 5% |
| Type conversions | 2 | 5% |

The primary blocker is transcendental functions (10 operations), which
cannot be verified by any of the three tools: Z3 has no theory for f32
transcendentals, Coq's Flocq does not model them, and Kani/CBMC
over-approximates them with nondeterministic ranges.

### Property Coverage

Beyond operation count, we measure the diversity of properties verified:

| Property Category | Verus | Coq | Kani | Example |
|-------------------|-------|-----|------|---------|
| Algebraic structure | 180+ | 400+ | 80+ | Commutativity, associativity, identity |
| Domain-specific | 100+ | 300+ | 50+ | Porter-Duff blending, projection |
| IEEE 754 safety | — | — | 272 | NaN-freedom, finiteness |
| FP error bounds | — | 361 | — | Operation error <= eps * result |
| Complexity bounds | — | 60 | — | ICC-checked complexity classes |
| Cross-type | — | 51 | — | Matrix-vector transform consistency |

## 6.3 RQ2: Verification Effort

### Proof Size

| Component | Files | Theorems/Harnesses | Lines of Proof |
|-----------|-------|-------------------|--------------------|
| Verus proofs | 11 | 498 | ~5,500 |
| Coq specs | 9 | 0 | ~2,500 |
| Coq R-proofs | 10 | 1,366 | ~12,000 |
| Coq Z-compute | 9 | 471 | ~4,500 |
| Coq FP bounds | 9 | 361 | ~3,500 |
| Kani harnesses | 9 | 272 | ~3,000 |
| **Total** | **57** | **2,968** | **~31,000** |

### Proof-to-Code Ratio

The Rust implementation (`crates/rource-math/src/`) is approximately 4,500
lines of code (including documentation). The proof development is ~31,000
lines, yielding a proof-to-code ratio of approximately **6.9:1**.

For comparison:
- CompCert: ~76% proof, 14% algorithms → proof-to-code ratio ~5.4:1
- seL4 (original): 200,000 lines proof / 8,700 lines C → ~23:1
- Fiat-Crypto: ratio not reported (one hour serial build time)

### Compilation Time

| Tool | Total Time | Parallelizable | Per-Proof Average |
|------|-----------|----------------|-------------------|
| Verus (11 files) | ~15 seconds | Yes (per file) | ~30ms |
| Coq (37 files) | ~45 seconds | Yes (per layer) | ~20ms |
| Kani (272 harnesses) | ~4 hours total | Yes (per harness) | ~50 seconds |

Kani is the bottleneck: each harness requires CBMC to bit-blast f32
operations into a SAT problem, which takes 30-120 seconds per harness.
In CI, we run a subset of representative harnesses (~30 minutes).

## 6.4 RQ3: Tool Complementarity

### Overlap Analysis

We measured how many properties are verified by exactly 1, 2, or 3 tools:

| Verification Depth | Properties | Example |
|--------------------|-----------|---------|
| All 3 tools | ~140 | Vec2::add commutativity (Verus + Coq + Kani) |
| 2 tools (Verus + Coq) | ~79 | Mat4::determinant identity (no Kani analog) |
| 2 tools (Coq + Kani) | ~30 | Complex formula correctness |
| 1 tool only (Coq) | ~150 | FP error bounds, complexity, cross-type |
| 1 tool only (Kani) | ~42 | IEEE 754 safety (NaN-freedom, finiteness) |
| 1 tool only (Verus) | ~15 | Properties with no Coq/Kani analog |

### Unique Contributions per Tool

| Discovery | Tool | Could Other Tools Find It? |
|-----------|------|----------------------------|
| lerp overflow (Bug #1) | Kani | No: Verus/Coq prove over R/int where overflow impossible |
| project denormalized (Bug #2) | Kani | No: denormals don't exist in R/int |
| ULP self-intersection (Bug #3) | Kani | No: x + w > x always in R for w > 0 |
| Center roundoff (Bug #4) | Kani | No: cancellation doesn't occur in R |
| Mat3 mul associativity | Verus | Yes: Coq also proves it (via `ring`) |
| FP error composition | Coq (Flocq) | No: requires interactive proof with real analysis |
| Complexity bounds (ICC) | Coq | No: type-based complexity not available in Verus/Kani |

### Key Finding

The 4 IEEE 754 bugs discovered by Kani are the strongest evidence for
the triple-verification approach: they are fundamentally invisible to
algebraic verification and can only be detected by bit-precise model
checking.

## 6.5 RQ4: Library Performance

The verified library maintains production-quality performance:

### Native Performance

| Benchmark | Time | Notes |
|-----------|------|-------|
| Vec2 add | ~0.3 ns | Compiled identically to unverified code |
| Mat4 multiply | ~8 ns | Same assembly output |
| Full frame (1000 objects) | ~18 µs | Within 20 µs budget |

Verification annotations (Verus ghost code, Kani harnesses) are
completely erased at compile time. The verified and unverified binaries
produce identical native code.

### WASM Extraction

| Metric | Value |
|--------|-------|
| Extracted WASM size | 6.8 KB |
| Production WASM size | ~1 MB (full application) |
| Extraction coverage | 8 types (all Z-based operations) |
| Runtime overhead | Not yet benchmarked (see Future Work) |

The extracted WASM library is operational: it accepts integer inputs,
performs computations using the Z-based definitions, and returns results.
The 6.8 KB size makes it suitable for embedding in web applications.

## 6.6 Mutation Testing (Preliminary)

We ran `cargo-mutants` on the rource-math crate to assess test suite
quality. Preliminary results:

| Metric | Value |
|--------|-------|
| Tool | cargo-mutants v26.2.0 |
| Mutants generated | 227+ (still running) |
| Caught (killed) | 218 |
| Missed (survived) | 9 |
| Timeout | 0 |
| **Mutation score** | **96.0%+** (218/227) |

The 9 surviving mutants are all in `Color::to_rgba8`, `to_argb8`, and
`to_abgr8`, where bitwise OR (`|`) was replaced with XOR (`^`). These
are bit-packing operations where the mutation produces different byte
ordering but identical numerical results for common input ranges, making
them difficult to detect without targeted bit-level tests.

---

*Word count: ~1050 (target: ~1200-1500 for 2-page evaluation section)*
*Tables/figures needed: Coverage bar chart, tool overlap Venn diagram,
compilation time breakdown, mutation score histogram*
*Note: Mutation testing results are preliminary — final numbers pending*
