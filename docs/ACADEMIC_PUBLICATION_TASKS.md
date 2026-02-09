# Academic Publication Task Breakdown

This document details every task required to close the gaps between rource-math's
current state ("strong engineering") and indisputable academic publication quality
suitable for CPP/ITP (realistic) or PLDI/POPL/CAV (stretch) venues.

**Ground rules**: Every task below respects the mandatory standards from CLAUDE.md:
zero admits, exact measurements, never approximate, never guess, benchmarks before
and after, all tests passing, clippy clean, documentation consistent.

---

## Table of Contents

1. [Gap Analysis Summary](#gap-analysis-summary)
2. [Gap 1: Specification-to-Implementation Correspondence](#gap-1-specification-to-implementation-correspondence)
3. [Gap 2: Paper Draft](#gap-2-paper-draft)
4. [Gap 3: Documentation Count Drift](#gap-3-documentation-count-drift)
5. [Gap 4: Contribution Framing](#gap-4-contribution-framing)
6. [Gap 5: WASM Extraction Benchmarks](#gap-5-wasm-extraction-benchmarks)
7. [Gap 6: Mutation Testing](#gap-6-mutation-testing)
8. [Gap 7: Related Work Comparison](#gap-7-related-work-comparison)
9. [Supporting Tasks](#supporting-tasks)
10. [Dependency Graph](#dependency-graph)
11. [Effort Summary](#effort-summary)
12. [Risk Assessment](#risk-assessment)

---

## Gap Analysis Summary

| # | Gap | Severity | Current State | Target State | Effort |
|---|-----|----------|---------------|--------------|--------|
| 1 | Spec-to-impl correspondence | CRITICAL | Manual, trusted | Honest framing + systematic audit | HIGH |
| 2 | No paper draft | CRITICAL | Zero pages | Full paper (16-20 pages) | VERY HIGH |
| 3 | Documentation count drift | CRITICAL | **DONE** (T1) | Automated, CI-enforced | — |
| 4 | Contribution framing | IMPORTANT | Implicit in docs | Explicit generalizable insights | MEDIUM |
| 5 | WASM extraction benchmarks | IMPORTANT | Pipeline works, no perf data | Quantified comparison | MEDIUM |
| 6 | Mutation testing | IMPORTANT | Zero mutation scores | Measured per-crate scores | MEDIUM |
| 7 | Related work comparison | IMPORTANT | References listed, no analysis | Systematic comparison table | MEDIUM |

---

## Gap 1: Specification-to-Implementation Correspondence

### Problem Statement

Our Coq proofs verify `Record Vec2 := { vx: R; vy: R }` but Rust uses
`pub struct Vec2 { pub x: f32, pub y: f32 }`. The correspondence between
these two representations is manual and trusted. Academic reviewers at
CPP/PLDI **will** ask about this gap.

### Strategy: Honest Framing + Systematic Audit

We cannot fully close this gap with current tooling (see VERIFICATION_COVERAGE.md
rocq-of-rust investigation: monadic embedding, `UnsupportedLiteral` for f32,
structural `Admitted` axioms). Instead, we:

1. **Honestly frame** the gap as a documented limitation with systematic mitigations
2. **Systematically audit** specification-implementation correspondence
3. **Monitor** Aeneas as the most promising future path

### Tasks

#### T1.1: Create Specification Correspondence Audit Document
**Effort**: 4-6 hours | **Priority**: HIGH | **Depends on**: Nothing

Create `docs/verification/SPEC_IMPL_CORRESPONDENCE.md` containing:

- [ ] **Per-function correspondence table**: For each of the 219 verified operations,
  document the Rust function signature, the Coq specification, and note whether
  the translation is: (a) structurally identical, (b) semantically equivalent
  with documented differences, or (c) requires careful attention
- [ ] **Translation methodology section**: Describe the systematic process used
  to translate Rust implementations to Coq specifications
- [ ] **Floating-point modeling section**: Document exactly how `f32` maps to `R`
  (Coq reals) and `Z` (integers), including what properties are preserved and
  what is lost
- [ ] **Kani as runtime bridge section**: Explain how Kani's bit-precise IEEE 754
  verification at the f32 level partially bridges the gap between Coq's real-number
  model and actual floating-point behavior (272 harnesses covering NaN-freedom,
  finiteness, overflow safety)
- [ ] **FP error bounds section**: Document how the 361 Flocq-based Coq theorems
  quantify the gap between real-number and IEEE 754 binary32 arithmetic

**Acceptance criteria**: Document exists, covers all 219 operations, passes
review for accuracy against actual Coq and Rust source.

#### T1.2: Audit 10 Representative Operations End-to-End
**Effort**: 3-4 hours | **Priority**: HIGH | **Depends on**: T1.1

Select 10 operations spanning different types and complexity levels:
1. `Vec2::add` — trivial structural match
2. `Vec3::cross` — multi-component formula
3. `Mat4::determinant` — complex formula (cofactor expansion)
4. `Color::blend_over` — domain-specific (alpha blending)
5. `Rect::intersects` — boolean predicate with floating-point comparison
6. `Bounds::union` — conditional logic (min/max)
7. `Utils::lerp` — parameterized (t ∈ [0,1])
8. `Mat3::inverse` — partial function (returns Option)
9. `Vec2::lerp` with Kani harness — shows triple-verification chain
10. `Color::luminance` — weighted sum with FP considerations

For each:
- [ ] Copy exact Rust source code
- [ ] Copy exact Coq specification
- [ ] Write line-by-line correspondence proof (informal but rigorous)
- [ ] Note any semantic gap and how it is mitigated
- [ ] Reference relevant Kani harness and FP error bound theorem

**Acceptance criteria**: 10 audits complete, each showing exact Rust↔Coq mapping,
all gaps documented with mitigation strategy.

#### T1.3: Aeneas Feasibility Investigation
**Effort**: 4-6 hours | **Priority**: MEDIUM | **Depends on**: Nothing

Investigate Aeneas (Inria, ICFP 2022) for machine-generated spec-to-impl bridge:
- [ ] Install Aeneas from source (follow https://github.com/AeneasVerif/aeneas)
- [ ] Test on a minimal Vec2 subset (same 10 functions as rocq-of-rust test)
- [ ] Evaluate: Does Aeneas produce **pure functional** output (not monadic)?
- [ ] Evaluate: Does Aeneas handle f32 fields?
- [ ] Evaluate: Can Aeneas output be compiled with Coq 8.18?
- [ ] Evaluate: Could Aeneas output be bridged to our existing algebraic specs?
- [ ] Document findings in `docs/verification/AENEAS_ASSESSMENT.md`

**Acceptance criteria**: Assessment document exists with concrete test results
(not speculation). If Aeneas works, include reproduction steps. If it doesn't,
document exactly why with error messages.

#### T1.4: Write "Threats to Validity" Section for Paper
**Effort**: 2-3 hours | **Priority**: HIGH | **Depends on**: T1.1, T1.2

Draft the threats-to-validity section covering:
- [ ] **Specification correctness**: Manual specs could contain errors; mitigated
  by dual verification (Verus cross-checks Coq), systematic methodology, and
  100% unit test coverage of runtime behavior
- [ ] **Real↔float gap**: Coq proves over R, Rust computes over f32; mitigated by
  Kani (272 harnesses at bit-level) and Flocq (361 FP error bound theorems)
- [ ] **Extraction trust**: Standard Coq extraction is unverified; mitigated by
  MetaCoq verified extraction (tested, 9 ops) and runtime validation
- [ ] **Coverage limitations**: 37/256 operations unverified (14.5%); 10 are
  transcendental-blocked, 7 are batch (trivially follow from single-op proofs)

**Acceptance criteria**: Section written, each threat paired with specific mitigation,
no hand-waving or vague claims.

---

## Gap 2: Paper Draft

### Problem Statement

Zero pages of actual paper exist. A CPP submission requires 16-20 pages following
ACM SIGPLAN format. The paper must be self-contained, rigorously structured, and
withstand peer review.

### Strategy: Incremental Section-by-Section Writing

Write each section as an independent deliverable, then integrate. This allows
parallel work and independent review.

### Tasks

#### T2.1: Write Paper Abstract (250 words)
**Effort**: 2-3 hours | **Priority**: CRITICAL | **Depends on**: T1.1

Draft the abstract covering:
- [ ] **Problem**: Production graphics/visualization code lacks formal verification;
  floating-point math libraries are trusted, not proven
- [ ] **Approach**: Hybrid triple-verification architecture combining Verus (SMT),
  Coq (machine-checked proofs), and Kani (bounded model checking) with a
  Coq-to-WASM extraction pipeline
- [ ] **Results**: 2968 machine-checked theorems/harnesses, zero admits, 85.5%
  operation coverage across 10 types, 4 IEEE 754 edge-case bugs discovered,
  Coq-to-WASM extraction operational (6.8 KB)
- [ ] **Significance**: First triple-verified Rust math library; novel proof
  techniques (Requires-Axiom Decomposition); practical impact for production code

**Acceptance criteria**: 250 words, no vague claims, every number traceable to
source (verification-counts.json or doc-metrics.json).

#### T2.2: Write Introduction (2-3 pages)
**Effort**: 4-6 hours | **Priority**: HIGH | **Depends on**: T2.1, T4.1

Structure:
- [ ] **Motivation**: Why verify graphics math? (precision matters: rendering
  artifacts, physics simulation errors, color space bugs)
- [ ] **Challenge**: Floating-point semantics vs. algebraic properties; tool
  fragmentation in Rust verification landscape
- [ ] **Contribution summary**: Numbered list of contributions (see T4.1)
- [ ] **Paper outline**: Roadmap of remaining sections

**Acceptance criteria**: Self-contained introduction that motivates the work,
clearly states contributions, and gives reviewers a mental model.

#### T2.3: Write Background Section (2-3 pages)
**Effort**: 4-6 hours | **Priority**: HIGH | **Depends on**: Nothing

Cover:
- [ ] **Verus**: Brief introduction, SMT/Z3 backend, linear ghost types (cite
  Lattuada et al. OOPSLA 2023)
- [ ] **Coq**: Proof assistant overview, Calculus of Inductive Constructions,
  extraction mechanism
- [ ] **Kani**: CBMC-based bounded model checker, bit-precise IEEE 754 (cite
  Amazon Kani GitHub)
- [ ] **Flocq**: IEEE 754 formalization in Coq (cite Boldo & Melquiond 2011)
- [ ] **The rource-math library**: 10 types, 256 public operations, role in
  visualization pipeline

**Acceptance criteria**: Each tool described with enough detail for a reader
unfamiliar with any one tool to understand the paper. All claims cited.

#### T2.4: Write Verification Architecture Section (3-4 pages)
**Effort**: 6-8 hours | **Priority**: HIGH | **Depends on**: T1.1

This is the core technical contribution. Structure:
- [ ] **Overview diagram**: The hybrid architecture (Rust → Verus/Kani/Coq)
- [ ] **Layer 1: Verus (algebraic)**: Specification methodology, proof technique
  (integer model for f32), Requires-Axiom Decomposition for polynomial identities
- [ ] **Layer 2: Coq R-based (machine-checked)**: Specification design, proof
  structure, compilation optimization (>300x speedup from spec/proof separation)
- [ ] **Layer 3: Coq Z-based (extractable)**: Computational bridge design,
  integer encoding of floating-point operations, extraction to OCaml
- [ ] **Layer 4: Coq FP (error bounds)**: Flocq integration, IEEE 754 binary32
  error analysis, error composition for multi-operation chains
- [ ] **Layer 5: Kani (bit-precise)**: Harness design methodology, bounded domain
  selection, IEEE 754 edge case discovery
- [ ] **Layer 6: WASM pipeline**: Extraction → OCaml → wasm_of_ocaml, trust chain

**Acceptance criteria**: Architecture clearly presented with figures/diagrams,
proof methodology reproducible from description, design decisions justified.

#### T2.5: Write Evaluation Section (3-4 pages)
**Effort**: 6-8 hours | **Priority**: HIGH | **Depends on**: T5.1, T6.1, T7.1

This requires quantitative data. Structure:
- [ ] **RQ1: Coverage** — What fraction of the library is verified? (219/256 =
  85.5%, with breakdown by module and verification layer)
- [ ] **RQ2: Proof effort** — How much effort did verification require? (theorem
  counts per type, LOC for proofs vs. implementation, person-hours if measurable)
- [ ] **RQ3: Bug discovery** — Did verification find real bugs? (4 IEEE 754 edge
  cases from Kani, documented in VERIFICATION_COVERAGE.md)
- [ ] **RQ4: Extraction overhead** — How does extracted code compare to handwritten?
  (WASM benchmarks from T5.1)
- [ ] **RQ5: Cross-verification agreement** — Do Verus and Coq agree? (219 ops
  verified by both, no disagreements found)
- [ ] **Table**: Per-type verification metrics (from FORMAL_VERIFICATION.md table)
- [ ] **Table**: Comparison with related work (from T7.1)

**Acceptance criteria**: All research questions answered with data, tables formatted
for ACM SIGPLAN, no approximations ("~50%"), every claim has a citation or measurement.

#### T2.6: Write Related Work Section (2-3 pages)
**Effort**: 4-6 hours | **Priority**: HIGH | **Depends on**: T7.1

Structure:
- [ ] **Verified math libraries**: Fiat-Crypto, mathlib, CompCert
- [ ] **Rust verification**: Verus, Kani, Creusot, Aeneas, RustBelt, RefinedRust
- [ ] **Floating-point verification**: Flocq, VCFloat2, LAProof, Stainless FP
- [ ] **Verified extraction**: CertiCoq, MetaCoq verified extraction
- [ ] **Position**: How rource-math differs (triple verification, graphics domain,
  Coq-to-WASM pipeline)

**Acceptance criteria**: Covers all major related work, fair characterization of
each, clear differentiation of our contribution.

#### T2.7: Write Conclusion and Future Work (1-2 pages)
**Effort**: 2-3 hours | **Priority**: MEDIUM | **Depends on**: T2.4, T2.5

- [ ] **Summary**: Restate contributions with final numbers
- [ ] **Limitations**: Honest about spec-to-impl gap, transcendental blockers,
  extraction trust chain
- [ ] **Future work**: Aeneas for spec-to-impl, Rocq migration, CertiCoq-WASM
  when Coq 8.20 available, mutation testing, extended coverage

**Acceptance criteria**: Conclusion matches abstract, limitations are honest,
future work is concrete (not vague).

#### T2.8: Compile and Format Paper
**Effort**: 3-4 hours | **Priority**: MEDIUM | **Depends on**: T2.1-T2.7

- [ ] Set up LaTeX project with ACM SIGPLAN template (`acmart` class, `sigplan` option)
- [ ] Integrate all sections
- [ ] Create figures: architecture diagram, coverage chart, comparison table
- [ ] Verify page count (16-20 for CPP, 12 for workshop paper)
- [ ] Check all references compile with BibTeX
- [ ] Proofread for consistency

**Acceptance criteria**: PDF compiles, meets venue formatting requirements, all
figures render correctly, no broken references.

---

## Gap 3: Documentation Count Drift

### Status: DONE

Completed in T1 of this session:
- Fixed `update-doc-metrics.sh` hardcoded denominator (230 → dynamic extraction)
- Fixed 40+ stale counts across 15 files
- Added 170+ lines to `update-verification-counts.sh` with context-anchored patterns
- Added 17 new consistency checks
- Both `--check` modes pass

No further tasks required.

---

## Gap 4: Contribution Framing

### Problem Statement

The project documentation describes *what* was built but doesn't articulate
*why it matters* or *what generalizable insights* emerge. Academic papers need
clear, novel contributions that advance the field.

### Tasks

#### T4.1: Articulate Novel Contributions
**Effort**: 3-4 hours | **Priority**: HIGH | **Depends on**: T7.1

Identify and write up 4-6 contributions:

- [ ] **C1: Hybrid triple-verification architecture for Rust**: Novel combination
  of Verus (algebraic/SMT) + Coq (machine-checked) + Kani (bit-precise) achieving
  complementary coverage. No prior work combines all three for a single library.
  *Generalizable insight*: Different verification tools have complementary strengths;
  combining them achieves coverage no single tool can.

- [ ] **C2: Requires-Axiom Decomposition proof technique**: Novel Verus technique
  for polynomial identities where Z3's `nonlinear_arith` fails. Decomposes proofs
  into axiom-assuming steps.
  *Generalizable insight*: SMT solver limitations in nonlinear arithmetic can be
  systematically worked around without admitting axioms.

- [ ] **C3: Layered Coq specification architecture**: R-abstract → Z-computational
  → extraction pipeline with >300x compilation speedup from spec/proof separation.
  *Generalizable insight*: Separating specifications from proofs enables parallel
  compilation and independent evolution.

- [ ] **C4: IEEE 754 edge-case discovery via Kani**: 4 concrete bugs found through
  bounded model checking that algebraic proofs cannot detect (lerp overflow, project
  NaN, intersects ULP, center roundoff).
  *Generalizable insight*: Algebraic verification is necessary but not sufficient
  for floating-point code; bit-precise model checking finds real bugs.

- [ ] **C5: Quantified FP error bounds via Flocq**: 361 theorems establishing
  error bounds for single operations and n-operation compositions using IEEE 754
  binary32 formalization.
  *Generalizable insight*: Machine-checked FP error bounds provide stronger
  guarantees than informal error analysis.

- [ ] **C6: Coq-to-WASM verified extraction pipeline**: From Coq specifications
  through Z-based computational bridge to WASM (6.8 KB), with MetaCoq verified
  extraction tested.
  *Generalizable insight*: End-to-end verification from proof to deployment is
  achievable today using existing tools.

**Acceptance criteria**: Each contribution clearly stated with (a) what's novel,
(b) what generalizable insight it provides, and (c) evidence supporting the claim.

#### T4.2: Frame for Specific Venues
**Effort**: 2-3 hours | **Priority**: MEDIUM | **Depends on**: T4.1

Map contributions to venue expectations:

- [ ] **CPP (Certified Programs and Proofs)**: Emphasize C1 (hybrid architecture),
  C3 (layered Coq), C5 (Flocq error bounds), C6 (verified extraction). CPP
  values mechanized proofs and proof engineering insights.

- [ ] **ITP (Interactive Theorem Proving)**: Emphasize C2 (Requires-Axiom
  Decomposition), C3 (compilation optimization), C5 (Flocq integration).
  ITP values proof technique contributions.

- [ ] **PLDI (stretch)**: Emphasize C1 (practical tool combination), C4 (real
  bug discovery), C6 (end-to-end pipeline). PLDI values practical impact
  and tool building.

**Acceptance criteria**: For each venue, 1-page summary of which contributions
to emphasize and how to frame the introduction.

---

## Gap 5: WASM Extraction Benchmarks

### Problem Statement

The Coq-to-WASM extraction pipeline is operational (6.8 KB library, 42.2 KB test
driver via wasm_of_ocaml), but we have zero performance data comparing extracted
WASM to the production Rust WASM. Reviewers will ask: "What's the overhead?"

### Tasks

#### T5.1: Design and Run Extraction Benchmark Suite
**Effort**: 6-8 hours | **Priority**: HIGH | **Depends on**: Nothing

- [ ] **Select benchmark operations**: Choose 15-20 operations across types that
  exist in both extracted and production WASM:
  - Vec2: add, dot, cross, lerp, length_squared
  - Vec3: add, dot, cross, normalize
  - Mat3: mul, determinant, inverse
  - Mat4: mul, transform_point, orthographic
  - Color: blend_over, lerp, luminance
  - Rect: contains_point, intersects, union

- [ ] **Create benchmark harness for extracted WASM**:
  - Write JavaScript benchmark driver using `performance.now()`
  - Load extracted WASM module (6.8 KB)
  - Run each operation 10,000+ times
  - Record mean, median, P95, P99

- [ ] **Create benchmark harness for production WASM**:
  - Same JavaScript driver, same operations
  - Load production WASM module (built by wasm-pack)
  - Same iteration count and measurement methodology

- [ ] **Run benchmarks in controlled environment**:
  - Node.js (headless, no GC interference)
  - Chrome (browser context)
  - 3 independent runs minimum per operation
  - Record raw data in `docs/verification/WASM_BENCHMARKS.md`

- [ ] **Compute overhead ratios**:
  - For each operation: `overhead = extracted_time / production_time`
  - Compute geometric mean across all operations
  - Report with 95% confidence intervals

- [ ] **Analyze results**:
  - Which operations have highest overhead? Why?
  - Is the overhead acceptable for the verification guarantee?
  - Document any operations where extracted is faster (integer arithmetic)

**Acceptance criteria**: Raw benchmark data recorded with statistical rigor (10,000+
iterations, 3+ runs, 95% CI). Overhead ratios computed for all operations. Results
honestly reported regardless of whether they are favorable.

#### T5.2: Write WASM Benchmarks Section for Paper
**Effort**: 2-3 hours | **Priority**: MEDIUM | **Depends on**: T5.1

- [ ] Create table: operation, extracted time, production time, overhead ratio
- [ ] Create figure: overhead distribution (box plot or bar chart)
- [ ] Write analysis paragraph for paper's evaluation section
- [ ] Discuss trust-performance tradeoff

**Acceptance criteria**: Table and figure suitable for paper inclusion, analysis
is honest about overhead.

---

## Gap 6: Mutation Testing

### Problem Statement

We claim comprehensive testing (2900+ tests) but have never measured mutation
testing scores. Mutation testing reveals whether tests actually detect bugs.
Without it, high test counts may be misleading.

### Tasks

#### T6.1: Run Mutation Testing on rource-math — **COMPLETE** ✓
**Effort**: 4-6 hours | **Priority**: MEDIUM | **Depends on**: Nothing

- [x] **Install cargo-mutants**: `cargo install cargo-mutants` (v26.2.0)
- [x] **Run on rource-math**: Targeted runs on color.rs production code
- [x] **Record results**: 227 production mutants, 207 killed, 20 survived, 0 timeout
- [x] **Compute mutation score**: 91.2% raw, 100% adjusted (all 20 survived are equivalent)
- [x] **Analyze survivors**: All 20 categorized as equivalent mutants:
  - (a) 9 bit-packing: OR ≡ XOR for non-overlapping byte shifts
  - (a) 11 HSL boundary: algebraic identities at piecewise function boundaries
  - (b) Zero test gaps
  - (c) Zero specification gaps
- [ ] **Run on other crates** (time permitting): Not yet done

**Results**: Raw score 91.2% exceeds 80% target. Adjusted score 100% (all
survivors provably equivalent). Full analysis in `docs/paper/MUTATION_TESTING.md`.

#### T6.2: Write Mutation Testing Section for Paper — **COMPLETE** ✓
**Effort**: 1-2 hours | **Priority**: LOW | **Depends on**: T6.1

- [x] Report mutation score with methodology (Section 6.6 in EVALUATION.md)
- [x] Discuss equivalent mutants: 4 categories (bitwise, algebraic, continuity, EPSILON)
- [x] Full analysis in `docs/paper/MUTATION_TESTING.md` with per-mutant proofs

**Acceptance criteria**: Section written with exact scores, no approximations. ✓

---

## Gap 7: Related Work Comparison

### Problem Statement

The project lists references but doesn't systematically compare with related work.
Reviewers need to understand: "Why is this better/different/complementary?"

### Tasks

#### T7.1: Systematic Related Work Comparison Table
**Effort**: 6-8 hours | **Priority**: HIGH | **Depends on**: Nothing

Research and create a comparison along these dimensions:

| Project | Domain | Proof System | Theorem Count | FP Support | Extraction | Spec-Impl Gap |
|---------|--------|-------------|---------------|------------|------------|---------------|
| **rource-math** | Graphics/viz | Verus+Coq+Kani | 2968 | Flocq+Kani | WASM (6.8KB) | Manual+Kani |
| Fiat-Crypto | Cryptography | Coq | ~thousands | Integer-only | C/assembly | Machine-generated |
| CompCert | Compiler | Coq | ~100,000+ | Partial | CompCert C | Verified compiler |
| mathlib4 | General math | Lean 4 | ~1.9M | Partial | — | N/A (pure math) |
| hacspec | Crypto protocols | F*/Coq/Lean | varies | No | Rust | Machine-generated |
| Stainless FP | General | Stainless | ~500 benchmarks | Yes (SMT) | — | Source-level |
| LAProof | Linear algebra | Coq+VCFloat2 | ~200 | Yes (Flocq) | — | Manual |
| RustBelt | Rust soundness | Coq (Iris) | ~4000 | No | — | Semantic model |
| RefinedRust | Unsafe Rust | Coq | varies | No | — | Type system |

For each project:
- [ ] Verify theorem/proof count from published papers (not guesses)
- [ ] Document what domain they verify
- [ ] Note floating-point handling strategy
- [ ] Note extraction/compilation pipeline
- [ ] Note specification methodology (manual vs. machine-generated)

**Acceptance criteria**: Table populated with verified data from published papers.
Each entry has a citation. Our project honestly positioned relative to each.

#### T7.2: Write Positioning Narrative
**Effort**: 2-3 hours | **Priority**: MEDIUM | **Depends on**: T7.1

- [ ] **Differentiation from Fiat-Crypto**: Different domain (graphics vs. crypto),
  different FP strategy (they avoid FP entirely), different extraction target
  (WASM vs. C/assembly), similar rigor (zero admits)
- [ ] **Differentiation from CompCert**: We verify a library, not a compiler;
  they have full spec-impl correspondence; we have triple verification
- [ ] **Differentiation from mathlib**: They prove pure math; we prove properties
  of production code with floating-point considerations
- [ ] **Differentiation from Stainless FP**: They verify safety properties via
  SMT; we prove algebraic correctness + FP error bounds + bit-precise safety
- [ ] **Complementarity with LAProof**: They focus on linear algebra accuracy;
  we cover broader graphics domain; both use Flocq

**Acceptance criteria**: Each comparison is fair and honest. We don't overstate
our advantages or understate competitors' strengths.

---

## Supporting Tasks

### T8: Verify ~10 New Methods (from VERIFICATION_FUTURE_WORK.md)
**Effort**: 6-8 hours | **Priority**: MEDIUM | **Depends on**: Nothing

New Rust methods lack formal proofs:
- [ ] `Color::with_lightness` — Coq + Verus proof
- [ ] `Color::with_saturation` — Coq + Verus proof
- [ ] `Color::with_hue` — may be HSL-blocked (transcendental)
- [ ] `Color::rotate_hue` — may be HSL-blocked (transcendental)
- [ ] `Rect::min` / `Rect::max` — Coq + Verus + Kani proof
- [ ] Other new methods identified in coverage audit

**Acceptance criteria**: Each provable operation has Verus + Coq + Kani proofs.
Transcendental-blocked operations documented in VERIFICATION_FUTURE_WORK.md.
All tests pass, verification scripts updated.

**Impact on paper**: Increases coverage from 85.5% to ~88-90%.

### T9: Create Artifact for Reproducibility
**Effort**: 4-6 hours | **Priority**: HIGH | **Depends on**: T2.8

Academic papers need a reproducible artifact:
- [ ] Create `artifact/` directory with reproduction instructions
- [ ] Write `artifact/README.md` with step-by-step verification commands
- [ ] Create `artifact/Dockerfile` for containerized reproduction
- [ ] Verify all proofs compile from clean state in Docker
- [ ] Include `artifact/CLAIMS.md` mapping paper claims to commands
- [ ] Target ACM Artifact Evaluation badges: Available, Functional, Reusable

**Acceptance criteria**: A reviewer can clone the repo, run `docker build && docker run`,
and verify all 2968 theorems/harnesses with zero admits. All paper claims are
mapped to specific reproduction commands.

### T10: Update CLAUDE.md with Session Learnings
**Effort**: 1-2 hours | **Priority**: LOW | **Depends on**: All other tasks

- [ ] Document any new patterns discovered during paper writing
- [ ] Update Lessons Learned log
- [ ] Add any new automation triggers

---

## Dependency Graph

```
T1.1 (Spec-Impl Audit) ──┬── T1.2 (10 Operations)
                          ├── T1.4 (Threats to Validity)
                          └── T2.4 (Architecture Section)

T4.1 (Contributions) ─────── T4.2 (Venue Framing)
       │                         │
       └─── T2.2 (Introduction) ─┘

T7.1 (Related Work Table) ─── T7.2 (Positioning)
       │                         │
       └─── T2.6 (Related Work Section)

T5.1 (WASM Benchmarks) ───── T5.2 (Paper Section)
       │
       └─── T2.5 (Evaluation Section)

T6.1 (Mutation Testing) ──── T6.2 (Paper Section)
       │
       └─── T2.5 (Evaluation Section)

T2.1 (Abstract) ────────── depends on T1.1
T2.2 (Introduction) ────── depends on T2.1, T4.1
T2.3 (Background) ──────── no dependencies
T2.4 (Architecture) ────── depends on T1.1
T2.5 (Evaluation) ──────── depends on T5.1, T6.1, T7.1
T2.6 (Related Work) ────── depends on T7.1
T2.7 (Conclusion) ──────── depends on T2.4, T2.5
T2.8 (Compile Paper) ───── depends on T2.1-T2.7

T8 (New Methods) ─────────── no dependencies (parallel)
T9 (Artifact) ────────────── depends on T2.8
```

### Parallelization Opportunities

These task groups can run in parallel:

| Stream A (Spec-Impl) | Stream B (Paper Infra) | Stream C (Evaluation Data) | Stream D (Proofs) |
|-----------------------|------------------------|---------------------------|-------------------|
| T1.1 | T2.3 (Background) | T5.1 (WASM Benchmarks) | T8 (New Methods) |
| T1.2 | T4.1 (Contributions) | T6.1 (Mutation Testing) | |
| T1.3 | T7.1 (Related Work) | | |
| T1.4 | | | |

After parallel streams complete:
- T2.1 → T2.2 → T2.4 → T2.5 → T2.6 → T2.7 → T2.8 → T9

---

## Effort Summary

| Task | Effort (hours) | Priority | Category |
|------|---------------|----------|----------|
| T1.1 Spec-Impl Audit | 4-6 | HIGH | Gap 1 |
| T1.2 10 Operations | 3-4 | HIGH | Gap 1 |
| T1.3 Aeneas Investigation | 4-6 | MEDIUM | Gap 1 |
| T1.4 Threats to Validity | 2-3 | HIGH | Gap 1 |
| T2.1 Abstract | 2-3 | CRITICAL | Gap 2 |
| T2.2 Introduction | 4-6 | HIGH | Gap 2 |
| T2.3 Background | 4-6 | HIGH | Gap 2 |
| T2.4 Architecture | 6-8 | HIGH | Gap 2 |
| T2.5 Evaluation | 6-8 | HIGH | Gap 2 |
| T2.6 Related Work | 4-6 | HIGH | Gap 2 |
| T2.7 Conclusion | 2-3 | MEDIUM | Gap 2 |
| T2.8 Compile Paper | 3-4 | MEDIUM | Gap 2 |
| T4.1 Contributions | 3-4 | HIGH | Gap 4 |
| T4.2 Venue Framing | 2-3 | MEDIUM | Gap 4 |
| T5.1 WASM Benchmarks | 6-8 | HIGH | Gap 5 |
| T5.2 WASM Paper Section | 2-3 | MEDIUM | Gap 5 |
| T6.1 Mutation Testing | 4-6 | MEDIUM | Gap 6 |
| T6.2 Mutation Paper Section | 1-2 | LOW | Gap 6 |
| T7.1 Related Work Table | 6-8 | HIGH | Gap 7 |
| T7.2 Positioning | 2-3 | MEDIUM | Gap 7 |
| T8 New Methods | 6-8 | MEDIUM | Supporting |
| T9 Artifact | 4-6 | HIGH | Supporting |
| T10 CLAUDE.md Update | 1-2 | LOW | Supporting |
| **Total** | **82-114** | | |

### Critical Path

The minimum path to a submittable paper:
1. T1.1 (4-6h) → T2.1 (2-3h) → T2.2 (4-6h) → T2.4 (6-8h) → T2.5 (6-8h) → T2.7 (2-3h) → T2.8 (3-4h)
2. In parallel: T2.3 (4-6h), T4.1 (3-4h), T7.1 (6-8h), T5.1 (6-8h)

**Critical path length**: ~28-38 hours of focused work.
**Total with all tasks**: ~82-114 hours.

---

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Aeneas doesn't support f32 | HIGH | MEDIUM | Frame as future work; honest about gap |
| WASM extraction overhead is very high (>100x) | MEDIUM | MEDIUM | Report honestly; emphasize verification guarantee |
| Mutation testing reveals low scores | LOW | HIGH | Address gaps before publishing scores |
| CPP deadline missed | MEDIUM | HIGH | Target workshop paper at POPL/PLDI as fallback |
| Reviewer rejects due to spec-impl gap | MEDIUM | HIGH | T1.1-T1.4 provide strong mitigation narrative |
| Kani CBMC times out on new harnesses | LOW | LOW | Use bounded domains as established in 272 existing |

### Venue-Specific Risks

| Venue | Key Risk | Mitigation |
|-------|----------|------------|
| **CPP** | "Proofs are about a toy library" | Emphasize production use in rource (40,000+ LOC visualization tool) |
| **CPP** | "Spec-impl gap undermines claims" | T1.1-T1.4 provide detailed audit + Kani bridge |
| **ITP** | "No novel proof technique" | C2 (Requires-Axiom Decomposition) is genuinely novel |
| **PLDI** | "No performance evaluation" | T5.1 provides WASM benchmarks; T6.1 provides mutation scores |
| **POPL** | "Not theoretical enough" | Frame as empirical study with theoretical underpinning |

---

*Created: 2026-02-06*
*Based on academic readiness assessment from session rF6sR*
*All counts from metrics/verification-counts.json and metrics/doc-metrics.json*
