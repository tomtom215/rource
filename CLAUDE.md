# CLAUDE.md - Rource Project Guide

This document provides context and guidance for Claude (AI assistant) when working on the Rource project.

---

## Table of Contents

1. [PEER REVIEWED PUBLISHED ACADEMIC Standard](#peer-reviewed-published-academic-standard)
2. [Performance Scale and Precision](#performance-scale-and-precision)
3. [Core Operating Principles](#core-operating-principles)
4. [Quality Domains](#quality-domains)
5. [Project Overview](#project-overview)
6. [Quick Start](#quick-start)
7. [Architecture](#architecture)
8. [Development Guidelines](#development-guidelines)
9. [Performance Optimization Standards](#performance-optimization-standards)
10. [UI/UX Excellence Standards](#uiux-excellence-standards)
11. [Testing & Quality Standards](#testing--quality-standards)
12. [Security Standards](#security-standards)
13. [Accessibility Standards](#accessibility-standards)
14. [Documentation Standards](#documentation-standards)
15. [Common Tasks](#common-tasks)
16. [CI/CD Pipeline](#cicd-pipeline)
17. [Debugging](#debugging)
18. [Dependencies Philosophy](#dependencies-philosophy)
19. [Git Workflow](#git-workflow)
20. [Troubleshooting](#troubleshooting)
21. [Reference Links](#reference-links)
22. [Roadmap Documents](#roadmap-documents)
23. [Session Best Practices](#session-best-practices)

---

## PEER REVIEWED PUBLISHED ACADEMIC Standard

### THE MANDATE

**This project targets PEER REVIEWED PUBLISHED ACADEMIC quality.** Every single contribution—every line of code, every UI element, every test, every document—MUST meet **publication-quality standards** suitable for top-tier venues (PLDI, POPL, CAV, CPP).

```
┌─────────────────────────────────────────────────────────────────────────────┐
│              PEER REVIEWED PUBLISHED ACADEMIC STANDARD                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  This standard applies to EVERY session, EVERY commit, EVERY change.        │
│                                                                             │
│  There are NO exceptions. There are NO shortcuts. There is NO "good enough."│
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │  EVERY claim must withstand peer review by domain experts.          │    │
│  │  EVERY proof must be machine-checked with zero admits.              │    │
│  │  EVERY measurement must be statistically rigorous.                  │    │
│  │  EVERY result must be reproducible by independent parties.          │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                                                             │
│  If it cannot be measured, it did not happen.                               │
│  If it was not tested, it does not work.                                    │
│  If it was not documented, it does not exist.                               │
│  If it was not benchmarked BEFORE and AFTER, it is speculation.             │
│  If it was not formally verified, it is not proven.                         │
│                                                                             │
│  The bar: "Would a reviewer at PLDI/POPL/CAV accept this?"                  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Target Ratings

Every domain must achieve **PEER REVIEWED PUBLISHED ACADEMIC** standard:

| Domain | Current | Target | Tracking Document |
|--------|---------|--------|-------------------|
| Technical Excellence | Expert | Academic | `docs/performance/CHRONOLOGY.md` |
| Performance Engineering | Expert+ | Academic | `docs/performance/BENCHMARKS.md` |
| **Formal Verification** | **Academic** | **Academic** | `docs/verification/FORMAL_VERIFICATION.md` |
| UI/UX Design | 3/10 | Expert+ | `docs/ux/MOBILE_UX_ROADMAP.md` |
| Testing Maturity | Senior+ | Expert+ | `docs/performance/FUTURE_WORK.md` |
| Security Posture | Senior | Expert+ | `docs/performance/FUTURE_WORK.md` |
| Accessibility | Not Rated | Expert+ | `docs/ux/MOBILE_UX_ROADMAP.md` |
| Operational Readiness | Senior+ | Expert+ | `docs/performance/FUTURE_WORK.md` |
| Documentation Quality | Expert | Academic | This document |

**Formal Verification Status (PEER REVIEWED PUBLISHED ACADEMIC):**
- **Verus**: 266 proof functions, 0 errors
- **Coq (R-based)**: 446 theorems, 0 admits, machine-checked (Vec2-4, Mat3-4, Color, Rect, Utils + Complexity)
- **Coq (Z-based)**: 235 theorems, 0 admits, machine-checked (extractable computational bridge, 8 types)
- **Kani (CBMC)**: 110 proof harnesses, 0 failures, bit-precise IEEE 754 f32 verification
- **Combined**: 1057 formally verified theorems/harnesses across 8 types

### The Non-Negotiable Rules

| Rule | Requirement | Consequence of Violation |
|------|-------------|--------------------------|
| **Never Assume** | Verify every claim with data | Work is invalid |
| **Never Guess** | Base all decisions on measurements | Work is invalid |
| **Never Skip Tests** | Run full test suite before claiming success | Work is invalid |
| **Never Ship Broken UX** | Mobile-first, touch-first, accessible | Work is invalid |
| **Never Commit Undocumented** | Every change documented with metrics | Work is invalid |
| **Never Ignore Warnings** | Zero clippy warnings, zero console errors | Work is invalid |
| **Never Approximate** | "~50%" is wrong; "52.5% (2.41µs → 1.15µs)" is correct | Work is invalid |

---

## Core Operating Principles

### The Standard

| Principle | Requirement |
|-----------|-------------|
| **Never Assume** | Verify every claim with data. If unsure, investigate first. |
| **Never Guess** | Base all decisions on measurements, not intuition. |
| **Always Test** | Run the full test suite before claiming success. |
| **Always Measure** | Use criterion benchmarks with statistical significance. |
| **Always Verify** | Confirm results are reproducible across runs. |
| **Always Validate** | Cross-check implementations against requirements. |
| **Always Document** | Every change needs before/after measurements in docs. |
| **Always Review** | Check mobile UX, accessibility, and user impact. |

### Precision Requirements

We operate at **nanosecond to picosecond precision** for performance and **pixel-perfect precision** for UI:

| Domain | Precision Level | Example |
|--------|-----------------|---------|
| **Performance** | Picoseconds-Nanoseconds | Draw call: 360 ps ± 6.8 ps |
| **Touch Targets** | Exact pixels | Minimum 44×44px (no exceptions) |
| **Typography** | Exact pixels | Minimum 12px body, 4.5:1 contrast |
| **Layout** | Percentage of viewport | Visualization: 85%+ during playback |
| **Animation** | Milliseconds | 16.67ms frame budget at 60 FPS |

### Anti-Patterns to Avoid

| Anti-Pattern | Why It's Wrong | Correct Approach |
|--------------|----------------|------------------|
| "This should be faster" | Speculation | Benchmark before and after |
| "~50% improvement" | Approximation | "52.5% improvement (2.41µs → 1.15µs)" |
| "Looks fine on my screen" | Single device | Test on mobile Safari, Chrome, Firefox |
| "Users will figure it out" | Assumption | Icons need labels, gestures need hints |
| "I'll document it later" | Never happens | Document as you implement |
| "The tests pass" | Insufficient | Also check mobile UX, accessibility |
| "It works on desktop" | Desktop bias | Mobile-first development required |
| **"Pre-existing issue"** | **Abdication of responsibility** | **Fix it NOW** |
| **"Unrelated to my changes"** | **Destroys trust and quality** | **You touched it, you own it** |

### CRITICAL: The "Pre-Existing Issue" Fallacy

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    **  ABSOLUTE PROHIBITION  **                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  NEVER dismiss ANY issue as "pre-existing" or "unrelated to my changes."   │
│                                                                             │
│  This behavior is ABSOLUTELY UNACCEPTABLE and represents:                   │
│                                                                             │
│  - A fundamental violation of Expert+ standards                             │
│  - An abdication of professional responsibility                             │
│  - A betrayal of trust with the project owner                               │
│  - A threat to the integrity of the entire codebase                         │
│  - Potential hidden bugs that will surface in production                    │
│                                                                             │
│  The correct response to ANY warning, error, or issue is:                   │
│                                                                             │
│  1. FIX IT IMMEDIATELY                                                      │
│  2. If you cannot fix it, DOCUMENT why and create a tracking issue          │
│  3. NEVER proceed with other work until the codebase is clean               │
│                                                                             │
│  Remember: This is a PORTFOLIO SHOWPIECE and PUBLIC WASM DEMO.              │
│  Every clippy warning, every test failure, every console error              │
│  reflects directly on the quality of the project and its author.            │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

**The Rule**: If you encounter ANY issue during your work session—whether you caused it or not—you are responsible for fixing it. There is no "not my problem." There is no "out of scope." If clippy reports 20 warnings, you fix 20 warnings. If tests fail, you fix the tests. Period.

**Why This Matters**:
1. **Hidden bugs accumulate**: "Pre-existing" issues often mask real bugs
2. **Trust erosion**: Dismissing issues signals you don't care about quality
3. **Technical debt compounds**: Every ignored warning makes the next one easier to ignore
4. **Portfolio damage**: A single clippy warning in a public demo undermines credibility
5. **Production risk**: Warnings today become crashes tomorrow

---

## Intellectual Honesty Standards

### The Honesty Mandate

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    ABSOLUTE INTELLECTUAL HONESTY                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  NEVER guess. NEVER assume. NEVER exaggerate. NEVER overstate.              │
│  NEVER skim. NEVER compromise. NEVER take shortcuts with truth.             │
│                                                                             │
│  Every claim must be:                                                       │
│    • VERIFIABLE - Can be independently reproduced                           │
│    • AUDITABLE - Evidence exists and is documented                          │
│    • PRECISE - Exact values, not approximations                             │
│    • HONEST - Acknowledges limitations and uncertainty                      │
│                                                                             │
│  When uncertain, say "I don't know" or "This needs verification."           │
│  When wrong, immediately correct and document the error.                    │
│  When results are inconclusive, say so explicitly.                          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### What Constitutes a Valid Performance Claim

| Claim Type | Required Evidence | Invalid Without |
|------------|-------------------|-----------------|
| **"X% faster"** | Criterion benchmark, 100+ samples, 95% CI, before/after | Statistical significance test |
| **"No regression"** | Same benchmark methodology, threshold-based pass/fail | Defined acceptance thresholds |
| **"Optimization"** | Algorithmic/data structure change + measured improvement | Actual code change that affects runtime |
| **"Improvement"** | Quantified metric with baseline comparison | Reproducible measurement |

### Invalid Performance Claims

The following are **NEVER** valid performance claims:

| Invalid Claim | Why It's Wrong | Correct Approach |
|---------------|----------------|------------------|
| "Module refactoring improved performance" | Module organization doesn't affect compiled binary | "Module refactoring improved maintainability; verified no regression" |
| "~X% improvement" | Approximation violates precision standards | "X.XX% improvement (before: Y, after: Z)" |
| "Should be faster" | Speculation, not measurement | Benchmark before claiming |
| "Feels faster" | Subjective, unmeasurable | Use objective metrics |
| "Minor improvement" | Vague, unquantified | Provide exact numbers |
| Timing variations without statistical analysis | Measurement requires rigor | Use criterion: 100+ samples, 95% CI, reproducible |

### Measurement Precision at Scale

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    PRECISION AT PICOSECOND SCALE                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  At our frame budget of 20µs (target: <10µs), EVERY PERCENT MATTERS:        │
│                                                                             │
│    • 10% of 20µs = 2µs = 6,000 CPU cycles = NOT NOISE                       │
│    • 5% of 20µs = 1µs = 3,000 CPU cycles = SIGNIFICANT                      │
│    • 1% of 20µs = 200ns = 600 CPU cycles = MEASURABLE                       │
│                                                                             │
│  We are measuring INDIVIDUAL CPU CLOCK CYCLES. There is no such thing       │
│  as "acceptable noise" at this precision level. Timing variations that      │
│  would be noise in millisecond-scale applications are REAL COSTS here.      │
│                                                                             │
│  Sources of variance (NOT noise - actual measurement considerations):       │
│    • CPU frequency scaling: Control with `cpupower frequency-set`           │
│    • Cache state: Warm up with 100+ samples before measuring                │
│    • System load: Use dedicated test environment, minimize processes        │
│    • Memory allocation: Pre-allocate, avoid measurement-time allocs         │
│    • Kernel scheduling: Use real-time priority, isolate CPU cores           │
│                                                                             │
│  To establish statistical confidence:                                       │
│    1. Use criterion with 100+ samples (statistical rigor)                   │
│    2. Verify 95% confidence intervals don't overlap                         │
│    3. Report exact values: "52.3% improvement" not "~50%"                   │
│    4. Run multiple independent benchmark sessions                           │
│    5. Control for variance sources listed above                             │
│                                                                             │
│  If criterion reports "No change" - report exactly that.                    │
│  If criterion reports a change - verify it's reproducible, then report it.  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Code Quality vs. Performance

**Code quality changes** (refactoring, module organization, documentation) should be:
- Documented as code quality improvements, NOT performance improvements
- Verified to cause no regression (threshold-based pass/fail)
- Not claimed as optimizations (the binary is identical)

**Performance changes** (algorithmic improvements, data structure changes) should be:
- Documented with criterion benchmarks (100+ samples, 95% CI)
- Include before/after measurements with exact values
- Calculate exact improvement percentages
- Verify statistical significance

### Self-Correction Protocol

When an error in reporting is discovered:

1. **Immediately acknowledge** the error explicitly
2. **Correct the documentation** with accurate information
3. **Explain** what was wrong and why
4. **Prevent recurrence** by strengthening standards if needed
5. **Do not minimize** or make excuses

Example of proper self-correction:
> "I incorrectly reported timing variations as performance improvements.
> Module refactoring does not affect compiled binary; observed timing
> differences were measurement artifacts within noise margin. The correct
> claim is: verified no regression against defined thresholds."

### Self-Improvement Protocol

```
┌─────────────────────────────────────────────────────────────────────────────┐
│          MANDATORY SELF-IMPROVEMENT (EVERY SESSION)                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  BEFORE ENDING ANY SESSION, Claude MUST:                                    │
│                                                                             │
│  1. REVIEW what was learned this session                                    │
│     └─ New tooling knowledge (installation, configuration, gotchas)         │
│     └─ Errors encountered and how they were resolved                        │
│     └─ Workarounds discovered for toolchain incompatibilities               │
│     └─ Performance insights or measurement techniques                       │
│                                                                             │
│  2. UPDATE CLAUDE.md if ANY of the following occurred:                      │
│     └─ A tool required non-obvious installation steps                       │
│     └─ A standard violation was discovered and corrected                    │
│     └─ A new best practice was established                                  │
│     └─ Session setup required manual intervention                           │
│     └─ CI failed for a preventable reason                                   │
│                                                                             │
│  3. UPDATE or CREATE scripts if:                                            │
│     └─ Manual tool installation was required                                │
│     └─ Environment configuration was needed                                 │
│     └─ A reproducibility issue was encountered                              │
│                                                                             │
│  4. ADD to Lessons Learned log (below) with:                                │
│     └─ Date and session ID                                                  │
│     └─ What happened, root cause, fix applied                               │
│     └─ How CLAUDE.md or scripts were updated                                │
│                                                                             │
│  This is NOT optional. Skipping self-improvement is a violation.            │
│  The goal: Each session leaves the project BETTER than it was found.        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### Self-Improvement Triggers

The following events MUST trigger a CLAUDE.md update:

| Trigger | Required Action |
|---------|-----------------|
| Tool installation required troubleshooting | Add to scripts/setup-formal-verification.sh |
| Toolchain version incompatibility | Document in CLAUDE.md and create workaround |
| CI failure that could have been prevented | Add to pre-commit checklist |
| Manual work that could be automated | Create or update script |
| New technique discovered | Document with examples |
| User had to ask for CLAUDE.md update | Add automatic trigger for similar situations |
| Standard violation identified | Add to Lessons Learned with prevention rule |

#### Lessons Learned Log

| Date | Session | Issue | Root Cause | Fix Applied | CLAUDE.md Updated |
|------|---------|-------|------------|-------------|-------------------|
| 2026-01-28 | - | Timing variations reported as perf improvements | Module refactoring doesn't affect binary | Added "Invalid Performance Claims" table | Yes |
| 2026-01-28 | - | "10% is noise" at picosecond scale | Wrong precision assumptions | Replaced with "Measurement Precision at Scale" | Yes |
| 2026-01-28 | - | Low coverage blamed on tarpaulin | Excuse instead of investigation | Added `--engine Llvm` requirement | Yes |
| 2026-01-28 | WBhqf | coq-of-rust incompatible with Rust 1.93 | Tool requires older nightly | Manual Coq specs; documented in FORMAL_VERIFICATION.md | Yes |
| 2026-01-28 | WBhqf | Windows CI benchmark timeout | Threshold too tight for CI variability | Increased threshold 100µs→150µs | Yes |
| 2026-01-28 | WBhqf | No automated Verus/Coq setup | Tools required manual installation | Created scripts/setup-formal-verification.sh | Yes |
| 2026-01-28 | SD81W | Coq installation via apt needs coq-theories | apt-get only installs coqc without theories | Use `apt-get install -y coq coq-theories` | Yes |
| 2026-01-28 | SD81W | Mat3/Mat4 Coq proofs follow Vec2/Vec3/Vec4 pattern | Manual Coq specs work well | Added Mat3.v, Mat4.v, Mat3_Proofs.v, Mat4_Proofs.v (44 new theorems) | Yes |
| 2026-01-28 | SD81W | Network issues can block apt-get | Transient DNS failures | Script should retry with exponential backoff | Yes |
| 2026-01-28 | 4sbzk | ICC complexity proofs simpler for fixed-size types | Operations on Vec2-4, Mat3-4 have constant cost regardless of input values | Created Complexity.v with 60 theorems proving O(1) for all operations | Yes |
| 2026-01-28 | 4sbzk | Coq lia tactic sufficient for O(1) bounds | Simple constant-cost proofs don't need ring/lra | Used `lia` for all complexity bounds; compilation under 1 second | Yes |
| 2026-01-29 | 4sbzk | Coq `f_equal` causes exponential blowup on large records | `f_equal` on 16-field Mat4 creates nested terms causing `lra`/`ring` to time out | Use `apply mat4_eq` instead of `f_equal`; processes fields independently | Yes |
| 2026-01-29 | 4sbzk | Coq `ring` times out on 16 simultaneous polynomial identities | 48 variables × 16 components = exponential term growth | Decompose into 16 component lemmas, each proven with `ring` separately | Yes |
| 2026-01-29 | 4sbzk | Coq tactic selection critical for Mat4 proofs | Wrong tactic = 30+ min timeout; right tactic = ~6s | Established tactic guide: lra (linear), ring (polynomial), reflexivity (structural), mat4_eq (records), component decomposition (complex polynomial) | Yes |
| 2026-01-29 | EnuTg | CertiCoq-WASM requires Coq 8.20, R type non-extractable | CertiCoq-WASM pinned to Coq >= 8.20 < 8.21~; Coq Reals are axiomatized | Designed layered architecture: R-abstract + Z-computational + extraction | Yes |
| 2026-01-29 | EnuTg | Never use `simpl` before `ring` on Z multiplication | `simpl` reduces Z constants (1*x, (-1)*x) to match expressions `ring` cannot handle | Use `Z.mul_1_l` or `Z.mul_0_l` directly; omit `simpl` for `ring` proofs | Yes |
| 2026-01-29 | EnuTg | `by` is reserved keyword in Coq 8.18 | Cannot use `by` as variable name in destructuring patterns `[bx by]` | Use `by0` or `b_y` as variable name instead | Yes |
| 2026-01-29 | EnuTg | Z.square_nonneg uses `0 <= n*n` not `n*n >= 0` | `>=` form causes Coq unification error (different comparison direction) | Always use `0 <= n * n` form with `Z.square_nonneg` | Yes |
| 2026-01-29 | EnuTg | R and Z share commutative ring properties | Both are commutative rings; algebraic proofs transfer | Z-based Vec2_Compute.v proves same 25 algebraic properties as R-based Vec2_Proofs.v | Yes |
| 2026-01-29 | EnuTg | Coq notation-overridden warnings from multi-module import | Multiple modules define same notations (+v, -v, etc.) | Use `Set Warnings "-notation-overridden"` around imports | Yes |
| 2026-01-29 | EnuTg | wasm_of_ocaml is production-ready for Coq→OCaml→WASM | v6.2.0, merged into js_of_ocaml, used by Jane Street | Recommended as Path 1 (production) for Coq-to-WASM pipeline | Yes |
| 2026-01-29 | EnuTg | MetaCoq Verified Extraction works with Coq 8.18 | PLDI'24 Distinguished Paper; branches for 8.17/8.18 maintained | Identified as Path 2 (academic) for partially verified extraction | Yes |
| 2026-01-29 | EnuTg | 9 distinct Coq-to-WASM paths exist (3 viable today) | Comprehensive survey: CertiCoq-WASM is only one option among many | Full landscape documented in CERTICOQ_WASM_ASSESSMENT.md | Yes |
| 2026-01-29 | EnuTg | coq-rust-extraction (AU-COBRA) needs Coq 8.20+ | v0.1.1 (May 2025), built on MetaCoq erasure | Deferred; interesting for Rust integration but too early and wrong Coq version | Yes |
| 2026-01-29 | EnuTg | WasmGC (browser GC) vs linear memory for Coq-extracted code | wasm_of_ocaml uses WasmGC (Chrome 119+, Firefox 122+, Safari 18.2+) | WasmGC ideal for pure functional Coq-extracted code (no C stubs) | Yes |
| 2026-01-29 | T2LcJ | `cbn [projections]` essential for Z record proofs | `simpl` reduces Z arithmetic into match expressions; `ring` cannot handle them | Use `cbn [zm3_0 zm3_1 ...]` to reduce only record projections before `ring` | Yes |
| 2026-01-29 | T2LcJ | Component decomposition scales to Mat4 over Z | Same pattern as R-based proofs works for Z computational bridge | 16 Local Lemmas for Mat4 mul_assoc, each proven with `ring` separately | Yes |
| 2026-01-29 | T2LcJ | `Local Ltac reduce_projections` encapsulates cbn pattern | Repeated `cbn [field_names]` calls throughout Mat4_Compute.v | Created reusable tactic abbreviation for cleaner proof scripts | Yes |
| 2026-01-29 | T2LcJ | ExtrOcamlZInt maps Z to native int | Coq Z type extracts to OCaml arbitrary-precision by default | Use `Require Import ExtrOcamlZInt` for efficient native int extraction | Yes |
| 2026-01-29 | T2LcJ | MetaCoq blocked by Coq opam repo HTTP 503 | Repository infrastructure intermittently unavailable | Try alternative sources: rocq-prover.org/packages, opam.ocaml.org | Yes |
| 2026-01-29 | T2LcJ | OCaml record syntax needed for matrix constructors | Coq record constructors don't extract as OCaml functions | Use `{ zm3_0 = 1; ... }` syntax in OCaml test driver, not `mkZMat3 ...` | Yes |
| 2026-01-29 | T2LcJ | MetaCoq buildable from source despite opam 503 | All Coq opam repos (coq.inria.fr, rocq-prover.org) return HTTP 503 | Clone MetaCoq from GitHub, pin coq-equations from GitHub source | Yes |
| 2026-01-29 | T2LcJ | coq-equations pinnable from GitHub source | opam pin bypasses broken opam repo infrastructure | `opam pin add coq-equations "git+https://github.com/mattam82/Coq-Equations.git#v1.3-8.18"` | Yes |
| 2026-01-29 | T2LcJ | MetaCoq coq-8.18 branch != MetaRocq/rocq-verified-extraction | rocq-verified-extraction requires Coq 8.19+; MetaCoq core has 8.18 branch | Use `github.com/MetaCoq/metacoq#coq-8.18` for Coq 8.18 compatibility | Yes |
| 2026-01-29 | T2LcJ | Setup scripts must pass shellcheck | Shell scripts can have subtle bugs; shellcheck catches them | Run `bash -n` + `shellcheck --severity=info` on all scripts before commit | Yes |
| 2026-01-29 | T2LcJ | libgmp-dev required for zarith/MetaCoq build | zarith (MetaCoq dep) needs GMP development headers | Include `apt-get install -y libgmp-dev` in setup script | Yes |
| 2026-01-29 | T2LcJ | Coq renamed to Rocq Prover (v9.0, March 2025) | Official rebranding; `coq` → `rocq-prover`, `From Coq` → `From Stdlib` | Stay on Coq 8.18 now; migrate to Rocq 9.x when opam repos stabilize | Yes |
| 2026-01-29 | T2LcJ | Both Coq AND Rocq opam repos return HTTP 503 | Infrastructure issue affects entire ecosystem, not version-specific | Use default `opam.ocaml.org` for core packages + GitHub pins for extras | Yes |
| 2026-01-29 | T2LcJ | MetaCoq → MetaRocq rename (v1.4 for Rocq 9.0) | `From MetaCoq` → `From MetaRocq`, `MCList` → `MRList` | For Coq 8.18: use MetaCoq/metacoq coq-8.18 branch; for Rocq 9.x: MetaRocq | Yes |
| 2026-01-29 | T2LcJ | rocq-core 9.1.0 available on opam.ocaml.org | Default opam repo has Rocq core packages (no dedicated repo needed) | `opam pin add rocq-prover 9.0.0` works from default repo | Yes |
| 2026-01-29 | T2LcJ | MetaRocq 1.4.1 is latest (Dec 2024, Rocq 9.1) | GitHub releases show clear version history per Rocq target | Use MetaRocq/metarocq releases page for version compatibility | Yes |
| 2026-01-29 | T2LcJ | MetaCoq built from source bypasses opam 503 | All 8 components build in ~30 min from `MetaCoq/metacoq#coq-8.18` | Document build order: utils→common→template-coq→pcuic→template-pcuic→safechecker→erasure→erasure-plugin | Yes |
| 2026-01-29 | T2LcJ | apt Coq vs opam Coq .vo file inconsistency | .vo compiled with apt Coq (`/usr/lib/coq`) incompatible with opam Coq (`~/.opam/default/lib/coq`) even at same version | After MetaCoq install: `rm -f *.vo *.vos *.vok *.glob` then recompile all layers with `eval $(opam env)` | Yes |
| 2026-01-29 | T2LcJ | `make install` for MetaCoq takes ~15-20 min | Builds ToPCUIC and ToTemplate quotation theories, not just file copy | Budget time accordingly; monitor with verbose output | Yes |
| 2026-01-29 | T2LcJ | Recompilation order matters for Coq .vo files | Layer dependencies: specs → proofs → complexity → compute → extraction → MetaCoq erasure | Always recompile in order; automated in `recompile_coq_proofs()` function | Yes |
| 2026-01-29 | T2LcJ | `verify_coq_proofs()` has 4 layers | Layer 1: specs+proofs, Layer 2: compute, Layer 3: extraction, Layer 4: MetaCoq (optional) | Each layer depends on prior; MetaCoq layer is optional (not a failure if unavailable) | Yes |
| 2026-01-29 | fqYWd | `simpl` destroys Z term structure for `lia`/`ring` | `simpl` reduces `Z.mul`, `Z.add` with variables into match expressions `lia`/`ring` cannot handle | Use `cbn -[Z.mul Z.div Z.add Z.sub]` to reduce only record projections; use `assert (H: 0/1000=0) by reflexivity; rewrite H` for ground divisions | Yes |
| 2026-01-29 | fqYWd | `Z.div_mul` requires specific operand order | `Z.div_mul: a * b / b = a` matches second mult operand = divisor; `Z.mul_comm` breaks this | Don't use `Z.mul_comm` before `Z.div_mul`; use `rewrite Z.div_mul by lia` directly | Yes |
| 2026-01-29 | fqYWd | `Z.gtb` not definitionally equal to `Z.ltb` with flipped args | `Z.gtb x y` defined as `match x ?= y with Gt => true | _ => false end`, NOT `Z.ltb y x` | Prove `Z_gtb_ltb: (x >? y) = (y <? x)` using `Z.compare_antisym` | Yes |
| 2026-01-29 | fqYWd | `zclamp_upper` requires `lo <= hi` precondition | Without `lo <= hi`, `v > hi` and `v < lo` possible (when `hi < lo`); clamp returns `lo` not `hi` | Add `lo <= hi` hypothesis to clamp theorems that assume ordered bounds | Yes |
| 2026-01-29 | fqYWd | `remember` + `destruct` avoids `simpl`/`cbn` reduction issues | Complex boolean proofs corrupt when `simpl`/`cbn` reduce Z comparisons | Use `remember (expr) as c; destruct c` to abstract boolean expressions before case analysis | Yes |
| 2026-01-29 | fqYWd | Color/Rect/Utils verification scales well | Same layered architecture (R→Z→Extract) works for all types | Color: 48 theorems, Rect: 42 theorems, Utils: 24 theorems, all 0 admits | Yes |
| 2026-01-29 | KuTgE | **STANDARDS VIOLATION**: Coq proofs committed without machine-checking | Coq was not installed; proofs written by pattern-matching from existing files | **NEVER commit formal proofs without compiling them with coqc.** Install tools FIRST via `./scripts/setup-formal-verification.sh`, then write and verify proofs. "If it was not tested, it does not work." | Yes |
| 2026-01-29 | KuTgE | `nra`/`nia` fail on sum-of-squares with subtraction | `nra` cannot prove `0 <= (x + -y)*(x + -y) + ...`; internal `-` representation blocks solver | R: `assert (H: forall r, 0 <= r*r) by (intro; nra). apply Rplus_le_le_0_compat; apply H.` Z: `apply Z.add_nonneg_nonneg; apply Z.square_nonneg.` | Yes |
| 2026-01-29 | KuTgE | `simpl` + `lia` fails on Z constants like 1000 | `simpl` reduces Z constants to binary representation that `lia` cannot handle | Use `cbn [field_projections]` instead of `simpl` before `lia` with Z constants; or omit `simpl` entirely | Yes |
| 2026-01-29 | KuTgE | `simpl` + `reflexivity` fails on `x * 0 / 1000 = 0` | `simpl` partially reduces but leaves `x * 0 / 1000` unreduced | Use `cbn [projections]` then `rewrite Z.mul_0_r; reflexivity` | Yes |
| 2026-01-29 | fqynP | **BREAKTHROUGH**: `by(nonlinear_arith)` requires-axiom pattern for degree-3+ polynomials | Z3 cannot prove degree-3 polynomial identities (e.g., det(A^T)=det(A)) even with helper lemma facts in context, because Z3's nonlinear_arith doesn't connect user-provided context facts to spec function expansions | **4-phase decomposition**: (1) Use distribution lemmas to expand spec functions into explicit polynomial terms, (2) Assert the expanded form with regular Z3 (which CAN expand spec functions), (3) Prove pairwise commutativity equalities with separate `by(nonlinear_arith)` assertions, (4) Close with `assert(result) by(nonlinear_arith) requires expanded_form_a, expanded_form_b;` — this decouples spec-function expansion (outer Z3 context) from polynomial equality verification (nonlinear_arith with axioms). **This is a general technique for ANY degree-3+ polynomial identity over spec functions.** | Yes |
| 2026-01-29 | fqynP | Verus `by(nonlinear_arith)` has isolated context | `by(nonlinear_arith)` does NOT inherit facts from the outer proof context — it runs in an isolated Z3 context. Only `requires` clauses provide axioms to the solver. | Always use `assert(goal) by(nonlinear_arith) requires fact1, fact2, ...;` when the solver needs external facts. Helper lemma calls only add facts to the OUTER context, not to `nonlinear_arith` blocks. | Yes |
| 2026-01-29 | fqynP | Verus file splitting for Z3 resource management | Combined mat3_proofs.rs (associativity with 200+ helper lemmas) + nonlinear_arith proofs exceeded Z3's resource limits | Split into mat3_proofs.rs (18 base theorems) and mat3_extended_proofs.rs (22 theorems + 4 helper lemmas). Each file verifies independently with duplicated spec types. Pattern applicable to any file that times out. | Yes |
| 2026-01-29 | fqynP | Never remove theorems as "Z3-intractable" | Removing Theorems 21/23 (det_transpose/det_swap_cols01) violated PEER REVIEWED PUBLISHED ACADEMIC standards; the user correctly identified this as an unacceptable compromise | Always decompose proofs further rather than removing them. The requires-axiom pattern (above) unlocked det_transpose. If Z3 truly cannot handle a proof, document it as BLOCKED with a tracking issue, never silently remove. | Yes |
| 2026-01-29 | vXZ54 | `f_equal; ring` works for Vec2 records, not `apply vec2_eq; ring` | After `apply vec2_eq`, goals still have un-reduced record projections that `ring` cannot handle | For small records (Vec2, 2 fields): use `f_equal; ring`. For large records (Mat3 9 fields, Mat4 16 fields): use `apply <type>_eq` then `ring` per field. `f_equal` only safe for ≤2 fields. | Yes |
| 2026-01-29 | vXZ54 | `nra` needed for Rmax/Rmin multiplicative area proofs | `lra` cannot handle multiplicative terms in intersection area commutativity | Use `nra` (nonlinear real arithmetic) when proof involves products of Rmax/Rmin expressions (e.g., area = width × height) | Yes |
| 2026-01-29 | vXZ54 | Mat3 transform proofs need Vec2 type in spec | Mat3 transform_point/vector operate on 2D points but Vec2 not defined in Mat3.v | Add `Record Vec2` + `vec2_eq` lemma directly in Mat3.v (separate from rource-math Vec2 which is in Vec2.v) | Yes |
| 2026-01-29 | vXZ54 | Mat4 det(-A)=det(A) for even dimension | Unlike Mat3 where det(-A)=-det(A), Mat4 satisfies det(-A)=det(A) because (-1)^4=1 | Dimension parity matters: odd dim → det(-A)=-det(A), even dim → det(-A)=det(A). Mat3 uses `ring` with negative terms; Mat4 factors cancel. | Yes |
| 2026-01-30 | wj6WE | `set` abstracts division for `ring` in project/reject proofs | `ring` cannot handle `/` (division); `lra` also fails to see through division | Use `set (k := expr / expr2)` to make term opaque, then `f_equal; ring` proves `k*w + (v - k*w) = v` | Yes |
| 2026-01-30 | wj6WE | `Rmin_id`/`Rmax_id` not available in Coq 8.18 | Standard library lemma missing | Use `unfold Rmin; destruct (Rle_dec s s); reflexivity` for 2D; `assert (Hs: Rmin s s = s) {...}; rewrite Hs` pattern for 3D/4D nested cases | Yes |
| 2026-01-30 | wj6WE | ring+rewrite decomposition for nonlinear constrained proofs | `ring` alone can't handle `nx²+ny²=1` constraint; `nra` times out on full expression | Factor expression with `ring` into `f(constraint_expr)`, then `rewrite Hconstraint`, then `ring` to close. Works for reflect_preserves_length_sq across Vec2/Vec3. | Yes |
| 2026-01-30 | wj6WE | Verification coverage milestone: 50% operations formally verified | Added reflect, project, reject, min/max_element, div, splat, element_sum across Vec2-4, Color add/scale/invert, Rect scale | 115/230 operations (50%), up from 92/230 (40%); 939 total theorems (was 862, +77) | Yes |
| 2026-01-30 | wj6WE | rocq-of-rust generates monadic shallow embedding, not algebraic specs | Rust→Rocq translation models memory (alloc/read/deref), not math (a+b=b+a) | NOT VIABLE for rource-math: f32 literals → `UnsupportedLiteral`, structural `Admitted` axioms, fundamentally different representation from our algebraic proofs. Better suited for systems-level verification (smart contracts, protocols). | Yes |
| 2026-01-30 | wj6WE | rocq-of-rust requires Rocq 9.0 + nightly-2024-12-07 | Binary builds fine, translation succeeds, but output requires RocqOfRust library (coq-coqutil, coq-hammer, rocq-smpl) from opam repos returning HTTP 503 | Two blockers: (1) opam infra unavailable, (2) Rocq 9.0 vs our Coq 8.18. Even if infra was available, bridging monadic output to algebraic proofs would require enormous refinement proof effort. | Yes |
| 2026-01-30 | wj6WE | `RUSTUP_TOOLCHAIN=nightly-2024-12-07` needed for rocq-of-rust | Tool uses rustc internals via `extern crate rustc_*`; needs matching sysroot | Set `RUSTUP_TOOLCHAIN` env var + `LD_LIBRARY_PATH=$(rustc +nightly-2024-12-07 --print sysroot)/lib` for dynamic linking | Yes |
| 2026-01-30 | 9ENKM | Stainless FP paper (arXiv:2601.14059) not applicable to rource-math | Scala-only tool; no Coq proofs; no error bounds; Z3 worst at FP (78–85% vs cvc5 89–100%) | Paper valuable as landscape survey; confirms Coq+Flocq+VCFloat2 is better path. Created FLOATING_POINT_VERIFICATION.md | Yes |
| 2026-01-30 | 9ENKM | Coq FP ecosystem (Flocq+VCFloat2+Gappa) all Coq 8.18 compatible | Flocq 4.1.3, VCFloat2 2.1.1, Gappa 1.5.4, CoqInterval 4.8.1 all in Coq Platform 8.18 | Recommended path for FP verification: Flocq for IEEE 754 formalization, VCFloat2 for automated error bounds, Gappa for interval proofs | Yes |
| 2026-01-30 | 9ENKM | FP verification proves error bounds, not algebraic properties | FP proofs show "result within N ULPs of exact" — complementary to R-based algebraic proofs, not replacement | Two-layer architecture: R-based proofs (mathematical correctness) + FP proofs (numerical accuracy). LAProof/VCFloat2 designed for this pattern. | Yes |
| 2026-01-30 | 9ENKM | ~46 of 114 FP operations immediately achievable with Flocq+VCFloat2 | sqrt-based (12), rounding (12), min/max/abs/clamp (16), lerp (6) are well-studied | Phase FP-1 could reach ~70% coverage (162/230); requires Flocq installation and spec writing | Yes |
| 2026-01-30 | 9ENKM | LAProof (ARITH 2023) verifies FP matrix-vector products | Kellison, Appel, Tekriwal, Bindel at Princeton/VeriNum; formal accuracy proofs for linear algebra | Directly applicable to Mat3/Mat4 transform_point/transform_vector; L2 norm proof applicable to Vec length() | Yes |
| 2026-01-30 | 9ENKM | Z3 is weakest SMT solver for floating-point queries | Stainless paper: Z3 78–85% vs cvc5 89–100% vs Bitwuzla 67–85% | If Verus ever adds FP support, portfolio solving (Z3+cvc5+Bitwuzla) would be needed. For now, Coq approach avoids this limitation entirely. | Yes |
| 2026-01-30 | 9ENKM | No existing formalization of HSL color space in any proof assistant | Surveyed Flocq, VCFloat, LAProof, CompCert — none formalize color space conversions | HSL verification requires novel proof engineering; lowest priority in FP roadmap (Phase FP-3) | Yes |
| 2026-01-30 | 9ENKM | det(A*B)=det(A)*det(B) provable with `ring` for both Mat3 AND Mat4 | Mat3: 18 variables (degree 3), compiles instantly. Mat4: 32 variables (degree 4), compiles in ~8s. No component decomposition needed. | Unlike mul_assoc (which needs 16 component lemmas for Mat4), det_mul is a scalar identity — `ring` handles it directly even for Mat4. Added +8 theorems (4 per type: det_mul, det_square, det_mul_comm, det_scale). | Yes |
| 2026-01-30 | 9ENKM | Kani (Amazon) is only Rust tool with bit-precise FP verification | CBMC-based bounded model checker, verifies NaN/overflow/infinity at bit level | ADOPT as Layer 2 for edge-case safety verification of f32 operations; complements Verus (algebra) + Coq (proofs). Created RUST_VERIFICATION_LANDSCAPE.md | Yes |
| 2026-01-30 | 9ENKM | Aeneas produces pure functional code (not monadic like rocq-of-rust) | MIR → LLBC → pure lambda calculus; value-based, no memory model | Most promising spec-to-impl bridge tool; MONITOR pending f32 support confirmation. Charon tracking issue #142 doesn't list f32 as unsupported. | Yes |
| 2026-01-30 | 9ENKM | Creusot leverages Why3 which has comprehensive ieee_float theory | Why3's Float32/Float64 types axiomatize full IEEE 754 (all rounding modes, NaN, specials) | MONITOR — potentially enables f32 deductive verification via CVC5 (89-100% FP success vs Z3's 78-85%). Creusot→Why3→CVC5 could outperform Verus→Z3 for FP. | Yes |
| 2026-01-30 | 9ENKM | hax (formerly hacspec v2) backends do NOT support floating-point | Paper explicitly states "most backends do not have any support for floats" (VSTTE 2024) | NOT APPLICABLE for rource-math; designed for cryptographic integer code, not numerical/graphics math | Yes |
| 2026-01-30 | 9ENKM | 8 Rust verification tools now surveyed for rource-math | Verus, Coq, Kani, Aeneas, Creusot, hax, rocq-of-rust, Stainless | Comprehensive landscape documented in RUST_VERIFICATION_LANDSCAPE.md; 4-layer architecture proposed: Verus+Coq (algebra) + Kani (edge cases) + Flocq (FP accuracy) | Yes |
| 2026-01-30 | 9ENKM | Kani `#[cfg(kani)]` requires workspace check-cfg | `cargo check` warns `unexpected cfg condition name: kani` | Add `unexpected_cfgs = { level = "warn", check-cfg = ['cfg(kani)'] }` to `[workspace.lints.rust]` in root Cargo.toml | Yes |
| 2026-01-30 | 9ENKM | Kani has built-in NaN checks on every float operation | Default checks fire even for `kani::any()` inputs that include NaN/inf bit patterns | Use `kani::assume(v.is_finite() && v.abs() < SAFE_BOUND)` to restrict symbolic search space. Do NOT use unbounded `kani::any::<f32>()` without preconditions. | Yes |
| 2026-01-30 | 9ENKM | `lerp(f32::MAX, -f32::MAX, 0.0)` produces NaN | `(b-a) = -MAX - MAX` overflows to `-inf`; `-inf * 0.0 = NaN` (IEEE 754) | Standard `a + (b-a)*t` formula requires bounded inputs; use `SAFE_BOUND = 1e18` to prevent intermediate overflow. Affects ALL math libraries. | Yes |
| 2026-01-30 | 9ENKM | `Vec2::project()` NaN for denormalized onto vectors | `length_squared > 0.0` passes for tiny denormals but `dot / length_squared` overflows to `±inf`; `inf * 0.0 = NaN` | Require `onto.length_squared() > f32::MIN_POSITIVE` in Kani precondition; division overflow occurs even with nonzero denominator | Yes |
| 2026-01-30 | 9ENKM | Kani does not support C `tanf` foreign function | `Mat4::perspective()` calls `f32::tan()` → C `tanf` → Kani failure | Remove perspective harness; document as known limitation (Kani issue #2423). Verify perspective algebraically via Verus/Coq instead. | Yes |
| 2026-01-30 | 9ENKM | Kani models `sinf`/`cosf` but not `tanf` | `Mat3::rotation()` (uses sin/cos) passes; `Mat4::perspective()` (uses tan) fails | Likely CBMC math stubs include sin/cos but not tan. Transcendental coverage is partial. | Yes |
| 2026-01-30 | 9ENKM | Mat4 determinant harness takes ~60s due to 16 symbolic floats | 80 CBMC checks for 4×4 determinant with symbolic elements | Most harnesses verify in <2s; Mat4 determinant is the exception. Plan accordingly for CI timeout settings. | Yes |
| 2026-01-30 | 9ENKM | Kani `cargo kani setup` installs nightly-2025-11-21 toolchain | Kani v0.67.0 needs its own Rust nightly with CBMC support | Does not conflict with stable/nightly used for development; `cargo kani` auto-selects correct toolchain | Yes |
| 2026-01-30 | 9ENKM | Safe bounds for symbolic f32 vary by operation depth | `sqrt(MAX/n)` for n-component dot; `(MAX/k)^(1/d)` for degree-d polynomial with k terms | Vec: 1e18 (2 components), Mat3 det: 1e12 (degree 3), Mat4 det: 1e9 (degree 4). Document bound derivation in harness comments. | Yes |
| 2026-01-30 | 9qF3t | Kani SIGSEGV when compiling 110+ harnesses at once | Kani compiler (kani-compiler) crashes with SIGSEGV when processing entire rource-math crate with 110 harnesses | Run harnesses individually: `cargo kani -p rource-math --harness <name>`. Full-crate `cargo kani -p rource-math` triggers memory issue in compiler. | Yes |
| 2026-01-30 | 9qF3t | `Rect::intersects(self)` fails when `width < ULP(x)` | IEEE 754: `x + width > x` is FALSE when width < unit of least precision at x. At `|x|=1e6`, ULP ≈ 0.12 | Require `width > 1.0` and `|x| < 1e6` for self-intersection property. This is a genuine FP edge case where mathematical property `x + w > x for w > 0` fails. | Yes |
| 2026-01-30 | 9qF3t | `Rect::from_center_size` center roundoff | `cx - w/2 + w/2 ≠ cx` due to catastrophic cancellation when `|cx| >> w` | Tighten bounds to `|cx| < 1e6`, `w < 1e6`; use tolerance 1.0 (roundoff ≈ 0.24). Document as genuine FP limitation. | Yes |
| 2026-01-30 | 9qF3t | CBMC symbolic `sqrt()` is extremely expensive | `get_scale()` calls `sqrt()`, and CBMC takes >15 min for symbolic sqrt verification | Replace exact-value roundtrip assertions with finiteness checks for sqrt-based operations. Exact roundtrips verified algebraically in Verus/Coq instead. | Yes |
| 2026-01-30 | 9qF3t | 65 new Kani harnesses scale well across 7 types | Same patterns (finiteness, NaN-freedom, postconditions, reflexivity) apply uniformly | Standard templates: `verify_<type>_<op>_finite`, `verify_<type>_<op>_no_nan`, `verify_<type>_approx_eq_reflexive`, `verify_<type>_<op>_componentwise`. Harness count: 45 → 110 (+65). | Yes |

---

## Performance Scale and Precision

### The 50,000 FPS Target

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    CRITICAL: FRAME BUDGET CONSTRAINT                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Target FPS:     50,000 FPS (theoretical maximum on test hardware)          │
│  Frame Budget:   20 microseconds (20,000 nanoseconds) MAXIMUM               │
│                                                                             │
│  At this scale:                                                             │
│    • 1 microsecond = 5% of frame budget                                     │
│    • 100 nanoseconds = 0.5% of frame budget                                 │
│    • 10 nanoseconds = 0.05% of frame budget                                 │
│    • 1 nanosecond = 0.005% of frame budget                                  │
│                                                                             │
│  Every nanosecond matters. Every CPU cycle counts.                          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### CPU Clock Cycle Reference

On a 3.0 GHz CPU (typical test hardware):

| Duration | Clock Cycles | Significance |
|----------|--------------|--------------|
| 1 picosecond | 0.003 cycles | Sub-instruction timing |
| 1 nanosecond | 3 cycles | Single instruction |
| 10 nanoseconds | 30 cycles | L1 cache access |
| 100 nanoseconds | 300 cycles | L2 cache access |
| 1 microsecond | 3,000 cycles | Complex operation |
| 10 microseconds | 30,000 cycles | Half frame budget |
| 20 microseconds | 60,000 cycles | **FULL FRAME BUDGET** |

### Measurement Precision Requirements

| Measurement | Precision Required | Example |
|-------------|-------------------|---------|
| Per-operation timing | Picoseconds | Draw call: 360 ps ± 6.8 ps |
| Per-label timing | Nanoseconds | Label placement: 88.9 ns |
| Per-frame timing | Microseconds | Full frame: 18.4 µs |
| Improvement claims | Exact percentage | 52.3% improvement (not "~50%") |

### The Absolute Rule

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  NEVER guess about performance. NEVER assume an optimization helps.         │
│  NEVER overstate improvements. NEVER approximate measurements.              │
│                                                                             │
│  The ONLY acceptable evidence is:                                           │
│                                                                             │
│  1. BEFORE benchmark (criterion, 100+ samples, 95% CI)                      │
│  2. AFTER benchmark (same methodology, same conditions)                     │
│  3. EXACT improvement calculation with measured values                      │
│  4. Statistical significance verification                                   │
│                                                                             │
│  If you cannot measure it, you cannot claim it.                             │
│  If you did not benchmark BEFORE changes, the change is speculation.        │
│  If the improvement is not statistically significant, it did not happen.    │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Current Performance Status

| Metric | Current | Target | Status |
|--------|---------|--------|--------|
| Frame time | ~18-23 µs | <20 µs | Near target |
| Optimization phases | 81 | Ongoing | Active |
| Algorithms evaluated | 79+ | Comprehensive | See ALGORITHM_CANDIDATES.md |

---

## Quality Domains

### Domain 1: Performance Engineering (Expert+)

**Standard**: Picosecond-to-nanosecond optimization with mathematical proof

| Criterion | Requirement |
|-----------|-------------|
| Benchmarks | Criterion with 100+ samples, 95% CI |
| Documentation | Before/after in CHRONOLOGY.md, BENCHMARKS.md |
| Complexity | Big-O analysis with scaling verification |
| Proof | Mathematical proof for complexity claims |
| Precision | Picosecond/nanosecond measurements |
| Frame Budget | Total render time < 20 µs |

**Reference**: `docs/performance/CHRONOLOGY.md` (81 phases)

---

### Domain 2: UI/UX Excellence (Target: Expert+)

**Standard**: Mobile-first, touch-first, user-centric design

| Criterion | Requirement |
|-----------|-------------|
| Touch targets | 44×44px minimum (Apple HIG) |
| Typography | 12px minimum, 4.5:1 contrast ratio (WCAG AA) |
| Layout | 85%+ viewport for primary content during use |
| Labels | All icons must have text labels or tooltips |
| Feedback | Every action has visible/haptic feedback |
| Progressive disclosure | Show less, reveal more on demand |
| Mobile testing | Test on real iOS Safari before merge |

**Reference**: `docs/ux/MOBILE_UX_ROADMAP.md` (46 issues tracked)

**Critical Mobile UX Rules**:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    MOBILE UX REQUIREMENTS                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. TOUCH TARGETS: Every interactive element ≥ 44×44px                  │
│     └─ Buttons, links, sliders, toggles, pills, icons                   │
│                                                                         │
│  2. TYPOGRAPHY: Minimum 12px, prefer 14-16px for body text              │
│     └─ Contrast ratio ≥ 4.5:1 for all text                              │
│     └─ No overlapping labels (collision detection required)             │
│                                                                         │
│  3. LAYOUT: Primary content takes 80%+ of viewport                      │
│     └─ Stats/chrome collapsible or auto-hide during use                 │
│     └─ Safe areas respected (notch, Dynamic Island, home indicator)     │
│                                                                         │
│  4. ICONS: Must have labels OR long-press tooltips                      │
│     └─ Mystery meat navigation is FORBIDDEN                             │
│                                                                         │
│  5. INFORMATION: Progressive disclosure, not information dump           │
│     └─ Developer metrics hidden by default                              │
│     └─ User-centric language, no jargon                                 │
│                                                                         │
│  6. GESTURES: Swipe-to-dismiss, pinch-to-zoom, pan supported            │
│     └─ First-time gesture hints for discoverability                     │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

### Domain 3: Testing Maturity (Target: Expert+)

**Standard**: Comprehensive testing with mutation analysis

| Criterion | Requirement |
|-----------|-------------|
| Unit tests | All public functions tested |
| Property tests | Mathematical invariants verified |
| Mutation testing | 80%+ mutation score for critical crates |
| Visual regression | Golden image comparison for rendering |
| Cross-browser | Chrome, Firefox, Safari, Edge |
| Load testing | 100k commits, 30 minutes, <5% memory growth |

**Reference**: `docs/performance/FUTURE_WORK.md` (TST-1 through TST-4)

---

### Domain 4: Security Posture (Target: Expert+)

**Standard**: Quantified security with supply chain transparency

| Criterion | Requirement |
|-----------|-------------|
| Fuzzing | Quantified coverage (75%+ edge coverage) |
| SBOM | Generated with every release |
| Audits | Weekly `cargo audit`, zero known vulnerabilities |
| Unsafe | Minimal, documented, justified |
| Dependencies | Audited, minimal, justified |

**Reference**: `docs/performance/FUTURE_WORK.md` (SEC-1 through SEC-4)

---

### Domain 5: Accessibility (Target: Expert+)

**Standard**: WCAG 2.1 AA compliance

| Criterion | Requirement |
|-----------|-------------|
| Keyboard | Full navigation without mouse |
| Screen reader | VoiceOver/TalkBack compatible |
| Contrast | 4.5:1 minimum for text, 3:1 for UI elements |
| Focus | Visible focus indicators |
| Motion | Reduced motion support |
| Touch | 44×44px targets, no hover-only interactions |

**Reference**: `docs/ux/MOBILE_UX_ROADMAP.md` (ACC-1 through ACC-5)

---

### Domain 6: Operational Readiness (Target: Expert+)

**Standard**: Production-grade telemetry and SLOs

| Criterion | Requirement |
|-----------|-------------|
| Telemetry | Tracing spans in hot paths |
| Metrics | P50/P99/P99.9 latency documented |
| Load testing | 30-minute stability test |
| Memory | Budget documented, growth <5% |
| Error tracking | Categorized, measured, alerted |

**Reference**: `docs/performance/FUTURE_WORK.md` (OP-1 through OP-5)

---

### Domain 7: Documentation Quality (Target: Expert+)

**Standard**: Complete, accurate, actionable documentation

| Criterion | Requirement |
|-----------|-------------|
| API stability | STABILITY.md with semver policy |
| Architecture | ADRs for key decisions |
| Runbooks | Operational playbooks |
| Performance | Before/after measurements always |
| UI/UX | Screenshots, issue tracking |

**Reference**: `docs/performance/FUTURE_WORK.md` (DOC-1 through DOC-3)

---

## Project Overview

**Rource** (Rust + Gource) is a complete rewrite of [Gource](https://github.com/acaudwell/Gource), the software version control visualization tool, in Rust with WebAssembly support.

### Goals

| Goal             | Description                                               |
|------------------|-----------------------------------------------------------|
| **Portable**     | Run on any CPU architecture without requiring a dedicated GPU |
| **Lightweight**  | Minimal dependencies, small binary size (~3.8MB native, ~1MB WASM gzip) |
| **Fast**         | Leverage Rust's performance and modern rendering techniques |
| **User-friendly**| Better UI/UX than original Gource (Expert+ mobile experience) |
| **Feature-complete** | Maintain at minimum feature parity with Gource        |
| **Accessible**   | WCAG 2.1 AA compliant, keyboard navigable                 |

### Key Documents

| Document | Purpose |
|----------|---------|
| `README.md` | Project overview and usage |
| `CONTRIBUTING.md` | Development guidelines |
| `docs/REVIEW_STANDARDS.md` | Code review requirements |
| `STABILITY.md` | API stability policy |
| `SECURITY.md` | Security policy |
| `docs/performance/CHRONOLOGY.md` | Optimization history (83 phases) |
| `docs/performance/BENCHMARKS.md` | Raw benchmark data |
| `docs/performance/NOT_APPLICABLE.md` | Algorithms evaluated as N/A |
| `docs/performance/ALGORITHM_CANDIDATES.md` | Future optimization candidates |
| `docs/performance/SUCCESSFUL_OPTIMIZATIONS.md` | Implemented optimizations catalog |
| `docs/performance/FUTURE_WORK.md` | Expert+ technical roadmap |
| `docs/verification/FORMAL_VERIFICATION.md` | Formal verification overview and index (1057 theorems/harnesses) |
| `docs/verification/VERUS_PROOFS.md` | Verus theorem tables (266 proof functions, 8 files) |
| `docs/verification/COQ_PROOFS.md` | Coq proofs (R + Z, 681 theorems, development workflow) |
| `docs/verification/VERIFICATION_COVERAGE.md` | Coverage metrics, limitations, floating-point assessment |
| `docs/verification/WASM_EXTRACTION_PIPELINE.md` | Coq-to-WASM pipeline, tool ecosystem, Rocq migration |
| `docs/verification/SETUP_GUIDE.md` | Formal verification environment setup |
| `docs/verification/FLOATING_POINT_VERIFICATION.md` | FP verification feasibility: Stainless paper, Flocq+VCFloat2 roadmap |
| `docs/verification/RUST_VERIFICATION_LANDSCAPE.md` | 8-tool landscape survey: Kani (ADOPT), Aeneas/Creusot (MONITOR), hax (N/A) |
| `docs/verification/CERTICOQ_WASM_ASSESSMENT.md` | Coq-to-WASM pipeline assessment (9-path survey) |
| `docs/ux/MOBILE_UX_ROADMAP.md` | Expert+ UI/UX roadmap |
| `LICENSE` | GPL-3.0 license |

---

## Quick Start

### Session Setup (MANDATORY)

Before starting development, run the setup scripts:

```bash
# 1. Basic session setup (Rust tooling, environment)
source scripts/session-setup.sh

# 2. Formal verification tools (ALL tools) - REQUIRED for math/core work
#    This installs: Verus, Coq, opam, coq-equations, MetaCoq, wasm_of_ocaml
./scripts/setup-formal-verification.sh

# 3. Check-only mode (verify everything is installed)
./scripts/setup-formal-verification.sh --check

# 4. Selective installation (if only one tool is needed)
./scripts/setup-formal-verification.sh --verus        # Verus only
./scripts/setup-formal-verification.sh --coq           # Coq + opam ecosystem
./scripts/setup-formal-verification.sh --metacoq       # MetaCoq from source
./scripts/setup-formal-verification.sh --wasm-of-ocaml # wasm_of_ocaml
```

**IMPORTANT**: The formal verification setup is REQUIRED when working on:
- `rource-math` (vector, matrix, color types)
- `rource-core` (scene, physics, animation)
- Any code that requires correctness proofs
- Coq-to-WASM pipeline work

**Setup Guide**: See `docs/verification/SETUP_GUIDE.md` for detailed manual
installation instructions and troubleshooting.

### Session Checklist

**Before ANY work begins, verify**:

```bash
# 1. Tests pass
cargo test

# 2. No warnings
cargo clippy -- -D warnings

# 3. Formatted
cargo fmt --check

# 4. Formal verification tools available (if needed)
/tmp/verus/verus --version
coqc --version
eval $(opam env)  # Activate opam environment

# 5. Read the roadmaps to understand current priorities
cat docs/performance/FUTURE_WORK.md
cat docs/ux/MOBILE_UX_ROADMAP.md
```

### Required Tools

| Tool | Version | Purpose | Setup Script |
|------|---------|---------|--------------|
| Rust | 1.93+ | Core language | `scripts/session-setup.sh` |
| Cargo | Latest | Package manager | `scripts/session-setup.sh` |
| wasm-pack | 0.12+ | WASM bundling | `scripts/session-setup.sh` |
| rustup | Latest | Toolchain management | `scripts/session-setup.sh` |
| **Kani** | 0.67.0+ | Bounded model checking (IEEE 754 f32) | `cargo install --locked kani-verifier && cargo kani setup` |
| **Verus** | 0.2026.01.23+ | Formal verification (Rust) | `scripts/setup-formal-verification.sh` |
| **Coq** | 8.18+ | Formal verification (proofs) | `scripts/setup-formal-verification.sh` |
| **opam** | 2.x | OCaml package manager | `scripts/setup-formal-verification.sh` |
| **coq-equations** | 1.3+8.18 | Dependent pattern matching | `scripts/setup-formal-verification.sh` |
| **MetaCoq** | 8.18.dev | Verified extraction (Path 2) | `scripts/setup-formal-verification.sh` |
| **wasm_of_ocaml** | 6.2.0+ | OCaml-to-WASM (Path 1) | `scripts/setup-formal-verification.sh` |
| cargo-tarpaulin | Latest | Code coverage | `scripts/session-setup.sh` |

### Running the Project

```bash
# Windowed mode (interactive)
cargo run --release -- .

# Headless mode (batch export)
cargo run --release -- --headless --output /tmp/frames --seconds-per-day 0.5 .
```

---

## Architecture

### Crate Structure

```
rource/
├── crates/
│   ├── rource-math/       # Math types (Vec2, Vec3, Vec4, Mat3, Mat4, Color)
│   ├── rource-vcs/        # VCS log parsing (Git, SVN, Custom, Mercurial, Bazaar)
│   ├── rource-core/       # Core engine (scene, physics, animation, camera, config)
│   └── rource-render/     # Rendering (software, WebGL2, wgpu, bloom, shadows)
├── rource-cli/            # Native CLI application (winit + softbuffer)
└── rource-wasm/           # WebAssembly application
```

**Test Count**: 2,100+ tests total across all crates.

### Rendering Backends

| Backend | Platform | Description |
|---------|----------|-------------|
| wgpu | Native + WASM | Cross-platform GPU via WebGPU/Vulkan/Metal/DX12 |
| WebGL2 | WASM | GPU-accelerated browser rendering (fallback) |
| Software | All | Pure CPU rendering, maximum compatibility |

### CLI and WASM Rendering Synchronization

**The CLI and WASM have separate rendering code that must be kept in sync.**

When making visual/rendering changes:
1. **BENCHMARK BASELINE FIRST** - Run `cargo test -p rource-wasm bench_ --release -- --nocapture`
2. Update `rource-cli/src/rendering.rs` for native CLI
3. **Also update** `rource-wasm/src/lib.rs` and `rource-wasm/src/render_phases.rs` with same changes
4. Update `crates/rource-render/src/label.rs` if label-related changes
5. **BENCHMARK AFTER** - Compare with baseline, verify < 5% regression
6. Rebuild WASM with `./scripts/build-wasm.sh`
7. Test both CLI and WASM to verify visual parity
8. **Test on mobile Safari** to verify mobile UX
9. Document benchmark results in commit message

---

## Development Guidelines

### The Development Workflow

Every change MUST follow this workflow:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    EXPERT+ DEVELOPMENT WORKFLOW                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. UNDERSTAND                                                          │
│     └─ Read relevant roadmap docs (FUTURE_WORK.md, MOBILE_UX_ROADMAP.md)│
│     └─ Understand the current state and target state                    │
│     └─ Identify success criteria BEFORE starting                        │
│                                                                         │
│  2. MEASURE BASELINE (if applicable)                                    │
│     └─ Performance: Create criterion benchmarks                         │
│     └─ UI/UX: Screenshot current state on mobile                        │
│     └─ Tests: Note current coverage/mutation score                      │
│                                                                         │
│  3. IMPLEMENT                                                           │
│     └─ Make targeted, minimal changes                                   │
│     └─ Follow all domain-specific standards                             │
│     └─ Add tests for new functionality                                  │
│                                                                         │
│  4. VERIFY CORRECTNESS                                                  │
│     └─ cargo test (all 2,100+ tests pass)                               │
│     └─ cargo clippy -- -D warnings (zero warnings)                      │
│     └─ cargo fmt --check (formatted)                                    │
│     └─ Mobile Safari test (if UI change)                                │
│                                                                         │
│  5. MEASURE IMPROVEMENT                                                 │
│     └─ Performance: Run same benchmarks, calculate exact improvement    │
│     └─ UI/UX: Screenshot new state, compare                             │
│     └─ Tests: Verify coverage maintained/improved                       │
│                                                                         │
│  6. DOCUMENT                                                            │
│     └─ Performance: CHRONOLOGY.md, BENCHMARKS.md                        │
│     └─ UI/UX: Update MOBILE_UX_ROADMAP.md status                        │
│     └─ Update relevant roadmap documents                                │
│                                                                         │
│  7. COMMIT                                                              │
│     └─ Clear message with metrics and impact                            │
│     └─ Reference issue/task IDs                                         │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Code Style

- Use `cargo fmt` before committing
- Run `cargo clippy -- -D warnings` and fix ALL warnings
- Follow Rust API guidelines: https://rust-lang.github.io/api-guidelines/

### Building

```bash
# Debug build (native)
cargo build

# Release build (native)
cargo build --release

# WASM build
wasm-pack build --target web --release
```

### Testing

```bash
# Run all tests
cargo test

# Run specific crate tests
cargo test -p rource-core

# Run with output
cargo test -- --nocapture
```

---

## Performance Optimization Standards

### The Optimization Workflow

Every optimization MUST follow this exact process:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    OPTIMIZATION WORKFLOW                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. IDENTIFY                                                            │
│     └─ Profile, grep for patterns, analyze algorithmic complexity       │
│                                                                         │
│  2. BENCHMARK BASELINE                                                  │
│     └─ Create criterion benchmark BEFORE any changes                    │
│     └─ Record exact measurements with statistical significance          │
│     └─ Test multiple input sizes to verify complexity                   │
│                                                                         │
│  3. IMPLEMENT                                                           │
│     └─ Make targeted, minimal changes                                   │
│     └─ Add comments explaining the optimization                         │
│     └─ Preserve all existing behavior                                   │
│                                                                         │
│  4. VERIFY CORRECTNESS                                                  │
│     └─ Run ALL tests: cargo test                                        │
│     └─ Run clippy: cargo clippy -- -D warnings                          │
│     └─ Run rustfmt: cargo fmt --check                                   │
│                                                                         │
│  5. BENCHMARK OPTIMIZED                                                 │
│     └─ Run same benchmarks as step 2                                    │
│     └─ Calculate exact improvement percentages                          │
│     └─ Verify scaling behavior matches theoretical complexity           │
│                                                                         │
│  6. DOCUMENT                                                            │
│     └─ CHRONOLOGY.md: Full phase documentation                          │
│     └─ BENCHMARKS.md: Raw data tables                                   │
│     └─ SUCCESSFUL_OPTIMIZATIONS.md: Summary entry                       │
│                                                                         │
│  7. COMMIT                                                              │
│     └─ Clear message with phase number and key metrics                  │
│     └─ Include improvement percentages in commit body                   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Quality Bar

| Criterion | Requirement |
|-----------|-------------|
| **Measurable** | Backed by criterion benchmarks with statistical significance |
| **Documented** | Added to ALL THREE docs/performance/ files |
| **Correct** | All 2,100+ tests must pass |
| **Clean** | Clippy and rustfmt compliant |
| **Verifiable** | Benchmarks can be re-run to reproduce results |
| **Mathematical** | Include complexity analysis and/or mathematical proof |

### Statistical Rigor Requirements

All benchmark claims must include:

1. **Sample size**: Minimum 100 samples (criterion default)
2. **Confidence interval**: 95% CI reported
3. **Multiple input sizes**: Test scaling behavior (e.g., 50, 100, 200, 300, 500)
4. **Throughput metrics**: Elements/second where applicable
5. **Outlier analysis**: Report and explain outliers
6. **Reproducibility**: Same results on repeated runs

Example of proper benchmark reporting:

```
Instance Population (criterion, 100 samples, 95% CI):

| Avatar Count | Per-Texture | Texture Array | Improvement |
|--------------|-------------|---------------|-------------|
| 50           | 586.38 ns   | 300.28 ns     | -48.8%      |
| 100          | 1.1552 µs   | 564.60 ns     | -51.1%      |
| 300          | 3.9438 µs   | 1.7219 µs     | -56.3%      |

Mathematical Proof:
- Per-texture: T(n) = 1.06n ns (linear regression, R² ≈ 0.999)
- Texture array: T(n) = 360 ps ± 6.8 ps (constant)
- Complexity: O(n) → O(1) verified
```

### Current Optimization History

See `docs/performance/CHRONOLOGY.md` for complete history (77 phases).

### MANDATORY: Benchmark Before Committing Performance-Sensitive Code

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    CRITICAL: NEVER ASSUME, ALWAYS BENCHMARK                  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ANY change to the following code paths REQUIRES A/B benchmarking           │
│  BEFORE committing:                                                         │
│                                                                             │
│  • Label rendering (LabelPlacer, try_place, collision detection)            │
│  • Rendering loops (render_files, render_users, render_actions)             │
│  • Spatial data structures (grids, hashes, trees)                           │
│  • Per-frame operations (reset, update, draw calls)                         │
│  • Hot paths in rource-render, rource-wasm/render_phases.rs                 │
│  • Any code with "optimization", "performance", or "LOD" in comments        │
│                                                                             │
│  Even "simple" changes like adding 4 comparisons can have unexpected        │
│  impacts due to: cache effects, branch prediction, struct size changes,     │
│  compiler optimization differences, or memory layout changes.               │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

**A/B Benchmarking Protocol**:

```bash
# 1. BEFORE making changes, run baseline benchmarks
cargo test -p rource-wasm bench_ --release -- --nocapture

# 2. Record baseline numbers (copy/paste output)

# 3. Make your changes

# 4. Run SAME benchmarks again
cargo test -p rource-wasm bench_ --release -- --nocapture

# 5. Compare results - regression threshold is 5%
#    If regression > 5%, investigate before committing

# 6. For proper A/B comparison, use git checkout:
git stash
git checkout HEAD~1 -- <files>   # Baseline
cargo test -p rource-wasm bench_<name> --release -- --nocapture
git checkout HEAD -- <files>      # With changes
cargo test -p rource-wasm bench_<name> --release -- --nocapture
git stash pop
```

**Available Benchmarks**:

| Benchmark | What It Measures | Location |
|-----------|------------------|----------|
| `bench_label_placer_new` | LabelPlacer creation cost | render_phases/tests/benchmark_tests.rs |
| `bench_label_placer_reset` | Per-frame reset cost | render_phases/tests/benchmark_tests.rs |
| `bench_label_placer_try_place` | Single label placement | render_phases/tests/benchmark_tests.rs |
| `bench_label_placer_try_place_with_fallback` | Placement with collision | render_phases/tests/benchmark_tests.rs |
| `bench_full_label_placement_scenario` | Full frame (30+50 labels) | render_phases/tests/benchmark_tests.rs |
| `bench_beam_sorting` | Action beam ordering | render_phases/tests/benchmark_tests.rs |
| `bench_user_label_sorting` | User label prioritization | render_phases/tests/benchmark_tests.rs |
| `bench_estimate_text_width` | Text width estimation | render_phases/tests/benchmark_tests.rs |
| `bench_glow_lod_culling` | Glow LOD decision overhead | render_phases/tests/benchmark_tests.rs |

**Regression Thresholds**:

| Severity | Threshold | Action |
|----------|-----------|--------|
| Acceptable | < 5% | Document in commit message |
| Warning | 5-10% | Investigate, justify in PR |
| Blocking | > 10% | Do NOT commit without review |

**Session 7 Lesson Learned**: T9 viewport bounds check was committed without benchmarking. Post-commit A/B testing revealed +2.7% overhead (acceptable) but this should have been verified BEFORE committing. Always benchmark first.

---

## UI/UX Excellence Standards

### The Mobile-First Mandate

**Every UI change MUST be tested on mobile Safari before merge.**

The mobile experience is the PRIMARY experience. Desktop is the fallback.

### The UI/UX Workflow

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    UI/UX CHANGE WORKFLOW                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. CHECK ROADMAP                                                       │
│     └─ Read docs/ux/MOBILE_UX_ROADMAP.md                                │
│     └─ Identify relevant issue IDs (L1-L9, T1-T7, A1-A8, etc.)          │
│                                                                         │
│  2. SCREENSHOT BASELINE                                                 │
│     └─ Take screenshot on mobile Safari BEFORE changes                  │
│     └─ Note specific measurements (touch target sizes, font sizes)      │
│                                                                         │
│  3. IMPLEMENT                                                           │
│     └─ Follow the implementation guidance in roadmap                    │
│     └─ Respect all constraints (44px touch, 12px font, 4.5:1 contrast)  │
│     └─ Test on mobile during development, not after                     │
│                                                                         │
│  4. VERIFY                                                              │
│     └─ Screenshot on mobile Safari AFTER changes                        │
│     └─ Verify touch targets with inspector                              │
│     └─ Verify contrast ratios                                           │
│     └─ Test all gestures (tap, swipe, pinch)                            │
│     └─ Test with VoiceOver/screen reader                                │
│                                                                         │
│  5. DOCUMENT                                                            │
│     └─ Update issue status in MOBILE_UX_ROADMAP.md                      │
│     └─ Include before/after screenshots in commit                       │
│                                                                         │
│  6. COMMIT                                                              │
│     └─ Reference issue ID: "fix(L1): collapse stats panel by default"   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Non-Negotiable UI/UX Requirements

| Requirement | Specification | Verification |
|-------------|---------------|--------------|
| Touch targets | ≥44×44px | Browser inspector measurement |
| Font size | ≥12px body, ≥14px preferred | Browser inspector |
| Contrast | ≥4.5:1 text, ≥3:1 UI elements | Contrast checker tool |
| Labels | All icons have labels or tooltips | Visual inspection |
| Safe areas | Respect notch, Dynamic Island, home indicator | iOS device test |
| Viewport | Primary content ≥80% during use | Screenshot measurement |
| Collision | No overlapping labels | Visual inspection at all zoom levels |

### Current UI/UX Issues

See `docs/ux/MOBILE_UX_ROADMAP.md` for complete tracking (46 issues).

---

## Testing & Quality Standards

### Pre-Commit Checklist

**EVERY commit must pass this checklist:**

```bash
# 1. All tests pass
cargo test

# 2. No clippy warnings
cargo clippy -- -D warnings

# 3. Code is formatted
cargo fmt --check

# 4. Release build works
cargo build --release

# 5. WASM build works (if WASM changes)
wasm-pack build --target web --release

# 6. Mobile Safari test (if UI changes)
# Manual test required
```

### EXPERT+ Coverage Verification (MANDATORY)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    COVERAGE VERIFICATION REQUIREMENTS                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  To claim EXPERT+ quality, coverage must be MEASURED and DOCUMENTED.        │
│  "I think the tests are good" is NOT acceptable.                            │
│  "Coverage is X% (measured by tarpaulin)" IS acceptable.                    │
│                                                                             │
│  EVERY session that adds/modifies code MUST run these verifications:        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 1. Documentation Coverage (REQUIRED)

```bash
# Must produce ZERO warnings
cargo doc --no-deps --all-features 2>&1 | grep -E "(warning|error)"

# Expected output: (empty - no warnings)
# If warnings appear, FIX THEM before committing
```

**What this verifies:**
- All public items have documentation
- No broken doc links or unclosed HTML tags
- Doc examples compile correctly

#### 2. Line Coverage Analysis (REQUIRED)

```bash
# Install cargo-tarpaulin (done by session-setup.sh)
cargo install cargo-tarpaulin

# Run coverage analysis on core library crates
# CRITICAL: Use --engine Llvm to properly trace #[inline] functions
cargo tarpaulin -p rource-math -p rource-vcs -p rource-core -p rource-render \
    --engine Llvm --out Stdout --skip-clean 2>&1 | tail -50

# Record the coverage percentage in commit messages
```

**CRITICAL: Why `--engine Llvm` is Required**

The default ptrace engine does NOT trace `#[inline]` functions, causing severe
under-reporting. This codebase uses `#[inline]` extensively for performance.

| Engine | rect.rs Coverage | vec2.rs Coverage | Overall |
|--------|------------------|------------------|---------|
| ptrace (default) | 2.2% (4/179) | 23.0% (37/161) | ~44% |
| Llvm | 84.6% (170/201) | 100% (161/161) | ~65% |

The difference is NOT measurement error - it's the ptrace engine's inability
to instrument inlined code. Always use `--engine Llvm` for accurate results.

**Coverage Targets:**

| Crate | Target | Acceptable | Notes |
|-------|--------|------------|-------|
| rource-math | 80%+ | 60%+ | Pure functions, highly testable |
| rource-vcs | 70%+ | 50%+ | Parser logic, edge cases |
| rource-core | 60%+ | 40%+ | Scene, physics, animation |
| rource-render | 50%+ | 30%+ | Some GPU code untestable |
| rource-wasm | 30%+ | 20%+ | Platform-specific code |

**What coverage analysis reveals:**
- Which lines are never executed by tests
- Which branches are not covered
- Potential dead code or untested edge cases

#### 3. Coverage Reporting Protocol

**When adding tests, ALWAYS report:**

```markdown
Coverage improvement:
- Before: X% (Y/Z lines)
- After: X% (Y/Z lines)
- Delta: +X% (N new lines covered)
```

**When modifying code, ALWAYS verify:**

```bash
# Before changes (MUST use --engine Llvm for accurate inline function coverage)
cargo tarpaulin -p <crate> --engine Llvm --out Stdout 2>&1 | grep "coverage"

# After changes
cargo tarpaulin -p <crate> --engine Llvm --out Stdout 2>&1 | grep "coverage"

# Coverage should NOT decrease
```

#### 4. Per-File Coverage Check (Optional but Recommended)

```bash
# Get detailed per-file breakdown (MUST use --engine Llvm)
cargo tarpaulin -p rource-core --engine Llvm --out Stdout 2>&1 | grep -E "^\\|\\| crates/"

# Example output:
# || crates/rource-core/src/animation/spline.rs: 93/138 +0.00%
# || crates/rource-core/src/physics/barnes_hut.rs: 51/83 +0.00%
```

#### 5. Coverage Exceptions

Some code CANNOT be covered by unit tests:

| Category | Example | Reason |
|----------|---------|--------|
| Platform-specific | WASM bindings | Requires browser runtime |
| GPU code | WebGL2 shaders | Requires GPU context |
| CLI entry points | main() | Integration test territory |
| Interactive code | Event handlers | Requires user input |

**For uncoverable code:**
- Document WHY it can't be unit tested
- Ensure it's integration tested or manually verified
- Mark with `// COVERAGE: Integration tested` comment

### Testing Requirements

| Test Type | Requirement | Status |
|-----------|-------------|--------|
| Unit tests | All public functions | Yes (2,076 tests) |
| Property tests | Math crate invariants | Yes (Implemented) |
| Chaos tests | Edge cases, unicode, boundaries | Yes (Implemented) |
| Benchmarks | Critical paths | Yes (13 benchmark suites) |
| Mutation testing | 80%+ score | TODO |
| Visual regression | Rendering consistency | TODO |
| Cross-browser | Chrome, Firefox, Safari, Edge | TODO |
| Load testing | 100k commits, 30 min | TODO |

### Determinism Requirements

For 100% deterministic output:

1. **Use fixed time step**: In headless mode, use `dt = 1.0 / framerate`
2. **Seed random generators**: Any randomness should use a fixed seed
3. **Pre-warm the scene**: Run ~30 update cycles before first render
4. **Force camera position**: Use `jump_to()` + `set_zoom()`

### Formal Verification (PEER REVIEWED PUBLISHED ACADEMIC Standard)

The project uses a **hybrid verification architecture** with both Verus and Coq
for machine-checked proofs of mathematical correctness. This dual-verification
approach provides maximum confidence suitable for top-tier academic publication.

**Verification Hierarchy:**

| Level | Name | Description | Example |
|-------|------|-------------|---------|
| 1 | TESTED | Unit tests pass | `cargo test` passes |
| 2 | BENCHMARKED | Performance measured with statistical rigor | Criterion with 95% CI |
| 3 | FORMALLY VERIFIED | Correctness proven mathematically | Verus/Coq proofs compile |
| 4 | **DUAL VERIFIED** | Proven in BOTH Verus AND Coq | Vec2, Vec3, Vec4, Mat3, Mat4 |
| 5 | **TRIPLE VERIFIED** | Dual + Kani IEEE 754 edge-case safety | All 7 primary types |
| 6 | **PUBLISHED ACADEMIC** | Suitable for PLDI/POPL/CAV review | Zero admits, reproducible |

**Verified Components:**

| Component | Verus | Coq (R-based) | Coq (Z-Compute) | Kani (CBMC) | Total | Status |
|-----------|-------|---------------|-----------------|-------------|-------|--------|
| Vec2 | 49 proof fns | 65 theorems | 50 theorems | 21 harnesses | 185 | TRIPLE VERIFIED |
| Vec3 | 40 proof fns | 71 theorems | 42 theorems | 18 harnesses | 171 | TRIPLE VERIFIED |
| Vec4 | 39 proof fns | 51 theorems | 33 theorems | 9 harnesses | 132 | TRIPLE VERIFIED |
| Mat3 | 48 proof fns | 48 theorems | 25 theorems | 14 harnesses | 135 | TRIPLE VERIFIED |
| Mat4 | 22 proof fns | 52 theorems | 25 theorems | 15 harnesses | 114 | TRIPLE VERIFIED |
| Color | 35 proof fns | 46 theorems | 28 theorems | 15 harnesses | 124 | TRIPLE VERIFIED |
| Rect | 33 proof fns | 43 theorems | 24 theorems | 13 harnesses | 113 | TRIPLE VERIFIED |
| Utils | — | 10 theorems | 8 theorems | 5 harnesses | 23 | VERIFIED |
| Complexity | — | 60 theorems | — | — | 60 | VERIFIED |
| **Total** | **266 proof fns** | **446 theorems** | **235 theorems** | **110 harnesses** | **1057** | **ACADEMIC** |

**Running Formal Verification:**

```bash
# Option 1: Use the setup + verify script (RECOMMENDED)
./scripts/setup-formal-verification.sh --verify

# Option 2: Setup tools only
./scripts/setup-formal-verification.sh

# Option 3: Manual verification

# Kani proofs (110 harnesses)
# NOTE: Running all at once may SIGSEGV. Run individually:
cargo kani -p rource-math --harness verify_lerp_no_nan

# Verus proofs (266 proof functions)
/tmp/verus/verus crates/rource-math/proofs/vec2_proofs.rs
/tmp/verus/verus crates/rource-math/proofs/vec3_proofs.rs
/tmp/verus/verus crates/rource-math/proofs/vec4_proofs.rs
/tmp/verus/verus crates/rource-math/proofs/mat3_proofs.rs
/tmp/verus/verus crates/rource-math/proofs/mat4_proofs.rs
/tmp/verus/verus crates/rource-math/proofs/color_proofs.rs
/tmp/verus/verus crates/rource-math/proofs/rect_proofs.rs

# Coq proofs (673 theorems, ~45s)
cd crates/rource-math/proofs/coq

# Layer 1: Specifications + proofs
coqc -Q . RourceMath Vec2.v Vec3.v Vec4.v Mat3.v Mat4.v Color.v Rect.v Utils.v
coqc -Q . RourceMath Vec2_Proofs.v Vec3_Proofs.v Vec4_Proofs.v
coqc -Q . RourceMath Mat3_Proofs.v Mat4_Proofs.v
coqc -Q . RourceMath Color_Proofs.v Rect_Proofs.v
coqc -Q . RourceMath Complexity.v

# Layer 2: Computational bridge (Z-based, extractable)
coqc -Q . RourceMath Vec2_Compute.v Vec3_Compute.v Vec4_Compute.v
coqc -Q . RourceMath Mat3_Compute.v Mat4_Compute.v
coqc -Q . RourceMath Color_Compute.v Rect_Compute.v Utils_Compute.v

# Layer 3: Extraction (OCaml output)
coqc -Q . RourceMath RourceMath_Extract.v
```

**Formal Verification Rules:**

| Rule | Requirement |
|------|-------------|
| Zero Admits | Never use `assume!()` (Verus) or `admit.` (Coq) |
| Complete Specs | Specifications must capture full behavior |
| Reproducibility | All proofs must verify from clean state |
| Documentation | Each theorem documented with mathematical statement |
| Dual Verification | Critical types (Vec2-4, Mat3-4) verified in BOTH Verus and Coq |
| Triple Verification | All 7 primary types additionally verified with Kani (IEEE 754 f32 edge cases) |

**Reference:**
- Overview & Index: `docs/verification/FORMAL_VERIFICATION.md`
- Verus Proofs: `docs/verification/VERUS_PROOFS.md`
- Coq Proofs: `docs/verification/COQ_PROOFS.md`
- Coverage & Limitations: `docs/verification/VERIFICATION_COVERAGE.md`
- WASM Pipeline: `docs/verification/WASM_EXTRACTION_PIPELINE.md`
- Setup Guide: `docs/verification/SETUP_GUIDE.md`
- 9-Path Survey: `docs/verification/CERTICOQ_WASM_ASSESSMENT.md`

---

## Security Standards

### Security Requirements

| Requirement | Status |
|-------------|--------|
| `cargo audit` clean | Yes (CI enforced) |
| Minimal unsafe code | Yes (1 block, documented) |
| SBOM generation | Yes (SPDX + CycloneDX) |
| Fuzzing coverage | TODO (target: 75%+) |
| SECURITY.md | Yes (vulnerability reporting process) |

### Unsafe Code Policy

- Unsafe code requires explicit justification
- Must have `// SAFETY:` comment explaining invariants
- Must be reviewed for soundness
- Current unsafe: 1 block in `webgl2/buffers.rs` (float reinterpretation)

---

## Accessibility Standards

### WCAG 2.1 AA Requirements

| Criterion | Requirement | Status |
|-----------|-------------|--------|
| 1.4.3 Contrast | ≥4.5:1 for text | TODO: Fix gray text |
| 2.1.1 Keyboard | All functionality via keyboard | TODO |
| 2.4.7 Focus Visible | Clear focus indicators | TODO |
| 2.5.5 Target Size | ≥44×44px | TODO: Many violations |

### Accessibility Checklist

For every UI change:

- [ ] All interactive elements have visible focus state
- [ ] All icons have text labels or `aria-label`
- [ ] Color is not the only way to convey information
- [ ] Contrast ratios meet WCAG AA (4.5:1 text, 3:1 UI)
- [ ] Touch targets are ≥44×44px
- [ ] Screen reader announces state changes
- [ ] Reduced motion preference is respected

---

## Documentation Standards

### Documentation Requirements

Every change must be documented:

| Change Type | Documentation Required |
|-------------|------------------------|
| Performance optimization | CHRONOLOGY.md, BENCHMARKS.md, SUCCESSFUL_OPTIMIZATIONS.md |
| UI/UX improvement | MOBILE_UX_ROADMAP.md status update |
| New feature | README.md, API docs, usage examples |
| Bug fix | Commit message with root cause |
| Architecture change | ADR in docs/adr/ (TODO) |

### Commit Message Format

```
<type>(<scope>): <description>

<body with metrics and impact>

<footer with references>
```

Examples:

```
perf(phase65): implement label collision detection

- Label overlap: 100% → 0% (collision-free)
- Performance: 847µs for 1000 labels
- Algorithm: Spatial hash with greedy placement

Addresses: T1, T5 in MOBILE_UX_ROADMAP.md

fix(L1): collapse stats panel by default on mobile

- Visualization area: 20% → 85% of viewport
- Touch target: Play button now 48×48px
- Implements iOS-style swipe-to-dismiss

Before: Stats panel covers 40% of visualization
After: Stats panel collapsed, tap to expand

Addresses: L1, L7, L8 in MOBILE_UX_ROADMAP.md
```

---

## Common Tasks

### Adding a New VCS Parser

1. Create `crates/rource-vcs/src/parser/newvcs.rs`
2. Implement the `Parser` trait
3. Register in `crates/rource-vcs/src/detect.rs`
4. Add tests (unit + property + fuzz)
5. Update documentation

### Adding a New UI Component

1. Check `docs/ux/MOBILE_UX_ROADMAP.md` for requirements
2. Design mobile-first (44px targets, 12px fonts, 4.5:1 contrast)
3. Implement with accessibility (labels, focus, ARIA)
4. Test on mobile Safari
5. Update roadmap status

### Adding a New Configuration Option

1. Add field to appropriate module in `rource-core/src/config/settings/`
2. Add CLI argument in `rource-cli/src/args/mod.rs`
3. Add environment variable in `rource-core/src/config/config_env.rs`
4. Add WASM binding in `rource-wasm/src/wasm_api/settings.rs`
5. Update documentation (README, CLAUDE.md if significant)

---

## CI/CD Pipeline

### Workflow Overview

| Workflow | Purpose |
|----------|---------|
| CI | Core quality gates (format, clippy, test, build) |
| Coverage | Code coverage with Codecov |
| Benchmarks | Performance regression detection |
| Integration | Headless rendering tests |
| Security | Audits, license checks |
| Release | Multi-platform builds, signing |

### CI Jobs

| Job | Description |
|-----|-------------|
| Format | `cargo fmt --check` |
| Clippy | All lints with `-D warnings` |
| Test | Multi-platform (Linux, macOS, Windows) |
| MSRV | Minimum Supported Rust Version (1.93) |
| Build Native | Release binary with size report |
| Build WASM | WebAssembly with gzip size check |
| Documentation | Rustdoc with warning-as-error |

### Local CI Verification

```bash
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test --all
cargo doc --no-deps --all-features
cargo build --release
```

---

## Debugging

### Native

```bash
RUST_BACKTRACE=1 cargo run
RUST_LOG=debug cargo run
```

### WASM

- Browser DevTools console
- Enable `console_error_panic_hook`
- Use `web-sys` console logging

### Mobile Safari

1. Connect iPhone to Mac
2. Safari → Develop → [Device Name] → [Page]
3. Use Web Inspector for debugging

---

## Dependencies Philosophy

We minimize external dependencies to:
- Reduce binary size
- Improve compile times
- Ensure WASM compatibility
- Avoid security surface area

### Approved Dependencies

| Crate | Reason |
|-------|--------|
| `fontdue` | Best pure-Rust font rasterizer |
| `regex-lite` | Lighter than `regex`, no PCRE |
| `chrono` | Date/time handling |
| `wasm-bindgen` | Required for WASM |
| `clap` | CLI only, feature-gated |

### Avoid

- Heavy GUI frameworks (egui, iced)
- Full `image` crate
- `tokio`/`async-std`
- `serde` for core (optional for config)

---

## Git Workflow

### Branches

| Branch | Purpose |
|--------|---------|
| `main` | Stable releases |
| `develop` | Integration branch |
| `feature/*` | New features |
| `fix/*` | Bug fixes |
| `claude/*` | AI-assisted development |

### Commit Messages

Follow conventional commits with metrics:

```
feat: add git log parser
fix: correct spline interpolation at endpoints
docs: update CLAUDE.md with Expert+ standards
perf(phase65): label collision detection
ux(L1): collapsible stats panel
a11y(A1): add icon labels
```

---

## Troubleshooting

### Common Issues

| Symptom | Cause | Solution |
|---------|-------|----------|
| Black frames | Files haven't faded in | Pre-warm scene |
| Mobile UI cramped | Desktop-first design | Follow MOBILE_UX_ROADMAP.md |
| Labels overlap | No collision detection | Implement T1 from roadmap |
| Touch doesn't work | Targets too small | Ensure ≥44×44px |
| Low contrast | Wrong colors | Use contrast checker |

### WASM Build Fails

```bash
rustup target add wasm32-unknown-unknown
wasm-pack --version  # Check version
```

---

## Reference Links

| Resource | URL |
|----------|-----|
| Original Gource | https://github.com/acaudwell/Gource |
| Rust WASM Book | https://rustwasm.github.io/docs/book/ |
| Apple HIG | https://developer.apple.com/design/human-interface-guidelines/ |
| WCAG 2.1 | https://www.w3.org/WAI/WCAG21/quickref/ |
| Material Design | https://material.io/design |

---

## Roadmap Documents

### Active Roadmaps

| Document | Purpose | Priority |
|----------|---------|----------|
| `docs/REVIEW_STANDARDS.md` | Code review requirements | Critical |
| `docs/performance/FUTURE_WORK.md` | Technical excellence roadmap | High |
| `docs/ux/MOBILE_UX_ROADMAP.md` | UI/UX excellence roadmap | Critical |

### Roadmap Priority Order

**Phase A: Critical (Current Focus)**
1. Mobile UX fixes (L1, T1, A1, I1, V1)
2. Performance regression gates (CI-1)
3. Fuzzing coverage metrics (SEC-1)
4. API stability policy (DOC-1)

**Phase B: High Priority**
5. Load testing suite (OP-3)
6. Mutation testing (TST-1)
7. Label collision detection (T1, T5)
8. Touch target fixes (A2, A3)

**Phase C-E: Subsequent Phases**
See individual roadmap documents for complete priority order.

---

## Session Best Practices

### Starting a Session

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    SESSION STARTUP CHECKLIST                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  1. RUN VERIFICATION                                                        │
│     cargo test                          # All tests must pass               │
│     cargo clippy -- -D warnings         # Zero warnings allowed             │
│     cargo fmt --check                   # Must be formatted                 │
│     cargo doc --no-deps --all-features  # Zero doc warnings                 │
│                                                                             │
│  2. READ CURRENT STATE                                                      │
│     docs/performance/CHRONOLOGY.md      # What phase are we on?             │
│     docs/performance/ALGORITHM_CANDIDATES.md  # What's next?                │
│     docs/performance/NOT_APPLICABLE.md  # What's been ruled out?            │
│                                                                             │
│  3. ESTABLISH BASELINE                                                      │
│     cargo test -p rource-wasm bench_ --release -- --nocapture               │
│     Record exact numbers BEFORE any changes                                 │
│                                                                             │
│  4. RECORD COVERAGE BASELINE (if adding/modifying code)                     │
│     cargo tarpaulin -p <crate> --engine Llvm --out Stdout | grep "coverage" │
│     Record percentage BEFORE making changes                                 │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### During a Session

| Action | Requirement |
|--------|-------------|
| Before changing hot path code | Benchmark baseline |
| After changing hot path code | Benchmark again, compare |
| Claiming an improvement | Exact % with before/after values |
| Claiming N/A status | Document WHY with evidence |
| Any optimization attempt | Update CHRONOLOGY.md with phase number |

### Ending a Session

1. **Verify clean state**:
   ```bash
   cargo test && cargo clippy -- -D warnings && cargo doc --no-deps --all-features
   ```
2. **Verify coverage (if code was added/modified)**:
   ```bash
   cargo tarpaulin -p <crate> --engine Llvm --out Stdout | grep "coverage"
   # Coverage should NOT decrease from baseline (MUST use --engine Llvm)
   ```
3. **Update documentation**: CHRONOLOGY.md, NOT_APPLICABLE.md as needed
4. **Commit with metrics**: Include exact measurements AND coverage in commit message
5. **Push to branch**: Ensure all changes are pushed

### Tips for Expert+ Quality

1. **Never trust intuition**
   - "This should be faster" is not evidence
   - The only evidence is before/after benchmarks
   - Even "obvious" improvements can regress performance

2. **Measure twice, claim once**
   - Run benchmarks multiple times
   - Ensure statistical significance (95% CI)
   - Account for measurement noise

3. **Document the negative results**
   - NOT APPLICABLE findings are valuable
   - They prevent future sessions from repeating work
   - Always explain WHY something didn't work

4. **Respect the 20 µs budget**
   - At 50,000 FPS, every nanosecond counts
   - 1 µs = 5% of frame budget
   - Small regressions compound

5. **Use the phase system**
   - Every optimization attempt gets a phase number
   - Implemented, N/A, or Failed - all get documented
   - The CHRONOLOGY is the project's optimization history

6. **Read before implementing**
   - Check NOT_APPLICABLE.md before trying an algorithm
   - Check SUCCESSFUL_OPTIMIZATIONS.md for patterns
   - Don't repeat work that's already been done

7. **Benchmark protocol**
   ```bash
   # Always do this before AND after changes:
   cargo test -p rource-wasm bench_ --release -- --nocapture 2>&1 | tee benchmark_$(date +%Y%m%d_%H%M%S).txt
   ```

### Common Pitfalls to Avoid

| Pitfall | Why It's Wrong | Correct Approach |
|---------|---------------|------------------|
| "I didn't benchmark before" | No baseline = speculation | Always baseline first |
| "The improvement is obvious" | Intuition ≠ data | Measure everything |
| "~50% faster" | Approximation | "52.3% faster (2.41µs → 1.15µs)" |
| "Works on my machine" | Not reproducible | Use criterion with CI |
| "This is a pre-existing issue" | Abdication | Fix it or document it |
| "I'll document later" | Never happens | Document as you implement |

### Performance Vocabulary

Use precise language:

| Imprecise | Precise |
|-----------|---------|
| "faster" | "52.3% reduction in execution time (2.41µs → 1.15µs)" |
| "slower" | "+15.2% regression (1.15µs → 1.32µs)" |
| "about 50%" | "52.3% (calculated from measured values)" |
| "significant improvement" | "statistically significant (p < 0.05, 95% CI)" |
| "no change" | "within noise margin (±2.1%, not statistically significant)" |

---

## Summary: The PEER REVIEWED PUBLISHED ACADEMIC Standard

Every session, every commit, every line of code must meet this standard:

| Aspect | Requirement |
|--------|-------------|
| **Performance** | Picosecond/nanosecond precision, <20µs frame budget, criterion benchmarks |
| **Measurement** | BEFORE and AFTER benchmarks mandatory, exact percentages required |
| **Formal Verification** | Verus + Coq + Kani proofs (1057 theorems/harnesses), zero admits, triple verification for Vec2-4, Mat3-4, Color, Rect |
| **UI/UX** | Mobile-first, 44px touch targets, 12px fonts, 4.5:1 contrast |
| **Testing** | All tests pass, mutations killed, cross-browser verified |
| **Security** | Audited, fuzzed, minimal unsafe, SBOM generated |
| **Accessibility** | WCAG AA, keyboard navigable, screen reader compatible |
| **Documentation** | Before/after metrics, CHRONOLOGY.md updated, phase number assigned |
| **Self-Improvement** | CLAUDE.md updated with learnings, scripts created for automation |

**The questions to ask before every commit:**

1. "Did I benchmark BEFORE making changes?"
2. "Did I benchmark AFTER making changes?"
3. "Is the improvement statistically significant?"
4. "Are the formal verification proofs still passing?"
5. "Is the documentation complete with exact metrics?"
6. "Would a reviewer at PLDI/POPL/CAV accept this?"

If the answer to ANY of these is "no," the work is not complete.

**The questions to ask before ending a session:**

1. "Did I learn anything that should be documented in CLAUDE.md?"
2. "Did I do any manual setup that should be scripted?"
3. "Did I encounter any errors that could be prevented in future sessions?"
4. "Is the Lessons Learned log updated?"

If the answer to ANY of these is "yes" and not yet done, do it before ending.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  50,000 FPS = 20 µs frame budget                                            │
│  1 µs = 5% of frame budget = 3,000 CPU cycles                               │
│  Every nanosecond matters.                                                  │
│                                                                             │
│  1057 formally verified theorems/harnesses across Verus + Coq + Kani        │
│  Zero admits. Zero compromises.                                             │
│                                                                             │
│  Never guess. Never assume. Never overstate. Always measure. Always prove.  │
│                                                                             │
│  The bar: PEER REVIEWED PUBLISHED ACADEMIC quality.                         │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

*Last updated: 2026-01-30*
*Standard: PEER REVIEWED PUBLISHED ACADEMIC (Zero Compromises)*
*Optimization Phases: 83 (see docs/performance/CHRONOLOGY.md)*
*Formal Verification: 1057 theorems/harnesses (Verus: 266, Coq R-based: 446, Coq Z-based: 235, Kani: 110)*
