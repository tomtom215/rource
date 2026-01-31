# Lessons Learned Knowledge Base

> **Purpose**: Categorized reference for every lesson learned across all development sessions.
> Updated every session. Indexed for quick AI and human lookup.
>
> **How to use**: Search by domain category or browse the chronological audit log.
> New entries go in BOTH the appropriate category AND the chronological log.

---

## Table of Contents

1. [Decision Tables (Quick Reference)](#decision-tables-quick-reference)
2. [Category: Coq Tactics & Proof Engineering](#category-coq-tactics--proof-engineering)
3. [Category: Verus / Z3 SMT Proving](#category-verus--z3-smt-proving)
4. [Category: Kani / CBMC Bounded Model Checking](#category-kani--cbmc-bounded-model-checking)
5. [Category: Floating-Point Verification](#category-floating-point-verification)
6. [Category: Tool Installation & Environment](#category-tool-installation--environment)
7. [Category: Shell Scripting & Automation](#category-shell-scripting--automation)
8. [Category: CI / Workflow Configuration](#category-ci--workflow-configuration)
9. [Category: Documentation & Metrics Automation](#category-documentation--metrics-automation)
10. [Category: Measurement & Intellectual Honesty](#category-measurement--intellectual-honesty)
11. [Category: IEEE 754 Floating-Point Edge Cases](#category-ieee-754-floating-point-edge-cases)
12. [Category: Rust Verification Landscape](#category-rust-verification-landscape)
13. [Category: Coq Extraction & WASM Pipeline](#category-coq-extraction--wasm-pipeline)
14. [Chronological Audit Log](#chronological-audit-log)

---

## Decision Tables (Quick Reference)

### Coq Tactic Selection

| Situation | Tactic | Why |
|-----------|--------|-----|
| Linear real arithmetic | `lra` | Handles `+`, `-`, `*` by constant, `<`, `<=` |
| Nonlinear real (products of variables) | `nra` | Handles variable multiplication, Rmax/Rmin products |
| Polynomial ring identity | `ring` | Handles `a*b = b*a`, `(a+b)^2 = a^2+2ab+b^2` |
| Linear integer arithmetic | `lia` | O(1) complexity bounds, integer inequalities |
| Small records (≤2 fields) | `f_equal; ring` | `f_equal` decomposes cleanly for small records |
| Large records (≥3 fields) | `apply <type>_eq; ring` per field | Avoids `f_equal` blowup on many fields |
| Mat4 16-field identity | Component decomposition (16 Local Lemmas) | `ring` times out on 48 variables at once |
| Division in goal | `set (k := a / b)` then `ring` | `ring` does not handle `/` |
| `Rmin s s` / `Rmax s s` (Coq 8.18) | `unfold Rmin; destruct (Rle_dec s s); reflexivity` | `Rmin_id`/`Rmax_id` not available |
| Constrained nonlinear (`nx²+ny²=1`) | `ring` to factor, `rewrite Hconstraint`, `ring` to close | `nra` times out on full expression |
| Sum-of-squares `0 <= (x-y)² + ...` | R: `apply Rplus_le_le_0_compat; nra.` Z: `apply Z.add_nonneg_nonneg; apply Z.square_nonneg.` | `nra`/`nia` fail with subtraction |
| Z record projections before `ring` | `cbn [field1 field2 ...]` | `simpl` destroys Z term structure |
| Never before `ring` on Z | `simpl` | Reduces Z constants to binary match expressions |
| Generic `(1+u)^n > 0` | `apply pow_lt; lra` then provide to `nra` | `nra` can't prove non-polynomial positivity |

### Verus Proof Strategy

| Situation | Strategy | Why |
|-----------|----------|-----|
| Linear arithmetic | `by(nonlinear_arith)` | Z3 handles directly |
| Degree-2 polynomial | `by(nonlinear_arith)` | Z3 handles directly |
| Degree-3+ polynomial over spec functions | 4-phase decomposition | Z3 can't expand specs inside `nonlinear_arith` |
| File exceeds Z3 resource limits | Split into base + extended files | Each file gets independent Z3 context |
| `nonlinear_arith` needs external facts | `requires fact1, fact2` clause | `by(nonlinear_arith)` has isolated context |
| Integer division roundtrip `x*k/k == x` | Explicit `assert` hint | Z3 needs help with integer division |

### Kani Harness Design

| Situation | Approach | Why |
|-----------|----------|-----|
| Default `kani::any::<f32>()` | Add `kani::assume(v.is_finite() && v.abs() < BOUND)` | NaN checks fire on unbounded symbolic f32 |
| Vec2/Vec3 dot product | `SAFE_BOUND = 1e18` | `sqrt(MAX/n)` for n components |
| Mat3 determinant | `SAFE_BOUND = 1e12` | `(MAX/k)^(1/3)` for degree-3 |
| Mat4 determinant | `SAFE_BOUND = 1e9` | `(MAX/k)^(1/4)` for degree-4 |
| `sqrt()`-based operations | Finiteness check only, not exact roundtrip | CBMC symbolic `sqrt()` extremely expensive |
| `tanf` call | Skip harness, document limitation | Kani/CBMC does not model `tanf` |
| 110+ harnesses at once | Run individually: `cargo kani --harness <name>` | Kani compiler SIGSEGV on bulk compilation |
| Harness name collision | Use descriptive suffixes: `_finite`, `_no_nan`, etc. | Duplicate symbols cause compile errors |

### Tool Selection for Verification

| Need | Tool | Status |
|------|------|--------|
| Algebraic correctness (Rust) | Verus | ADOPT (327 proofs) |
| Mathematical theorems | Coq | ADOPT (796 theorems) |
| IEEE 754 edge-case safety | Kani (CBMC) | ADOPT (134 harnesses) |
| FP error bounds | Coq + Flocq | ADOPT (99 theorems) |
| Pure functional extraction | Aeneas | MONITOR (no f32 yet) |
| Deductive FP via Why3/CVC5 | Creusot | MONITOR |
| Cryptographic integer code | hax | NOT APPLICABLE |
| Monadic shallow embedding | rocq-of-rust | NOT APPLICABLE |
| Scala-only FP | Stainless | NOT APPLICABLE |

---

## Category: Coq Tactics & Proof Engineering

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 14 | `f_equal` causes exponential blowup on large records | `f_equal` on 16-field Mat4 creates nested terms | Use `apply mat4_eq` instead; processes fields independently |
| 15 | `ring` times out on 16 simultaneous polynomial identities | 48 variables × 16 components = exponential growth | Decompose into 16 component lemmas, each proven with `ring` |
| 16 | Mat3/Mat4 tactic selection critical | Wrong tactic = 30+ min timeout; right tactic = ~6s | Established tactic guide (see Decision Table) |
| 18 | Never use `simpl` before `ring` on Z multiplication | `simpl` reduces Z constants to match expressions `ring` can't handle | Use `Z.mul_1_l` or `Z.mul_0_l` directly |
| 19 | `by` is reserved keyword in Coq 8.18 | Cannot use `by` as variable name | Use `by0` or `b_y` instead |
| 20 | `Z.square_nonneg` uses `0 <= n*n` not `n*n >= 0` | `>=` form causes unification error | Always use `0 <= n * n` form |
| 22 | Notation-overridden warnings from multi-module import | Multiple modules define same notations | `Set Warnings "-notation-overridden"` |
| 28 | `cbn [projections]` essential for Z record proofs | `simpl` reduces Z arithmetic into match expressions | Use `cbn [zm3_0 zm3_1 ...]` for only projections |
| 30 | `Local Ltac reduce_projections` encapsulates cbn pattern | Repeated `cbn [fields]` calls | Reusable tactic abbreviation |
| 49 | `simpl` + `lia` fails on Z constants like 1000 | `simpl` reduces Z constants to binary representation | Use `cbn [field_projections]` instead |
| 50 | `Z.div_mul` requires specific operand order | `Z.mul_comm` before `Z.div_mul` breaks pattern match | Use `rewrite Z.div_mul by lia` directly |
| 51 | `Z.gtb` not definitionally equal to `Z.ltb` with flipped args | Different definitions in Coq standard library | Prove `Z_gtb_ltb` using `Z.compare_antisym` |
| 52 | `zclamp_upper` requires `lo <= hi` precondition | Without it, `v > hi` and `v < lo` both possible | Add `lo <= hi` hypothesis |
| 53 | `remember` + `destruct` avoids `simpl`/`cbn` reduction issues | Complex booleans corrupt under `simpl`/`cbn` | Abstract boolean expressions before case analysis |
| 56 | `nra`/`nia` fail on sum-of-squares with subtraction | Internal `-` representation blocks solver | Factor via `Rplus_le_le_0_compat` or `Z.add_nonneg_nonneg` |
| 57 | `simpl` + `lia` fails on Z constants like 1000 | Binary representation | Use `cbn [field_projections]` |
| 58 | `simpl` + `reflexivity` fails on `x * 0 / 1000 = 0` | Partial reduction | `cbn [projections]` then `rewrite Z.mul_0_r; reflexivity` |
| 63 | `f_equal; ring` works for Vec2 records, not `apply vec2_eq; ring` | Un-reduced projections after `apply vec2_eq` | Small records (≤2 fields): `f_equal; ring`. Large: `apply <type>_eq` |
| 64 | `nra` needed for Rmax/Rmin multiplicative area proofs | `lra` cannot handle products | Use `nra` for multiplicative terms |
| 65 | Mat3 transform proofs need Vec2 type in spec | Vec2 not defined in Mat3.v | Add local `Record Vec2` + `vec2_eq` in Mat3.v |
| 66 | Mat4 `det(-A)=det(A)` for even dimension | `(-1)^4=1` | Dimension parity: odd → `-det(A)`, even → `det(A)` |
| 67 | `set` abstracts division for `ring` | `ring` can't handle `/` | `set (k := a/b)` then `f_equal; ring` |
| 68 | `Rmin_id`/`Rmax_id` not in Coq 8.18 | Missing standard library lemma | `unfold Rmin; destruct (Rle_dec s s); reflexivity` |
| 69 | ring+rewrite decomposition for constrained proofs | `ring` can't handle constraints; `nra` times out | Factor with `ring`, `rewrite`, `ring` to close |
| 118 | `sqrt_Rsqr` is a direct lemma, not rewrite | Takes hypothesis as argument | `exact (sqrt_Rsqr x Hx)` not `rewrite sqrt_Rsqr; assumption` |
| 119 | `nlra` doesn't exist in Coq 8.18 | Nonlinear real is `nra` | `Require Import Psatz.` then use `nra` |
| 122 | `Require Import` is NOT `Require Export` | `FP_Common.v` imports don't re-export | Files must explicitly import what they need |
| 123 | `field` may close all subgoals in Coq 8.18 | Side conditions auto-discharged | Use `field.` alone or `field; lra.` (semicolon) |
| 124 | FP error composition follows inductive multiplication pattern | `(1+e1)*...*(1+en) - 1` decomposes as `(prefix-1)*(1+en) + en` | Factor, `Rabs_triang`, `Rabs_mult`, IH, then `ring`+`Rplus_le_compat` |

---

## Category: Verus / Z3 SMT Proving

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 59 | **BREAKTHROUGH**: `by(nonlinear_arith)` requires-axiom pattern | Z3 can't expand spec functions inside `nonlinear_arith` | 4-phase decomposition: expand specs in outer context, assert expanded forms, prove pairwise commutativity, close with `requires` |
| 60 | `by(nonlinear_arith)` has isolated context | Does NOT inherit outer proof facts | Always use `requires fact1, fact2, ...` |
| 61 | File splitting for Z3 resource management | Combined file exceeded Z3 resource limits | Split into base + extended files; each verifies independently |
| 62 | Never remove theorems as "Z3-intractable" | Violates academic standards | Decompose further; if truly blocked, document with tracking issue |
| 81 | `det(A*B)=det(A)*det(B)` provable with `ring` for Mat3 AND Mat4 | Scalar identity, not matrix identity | `ring` handles directly even for Mat4 (32 vars, degree 4, ~8s) |
| 112 | New Verus files must be added to counting script | `mat4_extended_proofs.rs` was not counted | Add variable + sum + SETUP_GUIDE.md sed patterns |
| 113 | 4-phase decomposition generalizes to Mat4 | `det(diag(d0,d1,d2,d3)) = d0*d1*d2*d3` is degree-4 | Expand minors as let bindings, assert in outer context |
| 114 | Mat4 T*S composite determinant needs all 16 elements + 12 minors | Both `mat4_mul` and `mat4_determinant` must be expanded | Assert all 16 elements + 12 Laplace minors; most are zero (sparse) |
| 115 | `dst.r * 1000 / 1000 == dst.r` not automatic for Z3 | Integer division truncation needs hint | Explicit `assert` per component |

---

## Category: Kani / CBMC Bounded Model Checking

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 82 | Kani is only Rust tool with bit-precise FP verification | CBMC-based bounded model checker | ADOPT as Layer 2 for edge-case safety |
| 87 | `#[cfg(kani)]` requires workspace `check-cfg` | `cargo check` warns on unexpected cfg | Add `check-cfg = ['cfg(kani)']` to workspace lints |
| 88 | Kani has built-in NaN checks on every float operation | Default checks fire on unbounded `kani::any()` | Use `kani::assume(v.is_finite() && v.abs() < SAFE_BOUND)` |
| 91 | Kani does not support C `tanf` foreign function | `Mat4::perspective()` calls `f32::tan()` | Remove perspective harness; verify algebraically |
| 92 | Kani models `sinf`/`cosf` but not `tanf` | CBMC math stubs are partial | Transcendental coverage is partial |
| 93 | Mat4 determinant harness takes ~60s | 16 symbolic floats × 80 CBMC checks | Plan for CI timeout; most harnesses verify in <2s |
| 94 | `cargo kani setup` installs nightly-2025-11-21 | Kani needs its own Rust nightly | Does not conflict with dev toolchain |
| 95 | Safe bounds vary by operation depth | `sqrt(MAX/n)` for dot; `(MAX/k)^(1/d)` for degree-d | Vec: 1e18, Mat3 det: 1e12, Mat4 det: 1e9 |
| 96 | Kani SIGSEGV when compiling 110+ harnesses at once | Compiler memory issue | Run individually: `cargo kani --harness <name>` |
| 100 | 65 new harnesses scale well across 7 types | Same patterns apply uniformly | Standard templates: `verify_<type>_<op>_finite`, etc. |
| 116 | Harness name collisions cause compile errors | Duplicate symbols | Use descriptive suffixes |

---

## Category: Floating-Point Verification

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 74 | Stainless FP paper not applicable to rource-math | Scala-only; Z3 worst at FP (78-85%) | Confirms Coq+Flocq+VCFloat2 is better path |
| 75 | Coq FP ecosystem all Coq 8.18 compatible | Flocq 4.1.3, VCFloat2 2.1.1, Gappa 1.5.4, CoqInterval 4.8.1 | Use Coq Platform 8.18 packages |
| 76 | FP proofs prove error bounds, not algebraic properties | Complementary to R-based proofs | Two-layer: R (correctness) + FP (accuracy) |
| 77 | ~46 of 114 FP ops immediately achievable | sqrt, rounding, min/max/abs/clamp, lerp well-studied | Phase FP-1 reaches ~70% coverage |
| 78 | LAProof verifies FP matrix-vector products | Princeton/VeriNum ARITH 2023 | Applicable to Mat3/Mat4 transforms |
| 79 | Z3 is weakest SMT solver for FP | 78-85% vs cvc5 89-100% | Portfolio solving needed if Verus adds FP |
| 80 | No existing HSL color space formalization | Surveyed all proof assistants | Novel proof engineering; lowest FP priority |
| 117 | Flocq 4.1.3 buildable from source despite opam 503 | GitLab INRIA tarball | Exclude `Nat2Z_8_12.v` (compat file for Coq < 8.14) |
| 120 | `(1+u)^n - 1 <= 2*n*u` FALSE for large `u` and `n >= 4` | Bound needs small `u` | `u <= 1/8` for n=4,5 |
| 121 | `nra` needs `pow_lt` hint for generic `(1+u)^n` | Not polynomial | `apply pow_lt; lra` then provide to `nra` |
| 125 | 99 Flocq-based FP theorems machine-checked | Phase FP-1 foundations | 4 files: FP_Common, FP_Rounding, FP_ErrorBounds, FP_Vec |

---

## Category: IEEE 754 Floating-Point Edge Cases

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 89 | `lerp(f32::MAX, -f32::MAX, 0.0)` produces NaN | `(b-a)` overflows to `-inf`; `-inf * 0.0 = NaN` | Require bounded inputs; `SAFE_BOUND = 1e18` |
| 90 | `Vec2::project()` NaN for denormalized onto vectors | `dot / length_squared` overflows for denormals | Require `onto.length_squared() > f32::MIN_POSITIVE` |
| 97 | `Rect::intersects(self)` fails when `width < ULP(x)` | `x + width > x` FALSE when width < ULP | Require `width > 1.0` and `|x| < 1e6` |
| 98 | `Rect::from_center_size` center roundoff | Catastrophic cancellation when `|cx| >> w` | Tighten bounds; tolerance 1.0 |
| 99 | CBMC symbolic `sqrt()` extremely expensive | >15 min for symbolic sqrt verification | Finiteness checks only; exact roundtrips via Verus/Coq |

---

## Category: Tool Installation & Environment

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 6 | coq-of-rust incompatible with Rust 1.93 | Requires older nightly | Manual Coq specs instead |
| 8 | No automated Verus/Coq setup | Tools required manual installation | Created `scripts/setup-formal-verification.sh` |
| 9 | Coq installation via apt needs `coq-theories` | apt only installs `coqc` without theories | `apt-get install -y coq coq-theories` |
| 11 | Network issues can block apt-get | Transient DNS failures | Retry with exponential backoff |
| 32 | MetaCoq blocked by Coq opam repo HTTP 503 | Repository infra intermittently unavailable | Try alternative sources or GitHub pins |
| 34 | MetaCoq buildable from source despite opam 503 | All opam repos return 503 | Clone from GitHub, pin coq-equations from source |
| 35 | coq-equations pinnable from GitHub source | opam pin bypasses broken infra | `opam pin add coq-equations "git+https://github.com/mattam82/Coq-Equations.git#v1.3-8.18"` |
| 36 | MetaCoq coq-8.18 branch != MetaRocq/rocq-verified-extraction | rocq-verified-extraction requires 8.19+ | Use `MetaCoq/metacoq#coq-8.18` |
| 38 | `libgmp-dev` required for zarith/MetaCoq build | zarith needs GMP dev headers | `apt-get install -y libgmp-dev` |
| 39 | Coq renamed to Rocq Prover (v9.0, March 2025) | Official rebranding | Stay on Coq 8.18; migrate to Rocq 9.x later |
| 40 | Both Coq AND Rocq opam repos return HTTP 503 | Infrastructure issue | Use `opam.ocaml.org` + GitHub pins |
| 41 | MetaCoq → MetaRocq rename (v1.4 for Rocq 9.0) | Namespace change | Coq 8.18: MetaCoq branch. Rocq 9.x: MetaRocq |
| 42 | rocq-core 9.1.0 available on opam.ocaml.org | Default opam repo has Rocq | `opam pin add rocq-prover 9.0.0` works |
| 43 | MetaRocq 1.4.1 is latest (Dec 2024, Rocq 9.1) | GitHub releases per Rocq target | Check releases page for version compat |
| 44 | MetaCoq built from source bypasses opam 503 | 8 components build in ~30 min | Build order: utils→common→template-coq→pcuic→template-pcuic→safechecker→erasure→erasure-plugin |
| 45 | apt Coq vs opam Coq .vo file inconsistency | .vo compiled with different Coq installations incompatible | `rm -f *.vo *.vos *.vok *.glob` then recompile with `eval $(opam env)` |
| 46 | `make install` for MetaCoq takes ~15-20 min | Builds quotation theories | Budget time; monitor with verbose output |
| 47 | Recompilation order matters for Coq .vo files | Layer dependencies: specs → proofs → compute → extraction | Always recompile in order |
| 48 | `verify_coq_proofs()` has 4 layers | Each depends on prior; MetaCoq layer optional | Layer 4 is not a failure if unavailable |
| 73 | `RUSTUP_TOOLCHAIN=nightly-2024-12-07` for rocq-of-rust | Uses rustc internals | Set env var + `LD_LIBRARY_PATH` |

---

## Category: Shell Scripting & Automation

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 37 | Setup scripts must pass shellcheck | Subtle bugs in shell scripts | `bash -n` + `shellcheck --severity=info` before commit |
| 101 | GNU sed only supports POSIX ERE | `(?!...)`, `(?=...)`, `\b` not available | Never use Perl-style features; use context anchoring |
| 102 | `local` keyword only valid inside bash functions | `local VAR=...` at top-level is error | Use plain `VAR=...` outside functions |
| 103 | Context-aware sed patterns prevent cross-contamination | Generic `s/[0-9]+/NEW/` matches wrong numbers | Use line-context anchors with unique surrounding text |
| 104 | Idempotency verification essential | Double-run may corrupt if patterns match own output | Test: `./script.sh && ./script.sh && ./script.sh --check` |
| 111 | Per-file sed patterns scale linearly but are necessary | 23 patterns for SETUP_GUIDE.md | No shortcuts; generic patterns cause cross-contamination |

---

## Category: CI / Workflow Configuration

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 7 | Windows CI benchmark timeout | Threshold too tight for CI variability | Increased threshold 100µs→150µs |
| 105 | Cargo package names differ from directory names | `rource-cli/` has package name `rource` | Check `Cargo.toml` `[package] name`; `-p` uses package name |
| 129 | `cargo bench --workspace` fails with `--noplot` | Binary targets use default harness, not criterion | Add `--benches` flag: `cargo bench --workspace --benches -- --noplot` |
| 130 | Mutation testing timeout too low for CI | Complex mutants need >60s on CI runners | Default timeout 60s→120s in `mutation.yml` |
| 131 | Feature-gated modules skip clippy unless `--all-features` | `cache` module behind `#[cfg(feature = "cache")]` | Always run `cargo clippy --all-targets --all-features -- -D warnings` |
| 132 | Display format hex vs decimal causes cross-platform test failure | `CacheError::RepositoryMismatch` formats `{:016x}` | Test assertions must match actual Display format, not assumed format |
| 133 | Docker Trivy scanning 138 OS-level CVEs from `debian:trixie-slim` | `runtime-with-git` pulls git + transitive deps (openldap, pam, ncurses, curl, etc.) | Switch default Docker target to `runtime-distroless` (cc-debian13); git stage opt-in |
| 134 | NEVER dismiss security alerts as "pre-existing" or "base image issue" | Assumption that alerts auto-resolve proved wrong | Fix root cause: minimize attack surface; never assume issues resolve themselves |
| 137 | Docker glibc version mismatch: build vs runtime | Builder on Trixie (glibc 2.39) + distroless cc-debian12 (glibc 2.36) = `GLIBC_2.39 not found` | All stages must use same Debian generation; upgrade distroless to cc-debian13 |

---

## Category: Documentation & Metrics Automation

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 106 | Rounded display strings resist minor fluctuations | "2700+" stays valid across small changes | Rounded form + `+` suffix for display; exact in JSON |
| 107 | Peripheral docs need same automation as primary docs | SETUP_GUIDE.md, etc. had stale counts | Automation must cover ALL files with metrics |
| 108 | Documentation drift inevitable without CI enforcement | Counts go stale within a single session | CI must enforce `--check` mode on both scripts |
| 109 | Two-tier script architecture for doc automation | Verification counts vs other metrics need different extraction | `update-verification-counts.sh` + `update-doc-metrics.sh` |
| 110 | Ground truth must come from source files | Hardcoded counts go stale immediately | Parse actual source: `grep -cE` patterns |

---

## Category: Measurement & Intellectual Honesty

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 1 | Timing variations reported as perf improvements | Module refactoring doesn't affect binary | Added "Invalid Performance Claims" table |
| 2 | "10% is noise" at picosecond scale | Wrong precision assumptions | "Measurement Precision at Scale" section |
| 3 | Low coverage blamed on tarpaulin | Excuse instead of investigation | Added `--engine Llvm` requirement |
| 55 | **STANDARDS VIOLATION**: Coq proofs committed without machine-checking | Coq was not installed | NEVER commit proofs without `coqc`. Install tools FIRST. |

---

## Category: Rust Verification Landscape

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 71 | rocq-of-rust generates monadic embedding, not algebraic specs | Models memory, not math | NOT VIABLE for rource-math |
| 72 | rocq-of-rust requires Rocq 9.0 + nightly-2024-12-07 | Rocq 9.0 vs our Coq 8.18 | Two blockers: opam infra + version mismatch |
| 83 | Aeneas produces pure functional code (not monadic) | MIR → LLBC → pure lambda calculus | MONITOR pending f32 support |
| 84 | Creusot leverages Why3 with comprehensive ieee_float theory | Why3 Float32/Float64 axiomatize full IEEE 754 | MONITOR for FP deductive verification |
| 85 | hax backends do NOT support floating-point | Designed for cryptographic integer code | NOT APPLICABLE for rource-math |
| 86 | 8 Rust verification tools now surveyed | Verus, Coq, Kani, Aeneas, Creusot, hax, rocq-of-rust, Stainless | Full landscape in RUST_VERIFICATION_LANDSCAPE.md |

---

## Category: Coq Extraction & WASM Pipeline

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 17 | CertiCoq-WASM requires Coq 8.20; R type non-extractable | Pinned to 8.20+; Reals are axiomatized | Layered arch: R-abstract + Z-computational + extraction |
| 21 | R and Z share commutative ring properties | Both are commutative rings | Z proofs mirror R proofs algebraically |
| 23 | wasm_of_ocaml is production-ready | v6.2.0, used by Jane Street | Path 1 (production) for Coq-to-WASM |
| 24 | MetaCoq Verified Extraction works with Coq 8.18 | PLDI'24 Distinguished Paper | Path 2 (academic) for partially verified extraction |
| 25 | 9 distinct Coq-to-WASM paths exist (3 viable today) | Comprehensive survey | Documented in CERTICOQ_WASM_ASSESSMENT.md |
| 26 | coq-rust-extraction needs Coq 8.20+ | v0.1.1 (May 2025) | Deferred; interesting but wrong Coq version |
| 27 | WasmGC vs linear memory for extracted code | wasm_of_ocaml uses WasmGC (Chrome 119+, Firefox 122+, Safari 18.2+) | Ideal for pure functional Coq-extracted code |
| 29 | Component decomposition scales to Mat4 over Z | Same pattern as R-based proofs | 16 Local Lemmas for mul_assoc over Z |
| 31 | ExtrOcamlZInt maps Z to native int | Default is arbitrary-precision | `Require Import ExtrOcamlZInt` for efficiency |
| 33 | OCaml record syntax needed for matrix constructors | Coq constructors don't extract as functions | Use `{ zm3_0 = 1; ... }` syntax in test driver |

---

## Chronological Audit Log

All 123 entries in chronological order. Entry numbers match category table references.

| # | Date | Session | Issue | Root Cause | Fix Applied |
|---|------|---------|-------|-----------|-------------|
| 1 | 2026-01-28 | - | Timing variations reported as perf improvements | Module refactoring doesn't affect binary | Added "Invalid Performance Claims" table |
| 2 | 2026-01-28 | - | "10% is noise" at picosecond scale | Wrong precision assumptions | Replaced with "Measurement Precision at Scale" |
| 3 | 2026-01-28 | - | Low coverage blamed on tarpaulin | Excuse instead of investigation | Added `--engine Llvm` requirement |
| 4 | 2026-01-28 | WBhqf | coq-of-rust incompatible with Rust 1.93 | Tool requires older nightly | Manual Coq specs; documented in FORMAL_VERIFICATION.md |
| 5 | 2026-01-28 | WBhqf | Windows CI benchmark timeout | Threshold too tight for CI variability | Increased threshold 100µs→150µs |
| 6 | 2026-01-28 | WBhqf | No automated Verus/Coq setup | Tools required manual installation | Created scripts/setup-formal-verification.sh |
| 7 | 2026-01-28 | SD81W | Coq installation via apt needs coq-theories | apt-get only installs coqc without theories | Use `apt-get install -y coq coq-theories` |
| 8 | 2026-01-28 | SD81W | Mat3/Mat4 Coq proofs follow Vec2/Vec3/Vec4 pattern | Manual Coq specs work well | Added Mat3.v, Mat4.v, Mat3_Proofs.v, Mat4_Proofs.v (44 new theorems) |
| 9 | 2026-01-28 | SD81W | Network issues can block apt-get | Transient DNS failures | Script should retry with exponential backoff |
| 10 | 2026-01-28 | 4sbzk | ICC complexity proofs simpler for fixed-size types | Constant cost regardless of input values | Created Complexity.v with 60 theorems |
| 11 | 2026-01-28 | 4sbzk | Coq lia tactic sufficient for O(1) bounds | Simple constant-cost proofs | Used `lia` for all complexity bounds |
| 12 | 2026-01-29 | 4sbzk | `f_equal` causes exponential blowup on large records | 16-field Mat4 nested terms | Use `apply mat4_eq`; processes fields independently |
| 13 | 2026-01-29 | 4sbzk | `ring` times out on 16 simultaneous polynomial identities | 48 variables × 16 components | 16 component lemmas, each proven with `ring` |
| 14 | 2026-01-29 | 4sbzk | Coq tactic selection critical for Mat4 proofs | Wrong tactic = timeout | Established tactic guide |
| 15 | 2026-01-29 | EnuTg | CertiCoq-WASM requires Coq 8.20, R type non-extractable | Pinned to >= 8.20; Reals axiomatized | Layered architecture: R + Z + extraction |
| 16 | 2026-01-29 | EnuTg | Never use `simpl` before `ring` on Z multiplication | Reduces to match expressions | Use `Z.mul_1_l` or `Z.mul_0_l` directly |
| 17 | 2026-01-29 | EnuTg | `by` is reserved keyword in Coq 8.18 | Cannot use as variable name | Use `by0` or `b_y` |
| 18 | 2026-01-29 | EnuTg | Z.square_nonneg uses `0 <= n*n` not `n*n >= 0` | Different comparison direction | Always use `0 <= n * n` form |
| 19 | 2026-01-29 | EnuTg | R and Z share commutative ring properties | Both are commutative rings | Z proofs mirror R proofs |
| 20 | 2026-01-29 | EnuTg | Notation-overridden warnings from multi-module import | Multiple modules define same notations | `Set Warnings "-notation-overridden"` |
| 21 | 2026-01-29 | EnuTg | wasm_of_ocaml is production-ready | v6.2.0, used by Jane Street | Path 1 (production) for Coq-to-WASM |
| 22 | 2026-01-29 | EnuTg | MetaCoq Verified Extraction works with Coq 8.18 | PLDI'24 Distinguished Paper | Path 2 (academic) |
| 23 | 2026-01-29 | EnuTg | 9 distinct Coq-to-WASM paths exist | Comprehensive survey | Documented in CERTICOQ_WASM_ASSESSMENT.md |
| 24 | 2026-01-29 | EnuTg | coq-rust-extraction needs Coq 8.20+ | v0.1.1 (May 2025) | Deferred |
| 25 | 2026-01-29 | EnuTg | WasmGC vs linear memory for extracted code | wasm_of_ocaml uses WasmGC | Ideal for pure functional code |
| 26 | 2026-01-29 | T2LcJ | `cbn [projections]` essential for Z record proofs | `simpl` reduces Z arithmetic | Use `cbn [zm3_0 zm3_1 ...]` |
| 27 | 2026-01-29 | T2LcJ | Component decomposition scales to Mat4 over Z | Same pattern as R-based proofs | 16 Local Lemmas for mul_assoc |
| 28 | 2026-01-29 | T2LcJ | `Local Ltac reduce_projections` encapsulates cbn | Repeated `cbn` calls | Reusable tactic abbreviation |
| 29 | 2026-01-29 | T2LcJ | ExtrOcamlZInt maps Z to native int | Default is arbitrary-precision | `Require Import ExtrOcamlZInt` |
| 30 | 2026-01-29 | T2LcJ | MetaCoq blocked by Coq opam repo HTTP 503 | Repository infra unavailable | Try alternative sources |
| 31 | 2026-01-29 | T2LcJ | OCaml record syntax needed for matrix constructors | Constructors don't extract as functions | Use `{ zm3_0 = 1; ... }` syntax |
| 32 | 2026-01-29 | T2LcJ | MetaCoq buildable from source despite opam 503 | All repos return 503 | Clone from GitHub, pin deps from source |
| 33 | 2026-01-29 | T2LcJ | coq-equations pinnable from GitHub source | opam pin bypasses broken infra | `opam pin add coq-equations "git+..."` |
| 34 | 2026-01-29 | T2LcJ | MetaCoq coq-8.18 branch != MetaRocq/rocq-verified-extraction | Different requirements | Use `MetaCoq/metacoq#coq-8.18` |
| 35 | 2026-01-29 | T2LcJ | Setup scripts must pass shellcheck | Subtle shell bugs | `bash -n` + `shellcheck --severity=info` |
| 36 | 2026-01-29 | T2LcJ | `libgmp-dev` required for zarith/MetaCoq | zarith needs GMP headers | `apt-get install -y libgmp-dev` |
| 37 | 2026-01-29 | T2LcJ | Coq renamed to Rocq Prover (v9.0) | Official rebranding | Stay on Coq 8.18; migrate later |
| 38 | 2026-01-29 | T2LcJ | Both Coq AND Rocq opam repos return HTTP 503 | Infrastructure issue | Use `opam.ocaml.org` + GitHub pins |
| 39 | 2026-01-29 | T2LcJ | MetaCoq → MetaRocq rename (v1.4) | Namespace change | Coq 8.18: MetaCoq branch |
| 40 | 2026-01-29 | T2LcJ | rocq-core 9.1.0 available on opam.ocaml.org | Default repo has Rocq | `opam pin add rocq-prover 9.0.0` |
| 41 | 2026-01-29 | T2LcJ | MetaRocq 1.4.1 is latest (Dec 2024) | Per Rocq target | Check releases page |
| 42 | 2026-01-29 | T2LcJ | MetaCoq built from source bypasses opam 503 | 8 components, ~30 min | Document build order |
| 43 | 2026-01-29 | T2LcJ | apt Coq vs opam Coq .vo file inconsistency | Different installations incompatible | `rm -f *.vo` then recompile with `eval $(opam env)` |
| 44 | 2026-01-29 | T2LcJ | `make install` for MetaCoq takes ~15-20 min | Builds quotation theories | Budget time accordingly |
| 45 | 2026-01-29 | T2LcJ | Recompilation order matters for .vo files | Layer dependencies | Always recompile in order |
| 46 | 2026-01-29 | T2LcJ | `verify_coq_proofs()` has 4 layers | Each depends on prior | MetaCoq layer is optional |
| 47 | 2026-01-29 | fqYWd | `simpl` destroys Z term structure for `lia`/`ring` | Reduces to match expressions | `cbn -[Z.mul Z.div Z.add Z.sub]` |
| 48 | 2026-01-29 | fqYWd | `Z.div_mul` requires specific operand order | `Z.mul_comm` breaks pattern | `rewrite Z.div_mul by lia` directly |
| 49 | 2026-01-29 | fqYWd | `Z.gtb` not definitionally equal to `Z.ltb` flipped | Different definitions | Prove `Z_gtb_ltb` using `Z.compare_antisym` |
| 50 | 2026-01-29 | fqYWd | `zclamp_upper` requires `lo <= hi` precondition | Unordered bounds allow contradictions | Add `lo <= hi` hypothesis |
| 51 | 2026-01-29 | fqYWd | `remember` + `destruct` avoids reduction issues | Complex booleans corrupt | Abstract before case analysis |
| 52 | 2026-01-29 | fqYWd | Color/Rect/Utils verification scales well | Same layered architecture works | +114 theorems, all 0 admits |
| 53 | 2026-01-29 | KuTgE | **VIOLATION**: Coq proofs committed without machine-checking | Coq not installed | NEVER commit proofs without `coqc` |
| 54 | 2026-01-29 | KuTgE | `nra`/`nia` fail on sum-of-squares with subtraction | Internal `-` blocks solver | Factor via `Rplus_le_le_0_compat` |
| 55 | 2026-01-29 | KuTgE | `simpl` + `lia` fails on Z constants like 1000 | Binary representation | `cbn [field_projections]` |
| 56 | 2026-01-29 | KuTgE | `simpl` + `reflexivity` fails on `x * 0 / 1000 = 0` | Partial reduction | `cbn [projections]` then `rewrite Z.mul_0_r` |
| 57 | 2026-01-29 | fqynP | **BREAKTHROUGH**: `by(nonlinear_arith)` requires-axiom pattern | Z3 can't expand specs in `nonlinear_arith` | 4-phase decomposition |
| 58 | 2026-01-29 | fqynP | `by(nonlinear_arith)` has isolated context | No inheritance from outer proof | Always use `requires` clause |
| 59 | 2026-01-29 | fqynP | Verus file splitting for Z3 resource management | Combined file exceeded limits | Split into base + extended files |
| 60 | 2026-01-29 | fqynP | Never remove theorems as "Z3-intractable" | Violates academic standards | Decompose further |
| 61 | 2026-01-29 | vXZ54 | `f_equal; ring` works for Vec2, not `apply vec2_eq; ring` | Un-reduced projections | Small: `f_equal; ring`. Large: `apply <type>_eq` |
| 62 | 2026-01-29 | vXZ54 | `nra` needed for Rmax/Rmin multiplicative proofs | `lra` can't handle products | Use `nra` |
| 63 | 2026-01-29 | vXZ54 | Mat3 transform proofs need Vec2 type in spec | Vec2 not in Mat3.v | Add local `Record Vec2` in Mat3.v |
| 64 | 2026-01-29 | vXZ54 | Mat4 det(-A)=det(A) for even dimension | (-1)^4=1 | Dimension parity matters |
| 65 | 2026-01-30 | wj6WE | `set` abstracts division for `ring` | `ring` can't handle `/` | `set (k := a/b)` then `f_equal; ring` |
| 66 | 2026-01-30 | wj6WE | `Rmin_id`/`Rmax_id` not in Coq 8.18 | Missing lemma | `unfold Rmin; destruct (Rle_dec s s); reflexivity` |
| 67 | 2026-01-30 | wj6WE | ring+rewrite decomposition for constrained proofs | `ring` can't handle constraints | Factor, `rewrite`, `ring` |
| 68 | 2026-01-30 | wj6WE | 50% operations formally verified milestone | +23 operations across types | 115/230 operations, 939 theorems |
| 69 | 2026-01-30 | wj6WE | rocq-of-rust generates monadic embedding | Models memory, not math | NOT VIABLE for rource-math |
| 70 | 2026-01-30 | wj6WE | rocq-of-rust requires Rocq 9.0 + nightly-2024-12-07 | Version mismatch + opam 503 | Two blockers |
| 71 | 2026-01-30 | wj6WE | `RUSTUP_TOOLCHAIN=nightly-2024-12-07` for rocq-of-rust | Uses rustc internals | Set env var + `LD_LIBRARY_PATH` |
| 72 | 2026-01-30 | 9ENKM | Stainless FP paper not applicable | Scala-only; Z3 worst at FP | Confirms Coq+Flocq path |
| 73 | 2026-01-30 | 9ENKM | Coq FP ecosystem all Coq 8.18 compatible | Platform packages | Flocq, VCFloat2, Gappa, CoqInterval |
| 74 | 2026-01-30 | 9ENKM | FP proofs prove error bounds, not algebraic properties | Complementary layers | Two-layer: R + FP |
| 75 | 2026-01-30 | 9ENKM | ~46 of 114 FP ops immediately achievable | Well-studied operations | Phase FP-1 reaches ~70% coverage |
| 76 | 2026-01-30 | 9ENKM | LAProof verifies FP matrix-vector products | Princeton ARITH 2023 | Applicable to Mat3/Mat4 transforms |
| 77 | 2026-01-30 | 9ENKM | Z3 is weakest SMT solver for FP | 78-85% success rate | Portfolio solving if Verus adds FP |
| 78 | 2026-01-30 | 9ENKM | No existing HSL color space formalization | Surveyed all tools | Novel proof engineering; lowest priority |
| 79 | 2026-01-30 | 9ENKM | det(A*B)=det(A)*det(B) with `ring` for Mat3 AND Mat4 | Scalar identity | Direct `ring`; ~8s for Mat4 |
| 80 | 2026-01-30 | 9ENKM | Kani is only Rust tool with bit-precise FP | CBMC-based | ADOPT as Layer 2 |
| 81 | 2026-01-30 | 9ENKM | Aeneas produces pure functional code | MIR → LLBC → lambda calc | MONITOR pending f32 |
| 82 | 2026-01-30 | 9ENKM | Creusot leverages Why3 ieee_float theory | Comprehensive axiomatization | MONITOR for FP via CVC5 |
| 83 | 2026-01-30 | 9ENKM | hax backends do NOT support floating-point | Designed for crypto | NOT APPLICABLE |
| 84 | 2026-01-30 | 9ENKM | 8 Rust verification tools surveyed | Comprehensive landscape | RUST_VERIFICATION_LANDSCAPE.md |
| 85 | 2026-01-30 | 9ENKM | `#[cfg(kani)]` requires workspace check-cfg | `cargo check` warns | Add to `[workspace.lints.rust]` |
| 86 | 2026-01-30 | 9ENKM | Kani has built-in NaN checks on every float op | Fires on unbounded `kani::any()` | `kani::assume(v.is_finite())` |
| 87 | 2026-01-30 | 9ENKM | `lerp(MAX, -MAX, 0.0)` produces NaN | Intermediate overflow | Require bounded inputs |
| 88 | 2026-01-30 | 9ENKM | `Vec2::project()` NaN for denormalized vectors | `dot / length_squared` overflows | Require `> f32::MIN_POSITIVE` |
| 89 | 2026-01-30 | 9ENKM | Kani does not support `tanf` | CBMC math stubs partial | Skip harness; verify algebraically |
| 90 | 2026-01-30 | 9ENKM | Kani models `sinf`/`cosf` but not `tanf` | Partial stubs | Transcendental coverage partial |
| 91 | 2026-01-30 | 9ENKM | Mat4 det harness takes ~60s | 16 symbolic floats | Plan CI timeout |
| 92 | 2026-01-30 | 9ENKM | `cargo kani setup` installs nightly-2025-11-21 | Own Rust nightly | No conflict with dev toolchain |
| 93 | 2026-01-30 | 9ENKM | Safe bounds vary by operation depth | sqrt(MAX/n) formula | Vec: 1e18, Mat3: 1e12, Mat4: 1e9 |
| 94 | 2026-01-30 | 9qF3t | Kani SIGSEGV on 110+ harnesses | Compiler memory issue | Run individually |
| 95 | 2026-01-30 | 9qF3t | `Rect::intersects(self)` fails when `width < ULP(x)` | `x + width > x` false | Require `width > 1.0`, `|x| < 1e6` |
| 96 | 2026-01-30 | 9qF3t | `Rect::from_center_size` center roundoff | Catastrophic cancellation | Tighten bounds; tolerance 1.0 |
| 97 | 2026-01-30 | 9qF3t | CBMC symbolic `sqrt()` extremely expensive | >15 min for symbolic sqrt | Finiteness checks only |
| 98 | 2026-01-30 | 9qF3t | 65 new Kani harnesses scale well | Same patterns apply | Standard templates |
| 99 | 2026-01-30 | 9qF3t | GNU sed only supports POSIX ERE | No Perl-style features | Context anchoring instead |
| 100 | 2026-01-30 | 9qF3t | `local` only valid inside bash functions | Function-scoped only | Plain `VAR=...` at top level |
| 101 | 2026-01-30 | 9qF3t | Context-aware sed prevents cross-contamination | Generic patterns match wrong numbers | Line-context anchors |
| 102 | 2026-01-30 | 9qF3t | Idempotency verification essential | Double-run may corrupt | Test `./script.sh && ./script.sh && --check` |
| 103 | 2026-01-30 | 9qF3t | Cargo package names differ from directory names | `-p` uses package name | Check `Cargo.toml [package] name` |
| 104 | 2026-01-30 | 9qF3t | Rounded display strings resist fluctuations | "2700+" stays valid | Rounded for display; exact in JSON |
| 105 | 2026-01-30 | 9qF3t | Peripheral docs need same automation | SETUP_GUIDE.md had stale counts | All files in `--check` |
| 106 | 2026-01-30 | 9qF3t | Documentation drift inevitable without CI | Counts stale within single session | CI enforcement mandatory |
| 107 | 2026-01-30 | 9qF3t | Two-tier script architecture | Different extraction needed | verification-counts + doc-metrics |
| 108 | 2026-01-30 | 9qF3t | Ground truth from source files | Hardcoded counts stale | Parse with `grep -cE` |
| 109 | 2026-01-30 | 9qF3t | Per-file sed patterns necessary | 23 patterns for SETUP_GUIDE.md | No shortcuts |
| 110 | 2026-01-30 | Ja1ql | New Verus files must be added to counting script | mat4_extended not counted | Add variable + sum + sed patterns |
| 111 | 2026-01-30 | Ja1ql | 4-phase decomposition generalizes to Mat4 | degree-4 diagonal det | Expand minors as let bindings |
| 112 | 2026-01-30 | Ja1ql | Mat4 T*S composite determinant needs all 16 elements | Both mul and det expanded | Assert all 16 + 12 Laplace minors |
| 113 | 2026-01-30 | Ja1ql | `dst.r * 1000 / 1000 == dst.r` not automatic | Z3 needs div hint | Explicit `assert` per component |
| 114 | 2026-01-30 | Ja1ql | Kani harness name collisions | Duplicate symbols | Descriptive suffixes |
| 115 | 2026-01-30 | Ja1ql | Flocq 4.1.3 buildable from source | GitLab INRIA tarball | Exclude `Nat2Z_8_12.v` |
| 116 | 2026-01-30 | Ja1ql | `sqrt_Rsqr` is direct lemma | Takes hypothesis as argument | `exact (sqrt_Rsqr x Hx)` |
| 117 | 2026-01-30 | Ja1ql | `nlra` doesn't exist in Coq 8.18 | Tactic is `nra` | `Require Import Psatz.` then `nra` |
| 118 | 2026-01-30 | Ja1ql | `(1+u)^n - 1 <= 2*n*u` FALSE for large `u`, `n >= 4` | Bound needs small `u` | `u <= 1/8` for n=4,5 |
| 119 | 2026-01-30 | Ja1ql | `nra` needs `pow_lt` hint for `(1+u)^n` | Not polynomial | `apply pow_lt; lra` then provide |
| 120 | 2026-01-30 | Ja1ql | `Require Import` is NOT `Require Export` | Imports don't re-export | Explicit imports in each file |
| 121 | 2026-01-30 | Ja1ql | `field` may close all subgoals in Coq 8.18 | Side conditions auto-discharged | `field.` alone or `field; lra.` |
| 122 | 2026-01-30 | Ja1ql | FP error composition: inductive multiplication | `(prefix-1)*(1+en) + en` | Factor, Rabs_triang, IH, ring |
| 123 | 2026-01-30 | Ja1ql | 99 Flocq-based FP theorems machine-checked | Phase FP-1 foundations | 4 files, total Coq: 796, combined: 1257 |
| 124 | 2026-01-31 | OnmS0 | New Bounds.v type requires script update | Script had no Bounds entries | Add per-file variables + sed patterns + JSON + display row |
| 125 | 2026-01-31 | OnmS0 | Script README sed patterns must match actual file format | "N theorems, 0 admits" didn't match actual "N theorems \| Zero admits" | Use context-anchored per-row sed: `/Coq (R-based)/{s/pattern/}` |
| 126 | 2026-01-31 | OnmS0 | VERIFICATION_COVERAGE.md sed pattern had stale anchor | `50` percent no longer in the line | Use `[0-9]+` to match any percentage |
| 127 | 2026-01-31 | OnmS0 | Per-file R-based proof table in COQ_PROOFS.md was stale | Not updated by script | Manual update; consider adding per-file sed patterns |
| 128 | 2026-01-31 | OnmS0 | "Breakthrough" language inappropriate for axiom injection technique | Well-known in Dafny/F*/Verus communities | Use "Proof Engineering Pattern"; add Related Work |
| 129 | 2026-01-31 | GlDgV | `cargo bench --workspace -- --noplot` fails on binary targets | Default bench harness doesn't understand criterion's `--noplot` | Use `--benches` flag to target only `[[bench]]` targets |
| 130 | 2026-01-31 | GlDgV | Mutation testing timeout 60s insufficient for CI | Complex mutants (cache serialization, parser state machines) exceed 60s | Increase to 120s in all 3 locations in `mutation.yml` |
| 131 | 2026-01-31 | GlDgV | Feature-gated tests invisible to default clippy | `#[cfg(feature = "cache")]` modules not compiled without `--all-features` | ALWAYS use `--all-features` in local AND CI clippy runs |
| 132 | 2026-01-31 | GlDgV | Test assumed decimal Display format, actual was hex | `RepositoryMismatch` uses `{:016x}` format | Read Display impl before writing assertions; never assume format |
| 133 | 2026-01-31 | GlDgV | 138 Trivy alerts from Docker `debian:trixie-slim` + git transitive deps | git pulls openldap, pam, ncurses, curl, expat, libtasn1, util-linux | Switch default target to `runtime-distroless` (cc-debian13:nonroot) |
| 134 | 2026-01-31 | GlDgV | Dismissing security alerts as "base image issue" is a VIOLATION | Assumed alerts would auto-resolve after image bump; proved wrong | NEVER dismiss; fix root cause by minimizing attack surface |
| 135 | 2026-01-31 | GlDgV | Mutation test doc comments need backticks for clippy `doc_markdown` | `/// Kill mutant: foo_bar` triggers doc_markdown lint | Wrap all identifiers: `` /// Kill mutant: `foo_bar` `` |
| 136 | 2026-01-31 | GlDgV | Equivalent mutants: `ParseOptions::strict()` → Default identical | Both produce same struct field values | Document as equivalent; don't write tests for impossible-to-kill mutants |
| 137 | 2026-01-31 | GlDgV | Docker glibc mismatch: Trixie builder (glibc 2.39) vs distroless cc-debian12 (glibc 2.36) | All Docker stages must use same Debian generation | Upgrade distroless to cc-debian13; never mix Debian generations in multi-stage builds |

---

*Last updated: 2026-01-31 | 137 entries | 14 categories*
