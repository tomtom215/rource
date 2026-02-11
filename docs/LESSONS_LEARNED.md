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
14. [Category: Documentation Content Auditing](#category-documentation-content-auditing)
15. [Chronological Audit Log](#chronological-audit-log)

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
| Z area/expand with nested `Z.sub` in constructors | `rewrite` proven width/height lemmas, then `ring` | `zb_unfold` + `ring` fails on nested `Z.sub` |
| Z center translation `(a + dx + b + dx) / 2` | Factor as `dx * 2 + (a + b)`, `rewrite Z.div_add_l` | `lia` can't handle division directly |
| Generic `(1+u)^n > 0` | `apply pow_lt; lra` then provide to `nra` | `nra` can't prove non-polynomial positivity |
| `Rmin_left`/`Rmax_left` unavailable (Coq 8.18) | `unfold Rmin; destruct (Rle_dec ...); lra` | Named lemmas may not exist in 8.18; inline unfold always works |
| Record field accessors in hypotheses (`bounds_min_x (mkBounds ...)`) | `unfold ..., ... in *. simpl in *.` BEFORE `lra`/`f_equal` | `lra` cannot connect unsimplified field accessors to bare variables |
| Existential `Rabs` witness (counterexample) | `Rabs_def1` to prove, `Rabs_def2` to destructure hypothesis | Standard library pair; `Rabs_def1: -a < x < a → Rabs x < a` |
| `if Rle_dec _ _ then ... else ...` in definition | `destruct (Rle_dec _ _) as [H|H]` + handle both branches | Case-split the decision to expose concrete branch |
| Composition `f(f(x,a1),a2) = f(x, combined)` | Factor as `1 - (1-a1)*(1-a2)`, then `ring` | Both darken and lighten follow this multiplicative pattern |
| Decimal `0.2126` vs fraction `2126/10000` | `lra` (NOT `ring`) | `ring` can't equate decimal literals with fraction forms; `lra` handles both |
| 4-tuple equality `(a,b,c,d) = (a',b',c',d')` | `replace ... by ring; reflexivity` per component | `f_equal` chaining fails on 4-tuples; explicit component replacement is robust |
| `Rabs` of known-sign expression | `match goal with \|- Rabs ?x = _ => replace x with val by lra end. unfold Rabs. destruct (Rcase_abs val); lra.` | Most robust pattern; works regardless of expression complexity |
| Theorem name collision | `grep '^Theorem\|^Lemma' file.v` BEFORE adding | Duplicate names cause `already exists` error; always check first |

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
| Algebraic correctness (Rust) | Verus | ADOPT (498 proof functions) |
| Mathematical theorems | Coq | ADOPT (1837 theorems: 1366 R-based + 471 Z-based) |
| IEEE 754 edge-case safety | Kani (CBMC) | ADOPT (272 harnesses) |
| FP error bounds | Coq + Flocq | ADOPT (361 theorems) |
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
| 211 | `ring` fails on decimal↔fraction equivalence (`0.2126` vs `2126/10000`) | `ring` normalizes polynomials over abstract reals; decimal literals are opaque | Use `lra` which handles linear real arithmetic including decimal/fraction equivalences |
| 212 | `f_equal` chaining fails for 4-tuple equality | `f_equal; [|f_equal; [|f_equal]]; ring` gives "Incorrect number of goals" on 4-tuples | Use sequential `replace` per component: `replace (1-(1-cr)) with cr by ring. ... reflexivity.` |
| 213 | Robust `Rabs` proof: match-replace-unfold-destruct pattern | `rewrite Rabs_Ropp` fails when subterm doesn't match syntactically | `match goal with \|- Rabs ?x = _ => replace x with val by lra end. unfold Rabs. destruct (Rcase_abs val); lra.` |
| 214 | `color_scale` scales ALL components including alpha | Theorem incorrectly stated `color_a c` for alpha of scaled color | Correct: `color_a (color_scale c s) = color_a c * s`, not `color_a c` |
| 215 | `apply vec3_eq; ring` fails — needs `simpl` between | After `apply vec3_eq`, goals have unevaluated record projections like `v3x (mkVec3 ...)` | Always `apply vec3_eq; simpl; ring` — `simpl` reduces the projections first |
| 216 | `mat4_scale` not `mat4_scalar_mul` | Grepped wrong function name from memory | Always `grep 'Definition mat4_' file.v` to confirm exact name |
| 217 | `bounds_contains` not `bounds_contains_point` | Wrong name assumed for Bounds containment predicate | Always check `.v` spec file for exact definition name |
| 124 | FP error composition follows inductive multiplication pattern | `(1+e1)*...*(1+en) - 1` decomposes as `(prefix-1)*(1+en) + en` | Factor, `Rabs_triang`, `Rabs_mult`, IH, then `ring`+`Rplus_le_compat` |
| 142 | Z-based `ring` fails after `zb_unfold` on Bounds_Compute.v | `zb_unfold` exposes nested `Z.sub` in constructors | Rewrite with proven width/height lemmas first, then `ring` |
| 143 | `Z.abs_triangle` for approximate-equality triangle inequality | Transitive approximate equality via triangle inequality | Factor difference via `lia`, `eapply Z.le_lt_trans`, `apply Z.abs_triangle` |
| 144 | `Z.div_add_l` enables center-translation proofs | `(a*b + c)/b = a + c/b` | Factor sum, then `rewrite Z.div_add_l by lia` |
| 148 | `zlerp_bounded` requires careful Z division reasoning | Division monotonicity chain for bounded interpolation | `Z.mul_le_mono_nonneg_l` → `Z.div_le_mono` → `Z.div_mul` |
| 201 | `apply vec3_eq; ring` fails — unreduced record projections on RHS | `apply vec3_eq` generates goals with `v3x (mkVec3 0 0 0)` which `ring` can't handle as opaque | Always use `apply vec3_eq; simpl; ring` — the `simpl` reduces `v3x (mkVec3 a b c)` → `a` |
| 202 | Orthonormal basis parameterization avoids sqrt in Coq | `look_at(eye, target, up)` requires `normalize` (sqrt), unprovable in Coq | Parameterize as `look_at(s, u, f, eye)` with pre-computed orthonormal basis vectors |

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
| 156 | Verus `lerp_scale` proofs fail: struct equality after `by(nonlinear_arith)` | Z3 proves component-level facts in isolated nonlinear context but cannot connect them to struct-equality postcondition across function compositions | Avoid postconditions that compose two spec functions with nonlinear parameters; use concrete-value proofs (t=0,1,2) or trivially-reducible compositions instead |
| 157 | Adding proofs to a file can break previously-passing Z3 proofs | Z3 resource contention — more proofs consume Z3's resource budget, causing timeouts on complex proofs | Use `#[verifier::rlimit(20)]` on resource-intensive proofs (e.g., cross product orthogonality); default rlimit=10 may be insufficient for files with 50+ proof functions |
| 158 | Verus lerp spec function works best with boundary-value proofs | `lerp(a,b,0)=a`, `lerp(a,b,1)=b`, `lerp(v,v,t)=v` all verify with empty bodies; parametric compositions like `lerp(neg(a),neg(b),t)=neg(lerp(a,b,t))` do NOT verify | Stick to boundary values (t=0,1,2,-1) and algebraic identities (lerp(v,v,t)=v) for lerp proofs; these are the most valuable mathematically anyway |

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
| 138 | Adding new Kani module requires 6-place script update | Script has per-file vars, TOTAL, JSON, display, sed | Checklist: count var, TOTAL sum, per-type total, JSON, printf, sed |
| 139 | `mod` declaration easily missed for new Kani file | Created file but forgot `mod bounds;` | Verify module registration immediately after file creation |
| 141 | Bounds `intersects` self-check needs strict inequality gap | `intersects()` uses `<` not `<=` | Require `width > 1.0` for self-intersection |
| 159 | Kani harnesses for operator overloads require matching trait syntax | `v * s` compiles but tests `Mul<f32>` impl; `-v` tests `Neg` impl | Test operators directly (e.g., `a + b`, `a - b`, `-v`) — Kani will find the trait impl automatically |
| 160 | Kani `verify_color_fade_preserves_rgb` validates separation of concerns | `fade()` modifies alpha while preserving RGB — a common source of bugs | Property-based harnesses can catch field-mutation bugs that unit tests miss |
| 179 | Algebraic property harnesses (commutativity, anti-commutativity, idempotency) are uniformly applicable | All vector/matrix types support same operator overloads | Template: `verify_<type>_<op>_<property>` — e.g., `verify_vec4_mul_commutative`, `verify_clamp_idempotent` |
| 180 | `from_corners` harness validates `min(a,b)` / `max(a,b)` contract | `Rect::from_corners` normalizes via `f32::min`/`f32::max` | Assert `r.width >= 0.0 && r.height >= 0.0` for any finite inputs |

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
| 181 | `fp_four_op_composition` doesn't exist — must inline 4-op proof | FP_ErrorBounds.v only provides `two_op_error_bound` and `fp_three_op_composition` | Write 4-op proof inline following `fp_vec4_length_sq_error` pattern: chain `fp_three_op_composition` + `Rabs_triang` + `Rmult_le_compat` |
| 182 | `Rle_max_compat_l`/`Rle_max_compat_r` not in Coq 8.18 stdlib | Used in FP_Rect.v and FP_Bounds.v for Rmax bounds | Add `Local Lemma` definitions: `unfold Rmax; destruct (Rle_dec x y); lra` |
| 183 | FP Rect/Bounds/Utils files follow uniform structure | Each type needs: 1-op, 2-op, multi-op, exact, composition, and stability theorems | Template: ~35 Theorems + ~2 Local Lemmas per type, grouped by operation depth |

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
| 200 | `coq-flocq` not found: "No package named coq-flocq found" after `opam install` | `coq-flocq` is NOT in the default opam.ocaml.org repository; it requires the Coq released opam repo (`coq.inria.fr/opam/released`) which returns HTTP 503 | Cascading fallback: try HTTPS endpoints, then clone GitHub mirror (`github.com/coq/opam` → `released/` directory) as local opam repo |

---

## Category: Documentation & Metrics Automation

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 106 | Rounded display strings resist minor fluctuations | "2700+" stays valid across small changes | Rounded form + `+` suffix for display; exact in JSON |
| 107 | Peripheral docs need same automation as primary docs | SETUP_GUIDE.md, etc. had stale counts | Automation must cover ALL files with metrics |
| 108 | Documentation drift inevitable without CI enforcement | Counts go stale within a single session | CI must enforce `--check` mode on both scripts |
| 109 | Two-tier script architecture for doc automation | Verification counts vs other metrics need different extraction | `update-verification-counts.sh` + `update-doc-metrics.sh` |
| 110 | Ground truth must come from source files | Hardcoded counts go stale immediately | Parse actual source: `grep -cE` patterns |
| 140 | Sed patterns with hardcoded old counts become stale | Script used `**446 theorems**` literal | Use `[0-9]+` patterns for numbers; never hardcode previous values |
| 145 | README.md sed patterns must match actual Markdown table format | Expected `N theorems, 0 admits | Machine-checked` vs actual `N theorems | Zero admits` | Row-anchored: `/Coq \(R-based\)/s/[0-9]+ theorems/$N theorems/` |
| 146 | WASM_EXTRACTION_PIPELINE.md had no update rule in script | File with Coq counts was created without script entry | When creating doc files with metrics, ALWAYS add sed patterns to update script |
| 147 | CLAUDE.md per-type verification table needs automated updates | Per-type Bounds/Utils rows went stale | Added per-type row patterns to `update-verification-counts.sh` |
| 184 | New FP Coq files require 3-place script update | Script needs: count variable, TOTAL formula update, JSON output entry | Checklist: `COQ_FP_<TYPE>=$(count_coq ...)`, add to `COQ_FP_TOTAL`, add to JSON `coq_fp` block |
| 185 | `Rdiv_lt_1` not standard Coq — rewrite using `Rmult_lt_compat_r` | FP_Utils.v theorem on `u32 / (1 + u32) < 1` needed non-standard lemma | `Rmult_lt_compat_r` + `Rinv_r` pattern: multiply both sides by `/(1+u32)`, rewrite `(1+u32) * /(1+u32)` to 1 |

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

## Category: Documentation Content Auditing

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 233 | Non-existent CLI flags documented in TROUBLESHOOTING.md (7+ flags) | Docs written speculatively without verifying `args/mod.rs` | Always grep `rource-cli/src/args/` for any CLI flag referenced in docs |
| 234 | Wrong WASM API method names in RUNBOOK.md (8+ methods) | Names guessed from conventions instead of checked against `wasm_api/` | Always grep `rource-wasm/src/wasm_api/` and `lib.rs` for `#[wasm_bindgen]` exports |
| 235 | JS API constructor `new Rource(canvas)` never existed — factory is `await Rource.create(canvas)` | Docs assumed constructor pattern; actual API uses async factory | Verify JS API against `rource-wasm/src/lib.rs` `create()` method |
| 236 | Renderer trait signatures wrong in ARCHITECTURE.md and RENDERING.md | Documented from memory instead of source; missing `width` param on `draw_circle`, missing `draw_disc` | Always read `crates/rource-render/src/lib.rs` `pub trait Renderer` for authoritative signatures |
| 237 | Backend selection order wrong in RENDERING.md (said WebGL2 first; actual is wgpu first) | Documented assumption contradicted by `Rource::create()` in `lib.rs` | Check `rource-wasm/src/lib.rs` `create()` for actual initialization sequence |
| 238 | `getRendererType()` return strings documented as PascalCase but are lowercase | Convention assumed; actual strings are `"wgpu"`, `"webgl2"`, `"software"` | Check `get_renderer_type()` in `wasm_api/rendering.rs` for exact return values |
| 239 | ADR 0004 (generation counter) accepted but pattern never implemented | Decision documented but LabelPlacer uses `Vec::clear()` not generation counters | Audit ADRs against actual implementation; mark as Superseded when pattern differs |
| 240 | CONTRIBUTING.md JS directory tree had 12 entries but actual directory has 30+ files | Tree written once and never updated as files were added | Verify directory trees with `find` or `ls -R` before documenting |
| 241 | GOURCE_COMPARISON.md listed 3 features as "roadmap" that were already implemented | Feature status not updated when implementation completed | Cross-reference feature claims with `grep` in source before marking status |
| 242 | `getMetrics()` referenced in TELEMETRY.md but actual method is `getFrameStats()` | API renamed but docs not updated | Use `grep -r 'wasm_bindgen' rource-wasm/src/` to find actual exported names |
| 243 | Broken link in docs/README.md (`performance/FORMAL_PROOFS.md` → `performance/formal-proofs/README.md`) | Path changed but cross-reference not updated | Run link checker (`grep -oP` + file existence check) before committing doc changes |
| 244 | Verification proof counts drifted from source (Vec2 Verus: 55→61, Color Verus: 57→64, Coq-Z totals: 417→471) | Phase 1 metrics update missed per-file granular counts in VERUS_PROOFS.md and COQ_PROOFS.md | Automation scripts must cover ALL files containing per-type/per-file counts, not just summary totals |
| 245 | Subagent audit results must be verified before applying | Agent reported `getDetailedFrameStats` as non-existent but it exists at `lib.rs:1042` | Always cross-check agent-reported violations against source before editing |
| 246 | Files with most violations: TROUBLESHOOTING.md (7+), RUNBOOK.md (8+), RENDERING.md (5+), ARCHITECTURE.md (5+) | These files describe implementation details that change frequently | Prioritize these files in future audits; consider automation for API-referencing docs |
| 259 | Verus uses `proof fn` keyword, NOT `#[verifier::proof]` attribute | ARCHITECTURE.md had deprecated syntax | Always verify tool syntax against actual proof files |
| 260 | FP_Common.v uses named constants `prec32`/`emin32`/`fexp32`, not inline `binary32 := FLT_exp (-149) 24` | Paper simplified beyond accuracy | Diff code snippets against actual `.v` files |
| 261 | Kani proofs directory (`kani_proofs/`, 10 files), not single file `kani_proofs.rs` | Module refactored from file to directory | Update all grep/counting commands after refactors |
| 262 | ALL 8 Coq Record field names wrong in SPEC_IMPL_CORRESPONDENCE.md | Written from memory, never verified | ALWAYS read actual `.v` Record definitions |
| 263 | Utils.v MUST compile before Vec2.v, Vec3.v, Vec4.v | `Require Import RourceMath.Utils` dependency chain | Verify compilation order with `grep 'Require Import'` |
| 264 | Per-file Z-compute breakdown stale: Vec2(62→76), Rect(51→79); sum was 429, not claimed 471 | Per-file counts not updated | Cross-check per-file breakdowns SUM to claimed total |
| 265 | RENDERING_BOTTLENECK_ANALYSIS.md stale code snippet (Phase 70 changes not reflected) | Optimization applied but doc not updated | Re-verify before/after snippets after each optimization phase |
| 266 | BENCHMARKS.md test count "2,076" severely stale (actual 2964) | Snapshot never updated | Use rounded display strings or automate |
| 267 | File paths missing `crates/` prefix in 2 BENCHMARKS.md references | Shorthand without repo-root prefix | ALWAYS use full path from repo root |

---

## Chronological Audit Log

All 246 entries in chronological order. Entry numbers match category table references.

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
| 138 | 2026-01-31 | pnY2l | Adding new Kani module requires script update in 6 places | `update-verification-counts.sh` has per-file variables, TOTAL sum, JSON output, display row, sed patterns, and consistency checks | Checklist: (1) count variable, (2) TOTAL sum, (3) per-type total, (4) JSON, (5) display printf, (6) sed patterns for docs |
| 139 | 2026-01-31 | pnY2l | `mod` declaration easily missed when creating new Kani file | Created bounds.rs but forgot `mod bounds;` in mod.rs | Always verify module registration immediately after file creation; add to checklist |
| 140 | 2026-01-31 | pnY2l | Documentation sed patterns with hardcoded old counts become stale | Script used `**446 theorems**` as literal match; broke when counts changed | Use `[0-9]+` patterns for numbers, not hardcoded values |
| 141 | 2026-01-31 | pnY2l | Kani Bounds `intersects` self-check requires strict inequality gap | `intersects()` uses `<` not `<=`; degenerate bounds fail self-intersection | Require `width > 1.0` to ensure `min + width > min` in IEEE 754 |
| 142 | 2026-01-31 | pnY2l | Z-based `ring` fails after `zb_unfold` on Bounds_Compute.v | `zb_unfold` exposes `Z.sub` in constructor args; `ring` can't handle nested Z.sub | NEVER use `zb_unfold` + `ring` for area/expand; rewrite with proven lemmas first |
| 143 | 2026-01-31 | pnY2l | `Z.abs_triangle` for Z approximate-equality triangle inequality | `Z.abs (a - c) <= Z.abs (a - b) + Z.abs (b - c)` | Factor `a - c = (a - b) + (b - c)` via `lia`, then `eapply Z.le_lt_trans` with `Z.abs_triangle` |
| 144 | 2026-01-31 | pnY2l | `Z.div_add_l` enables center-translation proofs | `(a * b + c) / b = a + c / b` for `b <> 0` | Factor sum as `dx * 2 + (mnx + mxx)`, then `rewrite Z.div_add_l by lia` |
| 145 | 2026-01-31 | pnY2l | Script README.md sed patterns must match actual Markdown table format | Pattern expected `N theorems, 0 admits | Machine-checked` but actual was `N theorems | Zero admits` | Use row-anchored patterns: `/Coq \(R-based\)/s/[0-9]+ theorems/$N theorems/` |
| 146 | 2026-01-31 | pnY2l | WASM_EXTRACTION_PIPELINE.md had no update rule in script | New file with Coq counts was not in any script | When creating doc files with metrics, ALWAYS add sed patterns to update script |
| 147 | 2026-01-31 | pnY2l | CLAUDE.md per-type verification table needs automated updates | Bounds (70→79, 62→70) and Utils (23→30, 13→18) went stale | Added per-type row patterns to `update-verification-counts.sh` |
| 148 | 2026-01-31 | pnY2l | `zlerp_bounded` requires careful Z division reasoning | `(b-a)*t/1000 <= (b-a)` needs `Z.div_le_mono` + `Z.div_mul` | Factor: `Z.mul_le_mono_nonneg_l` for `t <= 1000`, then `Z.div_le_mono`, then `Z.div_mul` |
| 149 | 2026-01-31 | 6mS3R | Verus `lerp_simple(a,b,t) = a + (b-a)*t` fails for properties using `t*(b-a)` | Z3 linear arithmetic cannot prove `(b-a)*t == t*(b-a)` (multiplication commutativity is nonlinear) | Add `assert((b - a) * t == t * (b - a)) by(nonlinear_arith);` for commutativity, `by(nonlinear_arith)` for distributivity |
| 150 | 2026-01-31 | 6mS3R | Verus `by(nonlinear_arith)` assertions must match spec function's operand order | Spec used `(b-a)*t` but assertions proved `t*(b-a)` — Z3 couldn't connect them even with `nonlinear_arith` hints on the wrong term | Always match the exact term order from the spec function definition in `assert()` statements |
| 151 | 2026-01-31 | 6mS3R | `coqc` only accepts ONE `.v` file argument at a time | `coqc -Q . RourceMath A.v B.v` fails with "More than one file to compile" | Use `for f in *.v; do coqc -Q . RourceMath "$f"; done` or compile files individually |
| 152 | 2026-01-31 | 6mS3R | Coq proof files must compile AFTER their spec dependencies | `Vec2_Proofs.v` depends on `Vec2.v`; compiling out of order fails | Compile spec files (`.v`) before proof files (`_Proofs.v`) before compute files (`_Compute.v`) |
| 153 | 2026-01-31 | 6mS3R | Adding new Verus proof file requires script update in 8 places | `update-verification-counts.sh` needs: count variable, TOTAL sum, per-type total, JSON output, display printf row, sed patterns for each doc file, CHECKS array entries | Created checklist: same pattern as Kani lesson #138 but with Verus-specific sed patterns |
| 154 | 2026-01-31 | 6mS3R | GMP must be built from source when apt DNS fails | `apt install libgmp-dev` fails in sandboxed environments with no DNS | Download GMP 6.3.0 from gmplib.org, `./configure && make && make install`, create symlinks for `/usr/include/gmp.h` and `/usr/lib/x86_64-linux-gnu/libgmp.so` |
| 155 | 2026-01-31 | 6mS3R | Flocq build requires excluding incompatible files | `PrimFloat.v`, `Int63Compat.v`, `Int63Copy.v`, `Pff2Flocq.v`, `Nat2Z_compat.v` fail on Coq 8.18 | Edit `_CoqProject` to exclude these 5 files before running `coq_makefile` |
| 156 | 2026-01-31 | SdlU8 | Verus `lerp_scale` proofs fail: struct equality after nonlinear_arith | Z3 proves component facts in isolated context but can't connect to struct-equality postcondition | Use concrete-value proofs (t=0,1,2) instead of parametric compositions |
| 157 | 2026-01-31 | SdlU8 | Adding proofs to a file breaks previously-passing Z3 proofs | Z3 resource contention from more proofs in the file | Add `#[verifier::rlimit(20)]` to resource-intensive proofs; default rlimit=10 insufficient for 50+ proof files |
| 158 | 2026-01-31 | SdlU8 | Verus lerp spec function works best with boundary-value proofs | Parametric compositions fail but boundary values (t=0,1,2,-1) verify with empty bodies | Boundary-value lerp proofs are both most reliable and most mathematically valuable |
| 159 | 2026-01-31 | SdlU8 | Kani operator overload harnesses work directly | `a + b`, `a - b`, `-v` compile directly testing trait impls | No special syntax needed for operator trait verification |
| 160 | 2026-01-31 | SdlU8 | Kani property harnesses catch field-mutation bugs | `fade()` preserves RGB while modifying alpha — unit tests often miss this | Add separation-of-concern harnesses for methods that modify some fields but not others |
| 161 | 2026-01-31 | b9iYZ | Always `grep` for existing theorem names before adding new ones | Added theorems to Rect_Proofs.v/Bounds_Proofs.v that already existed, causing `already exists` errors | Run `grep '^Theorem\|^Lemma' file.v` before writing new proofs; deduplicate against full name list |
| 162 | 2026-01-31 | b9iYZ | `Rmin_left`/`Rmax_left` unavailable in Coq 8.18 | Used `apply Rmin_left` which doesn't exist | Use `unfold Rmin; destruct (Rle_dec ...); lra` pattern — always works regardless of stdlib version |
| 163 | 2026-01-31 | b9iYZ | Record destructuring hypotheses need `simpl in *` before `lra` | `bounds_contains` destruct gave `bounds_min_x (mkBounds a1 a2 a3 a4) <= px` — `lra` couldn't connect | Add `unfold ..., ... in *. simpl in *.` to reduce field accessors in ALL hypotheses before arithmetic tactics |
| 164 | 2026-01-31 | b9iYZ | `Rabs_def1`/`Rabs_def2` pair for existential counterexamples | Non-transitivity proof needs both constructing and destructuring `Rabs < eps` | `Rabs_def1: -a < x < a → |x| < a` (prove); `Rabs_def2: |x| < a → -a < x < a` (use as hyp) |
| 165 | 2026-01-31 | b9iYZ | Darken/lighten composition follows `1-(1-a1)*(1-a2)` pattern | Both `color_darken` and `color_lighten` compose multiplicatively | `ring` solves automatically; mathematically: `f(f(x,a1),a2) = f(x, 1-(1-a1)(1-a2))` |
| 166 | 2026-01-31 | b9iYZ | `Rle_dec` case-split required for `color_contrasting` proofs | `color_contrasting` uses `if Rle_dec (luminance c) (1/2) then white else black` | `destruct (Rle_dec _ _) as [H\|H]` to case-split, then each branch resolves by `reflexivity` or `exfalso; lra` |

| 167 | 2026-01-31 | 6qbb3 | `field; exact Hdet` fails when `field` generates conjunction side conditions | `field` on inverse expressions produces `det(A) <> 0 /\ det(inv(A)) <> 0`; single `exact` can't satisfy conjunction | Use `field; auto` or `field; split; assumption` to discharge conjunction side conditions |
| 168 | 2026-01-31 | 6qbb3 | Algebraic proof chains avoid brute-force `field` on nested inverses | `inverse(inverse(A)) = A` proof via component-wise `field` requires both `det(A)` AND `det(inv(A))` side conditions | Chain rewrites: `rewrite <- mat3_mul_right_identity`, `rewrite <- mat3_inverse_correct`, `rewrite <- mat3_mul_assoc`, `rewrite mat3_inverse_correct` — 5-line proof vs. fragile `field` |
| 169 | 2026-01-31 | 6qbb3 | `mat3_det_inverse` requires algebraic proof, not direct `field` | `field` on fully-unfolded `det(inverse(A))` produces "not a valid field equation" | Use `mat3_det_mul` + `mat3_inverse_correct` + `Rmult_eq_reg_r` to prove `det(inv(A)) * det(A) = 1` algebraically, then derive `det(inv(A)) = /det(A)` |
| 170 | 2026-01-31 | 6qbb3 | Rect_Proofs.v and Bounds_Proofs.v are more comprehensive than theorem number suggests | 120/86 theorems already cover ALL obvious properties including compositions, inverses, center preservation | Always grep ALL existing theorem names before proposing additions; output is available via `grep '^Theorem\\|^Lemma' file.v \| sort` |

| 171 | 2026-01-31 | NQWQv | `update-verification-counts.sh` doesn't update per-type Z-compute columns in FORMAL_VERIFICATION.md table | Script updated Color total to 219 but left Z-Compute column at "28 theorems" (should be 38) | After running the script, always manually verify per-type table cells against `metrics/verification-counts.json` — the script updates totals but not individual Z-compute values in per-type rows |
| 172 | 2026-01-31 | NQWQv | CLAUDE.md per-type table is not updated by `update-verification-counts.sh` | CLAUDE.md had stale Verus counts (49→55, 40→55, 39→55), stale Coq counts (80→92, 104→157, 88→100, 112→120), stale Kani (9→23), stale FP (99→177) | The script updates narrative counts in CLAUDE.md but NOT the per-type component table; always manually verify this table matches ground truth after major count changes |
| 173 | 2026-01-31 | NQWQv | `Z.quot.Z.div_0_l` doesn't exist in Coq 8.18 | Used `rewrite Z.quot.Z.div_0_l by lia` which gave "The reference Z.quot.Z.div_0_l was not found" | For `0 / n = 0` in Z, use `replace (X * 0 / n) with 0 by (rewrite Z.mul_0_r; reflexivity)` — the `Z.mul_0_r` lemma exists and `0 / n` computes to `0` by reflexivity |
| 174 | 2026-01-31 | NQWQv | Flocq not available in opam on this environment | `opam search flocq` returns only `farith` (extracted library), not the Coq formalization | FP error bound expansion (FP_Rect.v, FP_Bounds.v) requires Flocq 4.1.3 to be installed via opam; document in setup script and defer when unavailable |
| 175 | 2026-01-31 | NQWQv | Vec4 Kani harness gap was due to limited API, not missing coverage | Vec4 has only 11 public methods (no floor/ceil/round/reflect/project/distance) vs Vec2's 20+ | Don't compare harness counts across types with different APIs; instead add deeper algebraic property harnesses (commutativity, involution, unit-length) for existing operations |
| 176 | 2026-01-31 | ykSJI | `coqc: command not found` despite Coq 8.18 installed via apt at `/usr/bin/coqc` | The bash tool resets PATH between invocations; `eval $(opam env)` doesn't persist, and `/usr/bin` may not be in PATH during some shell initializations | Always use absolute path `/usr/bin/coqc` when invoking Coq directly, instead of relying on `coqc` being in PATH |
| 177 | 2026-01-31 | ykSJI | Z-integer roundtrip `zf32_to_u8(zu8_to_z1000(n)) = n` does NOT hold in general | Integer division truncation: `zu8_to_z1000(128) = 501`, `zf32_to_u8(501) = 127 ≠ 128`. The 1000-scale fixed-point loses precision through truncation | For Z-compute roundtrips involving division, prove boundary cases (0, 255) instead of universal quantification; document the precision limitation explicitly |
| 178 | 2026-01-31 | ykSJI | `simpl. lia.` and `change ... lia.` fail on Z division expressions after `unfold zclamp` | `lia` cannot handle `Z.div` (linear integer arithmetic only); `simpl` doesn't reduce division of concrete Z values after `destruct` on boolean comparisons | Factor out helper lemmas (`zclamp_ge_lo`, `zclamp_nonneg`, `zclamp_le_hi`) and use `Z.div_pos`, `Z.div_le_upper_bound`, `Z.mul_nonneg_nonneg` from the Z library instead of brute-force tactic application |

| 179 | 2026-02-01 | r1GdR | Algebraic property Kani harnesses (commutativity, anti-commutativity, idempotency) are uniformly applicable across all types | All vector/matrix types support same operator overloads (`Add`, `Sub`, `Mul`, `Neg`) | Template: `verify_<type>_<op>_<property>` works for Vec2-4, Mat3, Color, Rect, Bounds, Utils with identical structure |
| 180 | 2026-02-01 | r1GdR | `Rect::from_corners` harness validates `min`/`max` normalization contract | `from_corners(a, b)` uses `f32::min`/`f32::max` to normalize | Assert `r.width >= 0.0 && r.height >= 0.0` for any finite inputs — catches potential NaN propagation |
| 181 | 2026-02-01 | r1GdR | `fp_four_op_composition` doesn't exist in FP_ErrorBounds.v | FP_ErrorBounds.v only provides up to 3-op composition | Write 4-op proof inline following `fp_vec4_length_sq_error` pattern from FP_Vec.v |
| 182 | 2026-02-01 | r1GdR | `Rle_max_compat_l`/`Rle_max_compat_r` not in Coq 8.18 standard library | Used in FP_Rect.v and FP_Bounds.v for Rmax inequality bounds | Add `Local Lemma` definitions: `unfold Rmax; destruct (Rle_dec x y); lra` at top of each file |
| 183 | 2026-02-01 | r1GdR | FP Coq files follow uniform structure per type (~35 Theorems + ~2 Local Lemmas) | Each spatial type needs error bounds for all operation depths | Group by: 1-op exact, 1-op bounded, 2-op, multi-op, composition, stability |
| 184 | 2026-02-01 | r1GdR | New FP Coq files require 3-place script update (count var + TOTAL + JSON) | Script was blind to FP_Rect.v, FP_Bounds.v, FP_Utils.v initially | Checklist: `COQ_FP_<TYPE>=$(count_coq ...)`, update `COQ_FP_TOTAL` formula, add JSON `coq_fp` entry |
| 185 | 2026-02-01 | r1GdR | `Rdiv_lt_1` not available — rewrite using `Rmult_lt_compat_r` + `Rinv_r` | FP_Utils.v needed `u32 / (1 + u32) < 1` without standard lemma | Multiply both sides by `/(1+u32)`, use `Rmult_lt_compat_r` for order preservation, `Rinv_r` to cancel |
| 186 | 2026-02-01 | r1GdR | `Rabs_Rabsolu` may not exist in Coq 8.18 — use `Rabs_right` + `Rabs_pos` | Vec2_Proofs.v theorem on `abs(abs(x))` needed rewrite | `rewrite Rabs_right; try apply Rabs_pos; reflexivity` — always works |
| 187 | 2026-02-01 | r1GdR | Methods in VERIFICATION_COVERAGE.md may not exist in source | Color::scale, Rect::normalize, Vec2::fract listed as uncovered but don't exist in implementation | Always `grep 'pub fn method_name'` in source before writing harnesses; adapt plan to actual API |
| 188 | 2026-02-01 | aKa8F | FP theorem expansion is safely parallelizable across files | FP_Rect.v, FP_Bounds.v, FP_Rounding.v, FP_Utils.v, FP_Vec.v, FP_Mat.v, FP_Color.v each import only FP_Common.v and FP_ErrorBounds.v | Edit multiple FP files in parallel, then compile in dependency order: FP_Common → FP_Rounding → FP_ErrorBounds → rest |
| 189 | 2026-02-01 | aKa8F | Rmin/Rmax associativity proofs need exhaustive case splits | `unfold Rmin; destruct (Rle_dec ...)` generates 8 branches for 3-variable associativity | Use `try destruct; try lra` pattern to handle all 8 combinations; some branches need secondary destructs |
| 190 | 2026-02-01 | aKa8F | `Znearest_monotone` exists in Flocq 4.1.3 and takes `x <= y` directly | Needed for fp_round_monotone theorem | `apply Znearest_monotone. lra.` — the Flocq lemma handles the choice function automatically |
| 191 | 2026-02-01 | aKa8F | `Zceil_lb` exists in Flocq (unlike standard Coq) and gives `IZR(Zceil x) - 1 < x` | Needed for `fp_ceil_floor_distance` to bound ceil-floor gap | Available via `generalize (Zceil_lb x)` in proofs that need the lower bound of ceiling function |
| 192 | 2026-02-01 | aKa8F | VERIFICATION_COVERAGE.md operation counts had pre-existing inconsistency (Mat3: 17 total listed but 16+3=19 items) | The "not verified" list had 3 items but total was listed as 17 | Fixed: Mat3 total = 19 operations (16 verified + 3 not-verified), now 18 verified after transform_point/transform_vector proofs |
| 193 | 2026-02-01 | 8mCIA | `simpl` breaks `ring` for Z-compute lerp_one proofs: `Z.mul (Z.pos xH) x` reduces to irreducible match | `simpl` pattern-matches Z.mul on BOTH args; when second arg is symbolic `Z.sub`, it produces `match ... with Z0 => Z0 | Z.pos y' => Z.pos y' | Z.neg y' => Z.neg y'` which `ring` cannot handle | Use `cbn [field_selectors]` (e.g. `cbn [zvec2_x zvec2_y]`) to selectively reduce only record projections, keeping `1 * x` intact for `ring` |
| 194 | 2026-02-01 | 8mCIA | `lerp_zero` works with `simpl; ring` because `Z.mul Z0 x` reduces immediately (Z0 match on first arg) | Only `lerp_one` needs `cbn` workaround since `Z.mul 1 x` requires second-arg pattern match | Apply `cbn [field_selectors]` pattern ONLY where t=1; t=0 and t=same cases work fine with `simpl` |
| 195 | 2026-02-01 | 8mCIA | Duplicate theorem names across FP files cause silent shadowing, not compilation errors | Coq allows redefinition in different files; no warning unless modules are composed | Check with `grep -hE '^(Theorem\|Lemma) ' *.v \| sort \| uniq -d` before committing ANY Coq changes |
| 196 | 2026-02-01 | 8mCIA | FP_Rounding.v had 5 internal duplicates (theorems 6,8,9,11,16 re-defined as 31-35) | Adding "new" theorems without checking existing names in the SAME file | Always `grep -c 'theorem_name' current_file.v` before adding, even for seemingly unique names |
| 197 | 2026-02-01 | 8mCIA | Cross-file FP theorem name collisions: 6 pre-existing (fp_error_upper_approx_*, fp_min/max_idempotent, fp_rect_*_error) | Different FP files independently defined identically-named theorems with slightly different bounds/contexts | Use module-prefixed names: `fp_mat_*`, `fp_color_*`, `fp_*_bounds` to disambiguate cross-file theorems |
| 198 | 2026-02-01 | 8mCIA | Flocq/coq-flocq unavailable: opam package name is `coq-flocq`, but Coq opam repo (coq.inria.fr) returns HTTP 503 | Cannot machine-check FP_Rounding.v new theorems without Flocq 4.1.3 | FP theorems structurally follow verified patterns; mark as "written, pending machine-check" until Flocq repo available |
| 199 | 2026-02-01 | 8mCIA | Documentation counts can drift significantly (was 2508, actual 2491→2541 after session) even with update scripts | Scripts update docs but must be run; between runs, manual edits accumulate errors | ALWAYS run `update-verification-counts.sh` after ANY proof file change, not just at session end |

| 200 | 2026-02-03 | IoNDB | `coq-flocq` not found: "No package named coq-flocq found" after `opam install` | `coq-flocq` is NOT in the default opam.ocaml.org repository; it requires the Coq released opam repo (`coq.inria.fr/opam/released`) which returns HTTP 503 | Cascading fallback: try HTTPS endpoints, then clone GitHub mirror (`github.com/coq/opam` → `released/` directory as local opam repo); bumped cache key to v3 |
| 201 | 2026-02-04 | 82WIW | `apply vec3_eq; ring` fails: "not a valid ring equation" | `apply vec3_eq` introduces `v3x (mkVec3 0 0 0)` on RHS; `ring` can't handle unreduced record projections | Always `apply vec3_eq; simpl; ring` — existing codebase proofs consistently used this pattern |
| 202 | 2026-02-04 | 82WIW | `look_at(eye, target, up)` proofs blocked by sqrt/normalize | Coq cannot reason about `sqrt` algebraically (transcendental, axiomatized) | Parameterize as `look_at(s, u, f, eye)` with pre-computed orthonormal basis; proves all structural properties |

| 203 | 2026-02-05 | WV5K1 | `Rfloor` not in Coq 8.18 standard Reals library | `Rfloor` is defined in project Utils.v (via `IZR (Int_part x)`), not in the standard library | Always check `Utils.v` for custom real analysis definitions before assuming standard library provides them |
| 204 | 2026-02-05 | WV5K1 | `Rfloor_spec` and `Rfloor_eq` missing from Utils.v | Vec2/Vec3 fract proofs need combined floor bound and floor-in-[0,1) lemmas | Added `Rfloor_spec` (combines `Rfloor_le` + `Rfloor_lt_succ`) and `Rfloor_eq` (uses `Int_part_spec`) to Utils.v |
| 205 | 2026-02-05 | WV5K1 | `Int_part_tech` doesn't exist in Coq 8.18; use `Int_part_spec` instead | `Int_part_spec` takes `(r - 1 < IZR z <= r) -> z = Int_part r` — note reversed direction vs typical tech lemma | Use `assert (H: 0%Z = Int_part x). { apply Int_part_spec. simpl. lra. }` then `rewrite <- H` |
| 206 | 2026-02-05 | WV5K1 | `replace (_ - _) with (- (_ - _))` pattern fails with multiple R variables in scope | Coq cannot disambiguate which `_ - _` to replace when 4+ R subtractions are in the goal | Use explicit terms: `replace (br - ar) with (- (ar - br)) by ring` instead of wildcard `_` patterns |
| 207 | 2026-02-05 | WV5K1 | `exfalso; lra` wrong when premises give `x >= 0` and `x <= 0` (means `x = 0`, not False) | `Rle_dec x 0` returns `left: x <= 0` which combined with `x >= 0` gives `x = 0`, not contradiction | Use `assert (x = 0) by lra; subst` then handle the zero case, don't assume contradiction |
| 208 | 2026-02-05 | WV5K1 | `ring` cannot handle division; use `field` for goals with `/` | `rect_scale_from_center_identity` has `rx + rw / 2 - rw * 1 / 2` which requires `field`, not `ring` | Always use `field` for equalities involving division; `ring` only handles +, -, * |
| 209 | 2026-02-05 | WV5K1 | VERIFICATION_COVERAGE.md was massively stale: 27+ operations listed "Not verified" already had proofs | Vec3 had 12 operations listed as unverified that ALL had Coq proofs (lerp, min, max, abs, clamp, etc.) | Coverage went from 178/255 (69.8%) to 205/255 (80.4%) — majority from fixing documentation, not writing new proofs |
| 210 | 2026-02-05 | WV5K1 | `color_lerp` uses `(b - a) * t` not `t * (b - a)` in its definition | `replace` patterns must match actual term order after `unfold`+`simpl` | Always check definition order before writing `replace` — read the .v spec file first |
| 211 | 2026-02-05 | Resp0 | `ring` fails on decimal↔fraction equivalence (`0.2126` vs `2126/10000`) | `ring` normalizes polynomials over abstract reals; decimal literals are opaque | Use `lra` which handles linear real arithmetic including decimal/fraction equivalences |
| 212 | 2026-02-05 | Resp0 | `f_equal` chaining fails for 4-tuple equality (`color_to_rgba`) | `f_equal; [|f_equal; [|f_equal]]; ring` gives "Incorrect number of goals" on 4-tuples | Use sequential `replace` per component: `replace (1-(1-cr)) with cr by ring. ... reflexivity.` |
| 213 | 2026-02-05 | Resp0 | Robust `Rabs` proof: match-replace-unfold-destruct pattern | `rewrite Rabs_Ropp` fails when subterm doesn't match `Rabs (- ?M)` syntactically | `match goal with \|- Rabs ?x = _ => replace x with val by lra end. unfold Rabs. destruct (Rcase_abs val); lra.` |
| 214 | 2026-02-05 | Resp0 | `color_scale` scales ALL 4 components including alpha | Theorem incorrectly stated `color_a c` for alpha of scaled result | Correct: `color_a (color_scale c s) = color_a c * s`; read definition carefully before writing theorem |
| 215 | 2026-02-05 | Resp0 | `apply vec3_eq; ring` fails — needs `simpl` between | After `apply vec3_eq`, goals have unevaluated record projections `v3x (mkVec3 ...)` | Always `apply vec3_eq; simpl; ring` — `simpl` reduces the projections first |
| 216 | 2026-02-05 | Resp0 | `mat4_scale` not `mat4_scalar_mul` — wrong function name from memory | Assumed name without checking; caused `The reference mat4_scalar_mul was not found` | Always `grep 'Definition mat4_' file.v` to confirm exact definition name |
| 217 | 2026-02-05 | Resp0 | `bounds_contains` not `bounds_contains_point` — wrong predicate name | Assumed Bounds containment was named `bounds_contains_point`; actual is `bounds_contains` | Always check `.v` spec file for exact definition name before using |
| 218 | 2026-02-05 | Resp0 | Duplicate theorem name collision causes `already exists` error | `color_luminance_black` existed at line 202 and was re-added at line 1382 | ALWAYS `grep '^Theorem\|^Lemma' file.v` before adding new theorems; catch collisions early |
| 219 | 2026-02-05 | Resp0 | Modeling `get_scale` as `get_scale_sq` (length-squared) avoids sqrt | Coq cannot reason algebraically about `sqrt` (transcendental) | Use sum-of-squares `m0²+m1²+m2²` instead of `sqrt(m0²+m1²+m2²)`; proves all algebraic properties |
| 220 | 2026-02-05 | Resp0 | `lra` fails on nonlinear products; `ring` fails on linear comparisons | `1*1+0*0+0*0=1` needs `ring`; `Rle` needs `lra`; `Rle_0_sqr` needs neither | Match tactic to goal structure: `ring` for polynomial equality, `lra` for linear inequality, specialized lemmas for sum-of-squares |

| 221 | 2026-02-05 | 1WDWU | Color HSL operations (to_hsl, from_hsl, with_lightness, with_saturation, with_hue, rotate_hue) are purely algebraic — NO transcendental functions | Previously categorized as "transcendental-blocked" in verification docs, blocking Kani verification | Analysis of `color.rs` showed only arithmetic, comparisons, `rem_euclid` — enabled 9 new Kani harnesses covering 6 previously "unverifiable" operations |
| 222 | 2026-02-05 | 1WDWU | `nia` (nonlinear integer arithmetic) fails on degree-4+ polynomial constraints in Coq Z proofs | `reflect_involutive` required `a - 2*d*nx + 2*(2*d*nx - a)*nx*nx = a` with `nx*nx + ny*ny = 1` — degree-5 polynomial | Avoid degree-4+ nia proofs; decompose into unconditional `ring` identities (e.g., `reflect_dot_relation`) |
| 223 | 2026-02-05 | 1WDWU | `simpl` normalizes `2*d` to `d+d` in Coq Z, breaking syntactic `set`/`rewrite` pattern matching | After `simpl`, `set (d := zvec2_dot a n)` couldn't find `2*d` because it became `d+d` in the goal | Either avoid `simpl` before `set`, or use `cbn [specific_functions]` for targeted reduction |
| 224 | 2026-02-05 | 1WDWU | `Z.eqb_neq` rewrite requires hypothesis of form `(z =? z0) = false`, not `z <> 0` | `rewrite Z.eqb_neq in Hne` failed because Hne was `vx*vx + vy*vy <> 0`, not a `=? = false` form | Use `destruct (expr =? 0)%Z eqn:E` directly, then `apply Z.eqb_eq in E; contradiction` for true branch |
| 225 | 2026-02-05 | 1WDWU | Update script `update-verification-counts.sh` missed two sed patterns for docs/README.md and FLOATING_POINT_VERIFICATION.md | docs/README.md used `N theorems R+Z` format; FP_VERIFICATION.md used `N theorems/harnesses` format — neither matched existing sed patterns | Added `s/[0-9]+ theorems R\+Z/` and `s/\| [0-9]+ theorems\/harnesses/` patterns to cover all documentation formats |

| 226 | 2026-02-05 | 1WDWU | `f32::rem_euclid(360.0)` can return exactly `360.0` — documented Rust stdlib FP edge case | Kani found counterexample for `assert!(h < 360.0)` after `rem_euclid(360.0)` | Use `<= rhs` not `< rhs` when checking `rem_euclid` output; Rust docs: "can result in the modulus being equal to the divisor" |
| 227 | 2026-02-05 | 1WDWU | HSL `q = l + s - l*s` can exceed 1.0 in f32 when l ≥ 0.5; `hue_to_rgb` amplifies by 6x | Kani found `to_color()` producing RGB slightly > 1.0 + 1e-6; the `p + (q-p)*6*t` formula magnifies the q overshoot | Use tolerance ≥ 1e-4 for HSL-to-RGB range assertions; never assume algebraically-bounded FP results are exactly bounded |
| 228 | 2026-02-05 | 1WDWU | `(x + w) - x ≠ w` in f32 when `\|x\|` >> `w` (catastrophic cancellation in Rect::intersection self-test) | `intersection` computes `width = (x+w).min(x+w) - x.max(x)` = `(x+w) - x` which rounds differently than `w` | Use approximate equality (tolerance ≈ 1 ULP at given magnitude) for dimension assertions after add-then-subtract sequences |
| 229 | 2026-02-05 | 1WDWU | VERIFICATION_COVERAGE.md inflated by ~15 phantom operations (Coq-only definitions not in Rust API) | Many ops listed (Vec2: rejection/min_element/max_element/element_sum/fract; Color: mix/darken/lighten/saturate/desaturate/contrast) have Coq proofs but no `pub fn` in Rust | Total is ~241 real Rust ops, not 256; both numerator and denominator inflated equally so ~85% coverage figure is approximately correct |
| 230 | 2026-02-05 | 1WDWU | `fmodf` (C math library) is **not modeled** by CBMC (Kani's backend) — `f32::rem_euclid` and `f32 % f32` call `fmodf` | Kani harness `verify_hsl_rotate_hue_in_range` failed persistently despite correct tolerance; CBMC returns nondeterministic values for unmodeled functions | Never assert on the output of `rem_euclid` or `%` on floats in Kani harnesses; verify structural properties (s/l preservation) instead; prove range in Coq |
| 231 | 2026-02-05 | 1WDWU | CBMC SAT solver times out on tight FP range bounds with complex branching (CBMC issue #4337) | `verify_hsl_to_color_normalized` with ±1e-4 bounds on 3 calls to 4-branch `hue_to_rgb` exceeded 300s CI timeout | Use `#[kani::solver(cadical)]` for FP-heavy harnesses + wide bounds (e.g., [-1.0, 2.0]); prove tight bounds in Coq instead |
| 232 | 2026-02-05 | 1WDWU | Kani/CBMC verification tool division of labor: Kani excels at bit-precise structural/NaN/finiteness properties; Coq excels at tight mathematical bounds | Attempting tight FP range proofs in Kani hit fundamental CBMC limitations (fmodf unsupported, FP bit-blasting timeout) | Design Kani harnesses for IEEE 754 edge-case safety (NaN, infinity, structural invariants); design Coq proofs for mathematical range/correctness properties |

| 233 | 2026-02-09 | PNhXS | Non-existent CLI flags in TROUBLESHOOTING.md (--max-commits, --show-fps, --show-filenames, --show-usernames, --show-tree, --start-position, --log-format) | Docs written speculatively without verifying `args/mod.rs` | Removed or replaced all 7+ false flags with correct alternatives |
| 234 | 2026-02-09 | PNhXS | Wrong WASM API method names in RUNBOOK.md (getEntityCount, isGPUPhysicsActive, getLastFrameTime, getFileCount, getDirCount, getUserCount, getCommitQueueSize, getPlaybackSpeed, setSecondsPerDay) | Names guessed from conventions | Fixed all 8+ to actual exported names from `wasm_api/` |
| 235 | 2026-02-09 | PNhXS | JS API constructor `new Rource(canvas)` in README.md never existed | Docs assumed constructor pattern | Changed to `await Rource.create(canvas)` matching `lib.rs` |
| 236 | 2026-02-09 | PNhXS | Renderer trait signatures wrong in ARCHITECTURE.md and RENDERING.md | Documented from memory not source | Fixed all signatures against `pub trait Renderer` in `rource-render/src/lib.rs` |
| 237 | 2026-02-09 | PNhXS | Backend selection order wrong in RENDERING.md | Assumed WebGL2 first; actual is wgpu first | Corrected to match `Rource::create()` initialization sequence |
| 238 | 2026-02-09 | PNhXS | `getRendererType()` return strings documented as PascalCase | Convention assumed incorrectly | Fixed to lowercase: `"wgpu"`, `"webgl2"`, `"software"` |
| 239 | 2026-02-09 | PNhXS | ADR 0004 (generation counter) accepted but never implemented | LabelPlacer uses `Vec::clear()` not generation counters | Changed status to Superseded with implementation note |
| 240 | 2026-02-09 | PNhXS | CONTRIBUTING.md JS directory tree had 12 entries, actual has 30+ | Never updated as files added | Rewrote entire tree from `find` output |
| 241 | 2026-02-09 | PNhXS | GOURCE_COMPARISON.md listed background-image, logo, highlight-users as "roadmap" | Features implemented but status not updated | Removed from roadmap, updated parity to ~90% |
| 242 | 2026-02-09 | PNhXS | `getMetrics()` in TELEMETRY.md — actual method is `getFrameStats()` | API renamed, docs not updated | Global replace across file |
| 243 | 2026-02-09 | PNhXS | Broken link `performance/FORMAL_PROOFS.md` in docs/README.md | Path changed, cross-ref not updated | Fixed to `performance/formal-proofs/README.md` |
| 244 | 2026-02-09 | PNhXS | Per-file verification counts drifted (Vec2 Verus: 55→61, Color: 57→64, Coq-Z totals: 417→471) | Phase 1 update missed per-file granular counts | Fixed in VERUS_PROOFS.md and COQ_PROOFS.md |
| 245 | 2026-02-09 | PNhXS | Subagent reported `getDetailedFrameStats` as non-existent but it exists at `lib.rs:1042` | Agent error in verification | Cross-checked all agent-reported violations before applying |
| 246 | 2026-02-09 | PNhXS | Files with most violations: TROUBLESHOOTING.md (7+), RUNBOOK.md (8+), RENDERING.md (5+), ARCHITECTURE.md (5+) | Implementation-detail docs drift fastest | Prioritize these in future audits |
| 247 | 2026-02-09 | ykbr1 | `render_phases.rs` was refactored into `render_phases/` directory but 30+ docs still referenced the old monolithic file | Module refactors must trigger docs grep-and-replace | After any file→directory refactor, grep all .md files for the old path |
| 248 | 2026-02-09 | ykbr1 | Coq constructor names in paper docs were fabricated (mk_vec2 vs actual mkVec2, vx vs vec2_x, mat3_det vs mat3_determinant) | Paper examples written from memory, not copied from source | Always copy Coq snippets directly from .v source files |
| 249 | 2026-02-09 | ykbr1 | `mat3_cofactor` function referenced in TEN_OPERATION_AUDIT.md does not exist — actual mat3_inverse uses inline cofactor computation | Docs described abstracted version of algorithm instead of actual code | For "line-by-line correspondence" docs, literally copy from source |
| 250 | 2026-02-09 | ykbr1 | WCAG_COMPLIANCE.md claimed passing axe/Lighthouse scores but no testing was ever performed | Aspirational results presented as actual | Always mark unverified results as "Not Yet Tested" |
| 251 | 2026-02-09 | ykbr1 | SUPPLY_CHAIN.md claimed SLSA Level 3 "implements" but no releases published — provenance never generated | Future capability described in present tense | Use "configured for" not "implements" when prerequisite (release) hasn't occurred |
| 252 | 2026-02-09 | ykbr1 | `--max-commits` CLI flag referenced in 4 files but never existed in args/mod.rs | Speculative flag from Gource compatibility assumption | Verify every CLI flag against args/mod.rs before documenting |
| 253 | 2026-02-09 | ykbr1 | `setBloomEnabled()`, `setUseLOD()`, `getEntityCount()` WASM methods in docs were fabricated names | Methods named by convention rather than verified | Always grep `wasm_bindgen(js_name` for actual exported names |
| 254 | 2026-02-09 | ykbr1 | BENCHMARK_DASHBOARD.md listed fabricated `spatial_perf` benchmark that never existed | Benchmark list not verified against actual benches/ directory | `ls crates/*/benches/` is the ground truth for benchmark names |
| 255 | 2026-02-09 | ykbr1 | bench-pr.yml described as automatic PR trigger but actual trigger is `workflow_dispatch` (manual only) | CI docs assumed desired behavior was actual behavior | Read .github/workflows/ YAML to verify trigger configuration |
| 256 | 2026-02-09 | ykbr1 | Bounds type NOT extracted by RourceMath_Extract.v but 3 paper docs claimed "8 types extracted" | Extraction count taken from Z-compute file count (9) not import list (8) | Check RourceMath_Extract.v imports, not _Compute.v file count |
| 257 | 2026-02-09 | ykbr1 | PERFORMANCE_REPORT.md Phase 27 references wrong: Phase 27 is "Texture state management", not sqrt optimization or bloom | Phase numbers assigned without checking CHRONOLOGY.md | Always verify phase numbers against CHRONOLOGY.md |
| 258 | 2026-02-09 | ykbr1 | BENCHMARK_METHODOLOGY.md claimed "Software renderer only" but wgpu backend provides GPU acceleration | Stale from early project state when only software renderer existed | Architecture claims must be updated when new backends are added |

| 259 | 2026-02-09 | tuwZp | Verus uses `proof fn` keyword, NOT `#[verifier::proof]` attribute | Paper ARCHITECTURE.md described Verus annotation syntax from older/deprecated version | Always verify tool syntax against actual proof files (e.g., `grep 'proof fn' proofs/*.rs`), not memory or external docs |
| 260 | 2026-02-09 | tuwZp | FP_Common.v uses named constants `prec32`/`emin32`/`fexp32`, not inline `binary32 := FLT_exp (-149) 24` | Paper simplified the Coq definition for exposition but crossed into inaccuracy | For code snippets claiming "verbatim from source", always diff against the actual `.v` file |
| 261 | 2026-02-09 | tuwZp | Kani proofs live in `crates/rource-math/src/kani_proofs/` directory (10 files), not single `kani_proofs.rs` file | Module refactored from single file to directory; grep commands referencing old path were wrong | After any file→directory refactoring, update ALL grep/counting commands in docs |
| 262 | 2026-02-09 | tuwZp | SPEC_IMPL_CORRESPONDENCE.md had ALL 8 Coq Record field names wrong (used abbreviated forms: `vx`/`vy`, `cr`/`cg`/`cb`/`ca`, `m00`..`m22`) | Field names written from memory, never verified against actual `.v` definitions | ALWAYS read the `Record` definition in the actual `.v` file; field names are: `vec2_x`/`vec2_y`, `color_r`/`color_g`/`color_b`/`color_a`, `m0`..`m8`/`m15` |
| 263 | 2026-02-09 | tuwZp | `Utils.v` MUST compile before Vec2.v, Vec3.v, Vec4.v (they `Require Import RourceMath.Utils`) | 4 build commands across 3 docs had Utils.v listed LAST in compilation order | Coq compilation order follows `Require Import` dependency chain; always verify with `grep 'Require Import' *.v` |
| 264 | 2026-02-09 | tuwZp | FORMAL_VERIFICATION.md per-file Z-compute breakdown was stale: Vec2(62→76), Rect(51→79) but total still claimed 471 | Per-file counts not updated when theorems were added; stale values summed to 429, not 471 | Cross-check that per-file breakdowns actually SUM to the claimed total; this catches silent staleness |
| 265 | 2026-02-09 | tuwZp | RENDERING_BOTTLENECK_ANALYSIS.md "After" code snippet was stale: showed `effective_radius * 2.0` but actual code uses `effective_radius * 1.5` with `>= 3.0` LOD gate (Phase 70) | Code optimization applied but doc not updated | Before/after code snippets in analysis docs must be re-verified after optimization phases that touch the same code |
| 266 | 2026-02-09 | tuwZp | BENCHMARKS.md test count "now 2,076" was severely stale (actual: 2964) | Test count snapshot taken early and never updated | Use rounded display strings ("2900+") that resist fluctuation, or automate via `update-doc-metrics.sh` |
| 267 | 2026-02-09 | tuwZp | File paths missing `crates/` prefix (e.g., `rource-core/src/scene/mod.rs` → `crates/rource-core/src/scene/mod.rs`) | Shorthand path written without repo-root prefix | ALWAYS use full path from repo root; add `crates/` prefix for all crate source paths |

| 268 | 2026-02-11 | Vlgem | WASM demo black canvas: bloom FBO init failed but `config.enabled` stayed `true` | `BloomConfig::default()` sets `enabled: true`; `initialize()` failure logged warning but didn't disable config | On non-fatal init failure, ALWAYS set `config.enabled = false`; never leave feature enabled + uninitialized |
| 269 | 2026-02-11 | Vlgem | `begin_frame()` checked `config.enabled`, `end_frame()` checked `is_active()` — state predicate mismatch | Two frame boundaries used different predicates to gate the same offscreen FBO pipeline | Both frame boundaries MUST use the same predicate (`is_active()` checks both `enabled` AND `initialized`) |
| 270 | 2026-02-11 | Vlgem | `clippy::too_many_lines` triggered after adding 4 lines to WebGL2Renderer::new() (103/100) | Function was at 99 lines, 4-line fix pushed it over | Extract cold-path setup (context options) into helper when function approaches line limit |
| 271 | 2026-02-11 | Vlgem | Performance impact must be calculated exactly: 2 extra `bool` ANDs = 2 clock cycles = ~0.66ns = 0.003% of 20µs budget | Hot-path changes need cycle-level impact analysis, not "negligible" hand-waving | Calculate exact cycle count for hot-path changes: instruction count × clock period |
| 272 | 2026-02-11 | Vlgem | CSS design token migration: 23 hardcoded font-size values in insights.css replaced with `var(--font-size-*)` tokens | Component CSS files used raw px/rem values instead of variables.css tokens | Audit CSS with `grep -rn` for hardcoded values; ALL must use design system tokens |
| 273 | 2026-02-11 | Vlgem | Decorative SVGs missing `aria-hidden="true"` — 20 instances across index.html | SVG icons added without accessibility attributes | Every decorative SVG MUST have `aria-hidden="true"`; functional SVGs need `aria-label` |
| 274 | 2026-02-11 | Vlgem | `is_bloom_enabled()` returned `config.enabled` not `is_active()` — misled callers about actual state | API method exposed config flag without checking initialization state | Public `is_X_enabled()` methods must reflect actual operational state, not just config intent |

| 275 | 2026-02-11 | rMfEz | wgpu backend had SAME `begin_frame`/`end_frame` predicate mismatch as WebGL2 — used `self.bloom_enabled` boolean instead of `pipeline.is_active()` | Pattern fixed in WebGL2 but not propagated to wgpu backend in same session | When fixing a rendering bug in one backend, ALWAYS audit ALL backends for the same pattern |
| 276 | 2026-02-11 | rMfEz | wgpu `set_bloom_enabled(true)` didn't disable flag if pipeline init failed silently | `BloomPipeline::new()` succeeded but `is_active()` could be false if textures not allocated | Add defense-in-depth: after init attempt, check `is_active()` and disable flag if false |
| 277 | 2026-02-11 | rMfEz | Analytics dashboard scrolling broken: `grid-template-rows` not set for `view-analytics` layout | `.app-container` has `overflow: hidden`; without `grid-template-rows: 1fr`, the grid row uses `auto` sizing which grows unbounded then gets clipped | Grid containers with `overflow: hidden` need explicit row sizing for scroll containers to work |
| 278 | 2026-02-11 | rMfEz | `@media (prefers-color-scheme: light)` block in accessibility.css duplicated 57 lines already in themes.css | Accessibility file copied light theme definitions for OS-level preference detection | Canonical light theme lives in themes.css; never duplicate theme definitions across files |
| 279 | 2026-02-11 | rMfEz | 42 decorative SVGs still missing `aria-hidden="true"` after previous session fixed 20 | Previous audit found 20, deeper audit found 59 more; only 42 still needed after existing fixes | Use `grep -c` to count ALL instances before and after; partial audits compound technical debt |
| 280 | 2026-02-11 | rMfEz | `color-mix(in srgb, var(--token) N%, transparent)` replaces hardcoded `rgba(r, g, b, N%)` for theme-aware overlays | Hardcoded rgba values don't respond to theme changes | Use `color-mix()` for semi-transparent overlays derived from design tokens |
| 281 | 2026-02-11 | rMfEz | Focus ring fallback `#e94560` in accessibility.css should be `var(--accent)` not `var(--accent-primary, #e94560)` | `--accent-primary` is not a defined token; `--accent` is the correct token name | Always verify token names against variables.css before using them |
| 282 | 2026-02-11 | rMfEz | Clippy prefers `is_some_and(Type::method)` over `is_some_and(\|x\| x.method())` — redundant closure lint | Rust 1.93 clippy enforces `redundant_closure_for_method_calls` | Use method references with `is_some_and()` instead of closures when the closure just calls one method |

---

*Last updated: 2026-02-11 | 282 entries | 15 categories*
