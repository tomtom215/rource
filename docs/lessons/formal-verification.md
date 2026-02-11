# Lessons Learned: Formal Verification

> Part of the [Lessons Learned Knowledge Base](README.md).
> Categories: Coq, Verus, Kani, Floating-Point, IEEE 754, Rust Verification Landscape, Coq Extraction.
>
> New entries should also be added to the [Chronological Audit Log](chronological-log.md).

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
| 185 | `Rdiv_lt_1` not standard Coq — rewrite using `Rmult_lt_compat_r` | FP_Utils.v theorem on `u32 / (1 + u32) < 1` needed non-standard lemma | `Rmult_lt_compat_r` + `Rinv_r` pattern: multiply both sides by `/(1+u32)`, rewrite `(1+u32) * /(1+u32)` to 1 |

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

*Part of the [Lessons Learned Knowledge Base](README.md) | [Chronological Log](chronological-log.md) | [Development Practices](development-practices.md)*
