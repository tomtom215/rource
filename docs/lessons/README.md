# Lessons Learned Knowledge Base

> **Purpose**: Categorized reference for every lesson learned across all development sessions.
> Updated every session. Indexed for quick AI and human lookup.
>
> **How to use**: Search by domain category or browse the chronological audit log.
> New entries go in BOTH the appropriate category file AND the chronological log.

---

## Table of Contents

### Quick Reference (this file)
1. [Decision Tables](#decision-tables-quick-reference)

### By Domain
2. [Formal Verification](formal-verification.md) — Coq, Verus, Kani, FP, IEEE 754, Landscape, Extraction
3. [Development Practices](development-practices.md) — Tools, Shell, CI, Doc Automation, Auditing, Measurement

### Full History
4. [Chronological Audit Log](chronological-log.md) — All 291 entries in date order

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

*Last updated: 2026-02-11 | 291 entries across 4 files | 15 categories*
*Files: [formal-verification.md](formal-verification.md) | [development-practices.md](development-practices.md) | [chronological-log.md](chronological-log.md)*
