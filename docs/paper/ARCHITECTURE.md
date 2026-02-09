# Section 3: Triple-Verification Architecture

*Draft for CPP 2027 submission. Target length: ~2.5 pages.*

---

## 3.1 Design Rationale

The triple-verification architecture arises from a fundamental observation:
no single verification tool adequately covers the correctness spectrum of a
production floating-point math library.

| Correctness Aspect | Verus (SMT) | Coq (ITP) | Kani (BMC) |
|--------------------|-------------|-----------|------------|
| Algebraic properties | **Strong** | **Strong** | Bounded only |
| Mathematical proof objects | No (SMT trace) | **Yes** (kernel-checked) | No (SAT model) |
| IEEE 754 edge cases | Cannot model | Via Flocq only | **Native** |
| Universal quantification | **Yes** (over int) | **Yes** (over R/Z) | No (bounded domain) |
| Direct Rust verification | **Yes** (ghost code) | No (separate spec) | **Yes** (MIR) |
| Proof speed | Fast (~1s) | Moderate (~45s total) | Slow (~minutes each) |
| Trusted base size | Z3 + Verus | Coq kernel (small) | CBMC + Kani |

The three tools form a verification triangle where each tool's limitations
are covered by the other two:

```
             Verus (SMT)
            /          \
           / Algebraic   \
          /   over int    \
         /                 \
   Coq (ITP) ————————— Kani (BMC)
   Machine-checked      Bit-precise
   proofs over R        IEEE 754 f32
   + FP error bounds    + bounded domain
```

## 3.2 Verification Layers

### Layer 1: Verus Algebraic Proofs (498 proof functions)

Verus specifications model each type as an integer-field struct:
```rust
pub struct SpecVec2 { pub x: int, pub y: int }
pub struct SpecMat3 { pub m00: int, ..., pub m22: int }
```

Properties verified include:
- **Algebraic structure**: Commutativity, associativity, identity, inverses
- **Domain properties**: Determinant identities, orthogonality, interpolation bounds
- **Cross-type**: Matrix-vector transform correctness, type conversion consistency

Verus proof functions are annotated with `#[verifier::proof]` and use
`ensures` clauses specifying the postcondition. Most proofs are discharged
automatically by Z3; complex polynomial identities require the lemma
decomposition technique described in Section 4.1.

**Organization**: 11 proof files in `crates/rource-math/proofs/`:
```
vec2_proofs.rs  vec3_proofs.rs  vec4_proofs.rs
mat3_proofs.rs  mat3_extended_proofs.rs
mat4_proofs.rs  mat4_extended_proofs.rs
color_proofs.rs rect_proofs.rs bounds_proofs.rs utils_proofs.rs
```

The split into base and extended files (Mat3, Mat4) is necessitated by Z3
resource limits: combining polynomial identity proofs with simpler algebraic
proofs in a single file exceeds Z3's default resource budget.

### Layer 2: Coq Machine-Checked Proofs (2,198 theorems)

The Coq development comprises three sub-layers:

**Layer 2a: R-abstract specifications (1,366 theorems)**

Each type is modeled as a Coq Record with real-number fields:
```coq
Record Vec2 : Type := mkVec2 { vec2_x : R; vec2_y : R }.
Record Mat3 : Type := mkMat3 { m0 : R; m1 : R; m2 : R; m3 : R; m4 : R; m5 : R; m6 : R; m7 : R; m8 : R }.
```

Theorems prove properties over the field of reals, leveraging Coq's
standard library (`Reals`). Proof tactics include:
- `ring` and `field` for algebraic identities
- `lra` (linear real arithmetic) for inequalities
- Custom `Ltac` for domain-specific properties (e.g., matrix cofactor patterns)

**Layer 2b: Z-computational bridge (471 theorems)**

A parallel development models fields as integers (Z) for extractability:
```coq
Record ZVec2 : Type := mkZVec2 { zvec2_x : Z; zvec2_y : Z }.
```

Where division is needed (e.g., color normalization), we use scaled
fixed-point arithmetic with explicit scale factors.

Bridge theorems establish correspondence between R and Z layers
(e.g., `zvec2_add_correct: zvec2_add maps to vec2_add under embedding`).

**Layer 2c: Flocq FP error bounds (361 theorems)**

Using Flocq 4.1.3, we establish IEEE 754 binary32 error bounds:
```coq
Definition binary32 := FLT_exp (-149) 24.
Definition round32 := round radix2 binary32 rndNE.
```

Error bound theorems follow the pattern:
```coq
Theorem add_error: forall x y : R,
  Rabs (round32 (x + y) - (x + y)) <= /2 * ulp radix2 binary32 (x + y).
```

Composition theorems accumulate error through operation chains.

**Organization**: 46 Coq files, compiled in ~45 seconds:
```
Spec files (9):    Vec2.v Vec3.v Vec4.v Mat3.v Mat4.v Color.v Rect.v Bounds.v Utils.v
Proof files (10):  Vec2_Proofs.v Vec3_Proofs.v ... Bounds_Proofs.v Complexity.v Vec_CrossType.v
Compute files (9): Vec2_Compute.v Vec3_Compute.v ... Bounds_Compute.v Utils_Compute.v
FP files (9):      FP_Common.v FP_Rounding.v FP_ErrorBounds.v FP_Vec.v FP_Mat.v
                   FP_Color.v FP_Rect.v FP_Bounds.v FP_Utils.v
Extract files (9): Vec2_Extract.v ... Rect_Extract.v RourceMath_Extract.v Vec2_VerifiedExtract.v
```

### Layer 3: Kani Bit-Precise Verification (272 harnesses)

Kani proof harnesses annotated with `#[kani::proof]` execute actual Rust
functions on symbolic f32 inputs within bounded domains:

```rust
#[kani::proof]
fn verify_vec2_dot_finite() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    kani::assume(ax.is_finite() && ay.is_finite());
    kani::assume(ax.abs() < SAFE_BOUND_2 && ay.abs() < SAFE_BOUND_2);
    // ... similar for b
    let result = a.dot(&b);
    assert!(result.is_finite());
}
```

Safe bound constants are calibrated per operation arity:
- `SAFE_BOUND_2 = 1e18` for 2-component products (e.g., Vec2::dot)
- `SAFE_BOUND_3 = 1e12` for 3-component products (e.g., Vec3::dot)
- `SAFE_BOUND_4 = 1e9` for 4-component products (e.g., Vec4::dot)

These bounds ensure that intermediate products do not overflow f32's range
(approximately ±3.4 × 10^38).

**Organization**: 9 modules in `crates/rource-math/src/kani_proofs/`:
```
vec2.rs vec3.rs vec4.rs mat3.rs mat4.rs color.rs rect.rs bounds.rs utils.rs
```

## 3.3 Cross-Tool Correspondence

A critical aspect of the architecture is that all three tools verify
properties of the *same* Rust implementation. The correspondence is:

| Aspect | Verus | Coq | Kani |
|--------|-------|-----|------|
| Specification target | Ghost `SpecVec2` (int) | `Record Vec2` (R/Z) | Actual `Vec2` (f32) |
| Connection to impl | Same Rust file, ghost annotations | Manual translation | Direct (MIR) |
| What constitutes a "bug" | Spec violation | Proof failure | Assertion failure |
| Guarantees if all pass | Property holds for int model | Property holds for R model + FP error bounded | Property holds for f32 in bounded domain |

When all three tools verify the same property (e.g., `Vec2::add` commutativity):
- Verus: `spec_vec2_add(a,b) == spec_vec2_add(b,a)` for all `int` values
- Coq: `vec2_add_comm: vec2_add a b = vec2_add b a` for all `R` values
- Kani: `a + b == b + a` for all `f32` values with `|x| < 1e6`
- Coq (Flocq): `|round32(x+y) - (x+y)| <= eps` quantifying the f32 deviation

## 3.4 Coverage Statistics

| Type | Verus | Coq (R) | Coq (Z) | Coq (FP) | Kani | Total | % of Ops |
|------|-------|---------|---------|----------|------|-------|----------|
| Vec2 | 61 | 139 | 76 | — | 35 | 311 | 79% |
| Vec3 | 61 | 133 | 54 | — | 37 | 285 | 100% |
| Vec4 | 55 | 96 | 39 | — | 25 | 215 | 96% |
| Mat3 | 48 | 102 | 25 | — | 23 | 198 | 95% |
| Mat4 | 54 | 208 | 50 | — | 32 | 344 | 85% |
| Color | 64 | 164 | 60 | — | 47 | 335 | 87% |
| Rect | 52 | 218 | 79 | — | 35 | 384 | 66% |
| Bounds | 70 | 136 | 70 | — | 27 | 303 | 100% |
| Utils | 33 | 59 | 18 | — | 11 | 121 | 100% |
| Complexity | — | 60 | — | — | — | 60 | — |
| CrossType | — | 51 | — | — | — | 51 | — |
| FP Layer | — | — | — | 361 | — | 361 | — |
| **Total** | **498** | **1,366** | **471** | **361** | **272** | **2,968** | **85.5%** |

**Zero admits across all tools.** Verified by automated check:
```bash
grep -rn 'admit\|Admitted\|assume!' crates/rource-math/proofs/ | wc -l  # 0
```

---

*Word count: ~1100 (target: ~1200-1500 for 2.5-page architecture section)*
*Figures needed: Verification triangle diagram, layer dependency graph,
per-type coverage heatmap*
