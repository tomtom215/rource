# Verus Proofs for rource-math

This document details all Verus formal verification proofs for the `rource-math` crate.

For an overview of the complete verification effort (Verus + Coq), see
[FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md).

## Verification Tool

**Verus** (https://github.com/verus-lang/verus)
- Version: 0.2026.01.23.1650a05
- SMT Solver: Z3
- Toolchain: Rust 1.92.0

## Verified Properties

### Vec2 (55 Proof Functions, 87+ Verification Conditions)

All proofs verified with `0 errors`.

#### Algebraic Properties (Vector Space Axioms)

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 1 | Addition Commutativity | a + b = b + a |
| 2 | Addition Associativity | (a + b) + c = a + (b + c) |
| 3 | Additive Identity | a + 0 = a |
| 4 | Additive Inverse | a + (-a) = 0 |
| 5 | Scalar Associativity | (s * t) * v = s * (t * v) |
| 6 | Scalar Distribution | s * (a + b) = s * a + s * b |
| 7 | Scalar Addition Distribution | (s + t) * v = s * v + t * v |
| 8 | Scalar Identity | 1 * v = v |
| 9 | Scalar Zero | 0 * v = 0 |

#### Geometric Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 10 | Dot Product Commutativity | a . b = b . a |
| 11 | Dot Product Linearity | (s * a) . b = s * (a . b) |
| 12 | Dot Product Distribution | (a + b) . c = a . c + b . c |
| 13 | Cross Product Anti-symmetry | a x b = -(b x a) |
| 14 | Cross Self Zero | a x a = 0 |
| 15 | Perpendicular Orthogonality | perp(a) . a = 0 |
| 16 | Double Perpendicular | perp(perp(a)) = -a |

#### Length Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 17 | Length Squared Non-negative | \|a\|^2 >= 0 |
| 18 | Length Squared Zero iff Zero | \|a\|^2 = 0 <=> a = 0 |

#### Additional Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 19 | Subtraction Equivalence | a - b = a + (-b) |
| 20 | Component Multiplication Commutativity | a * b = b * a |
| 21 | Cross-Perp Relationship | a x b = perp(a) . b |
| 22 | Negation as Scaling | -v = (-1) * v |
| 23 | Vector Space Structure | Combined axiom verification |

#### Min/Max/Abs Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 24 | Splat Zero | splat(0) = zero vector |
| 25 | Min Commutativity | min(a, b) = min(b, a) |
| 26 | Max Commutativity | max(a, b) = max(b, a) |
| 27 | Min Idempotent | min(a, a) = a |
| 28 | Max Idempotent | max(a, a) = a |
| 29 | Min-Max Sum | min(a,b) + max(a,b) = a + b |
| 30 | Min ≤ Both | min(a,b) ≤ a and min(a,b) ≤ b |
| 31 | Max ≥ Both | max(a,b) ≥ a and max(a,b) ≥ b |

#### Abs Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 32 | Abs Non-negative | abs(v) ≥ 0 component-wise |
| 33 | Abs Idempotent | abs(abs(v)) = abs(v) |
| 34 | Abs Zero | abs(0) = 0 |
| 35 | Abs Negation | abs(-v) = abs(v) |

#### Clamp Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 36 | Clamp Bounds | lo ≤ clamp(v, lo, hi) ≤ hi |
| 37 | Clamp Identity | clamp(v, lo, hi) = v when lo ≤ v ≤ hi |
| 38 | Clamp Idempotent | clamp(clamp(v, lo, hi), lo, hi) = clamp(v, lo, hi) |

#### Distance Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 39 | Distance Squared Non-negative | dist²(a, b) ≥ 0 |
| 40 | Distance Squared Symmetric | dist²(a, b) = dist²(b, a) |
| 41 | Distance Squared Self | dist²(a, a) = 0 |

#### Element-wise Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 42 | Element Sum Zero | element_sum(0) = 0 |
| 43 | Element Sum Additive | element_sum(a + b) = element_sum(a) + element_sum(b) |
| 44 | Element Sum Scale | element_sum(s * v) = s * element_sum(v) |
| 45 | Element Product Splat | element_product(splat(v)) = v² |
| 46 | Element Product Commutative | element_product(v) is symmetric in components |

#### Reflect Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 47 | Reflect Along Unit Normal | reflect(n, n) = -n for unit n |
| 48 | Reflect Perpendicular | reflect(v, n) = v when v ⊥ n |

#### Lerp Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 49 | Lerp Zero | lerp(a, b, 0) = a |
| 50 | Lerp One | lerp(a, b, 1) = b |
| 51 | Lerp Identity | lerp(v, v, t) = v |
| 52 | Lerp Two | lerp(a, b, 2) = 2b - a |
| 53 | Lerp Neg One | lerp(a, b, -1) = 2a - b |
| 54 | Lerp Zero Zero | lerp(0, 0, t) = 0 |
| 55 | Vector Space Structure | Combined axiom verification (extended) |

### Vec3 (55 Proof Functions, 89+ Verification Conditions)

All proofs verified with `0 errors`.

#### Algebraic Properties

| Theorem | Property |
|---------|----------|
| 1-7 | Same as Vec2 (vector space axioms) |

#### Dot Product Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 8 | Commutativity | a . b = b . a |
| 9 | Length Squared Non-negative | \|a\|^2 >= 0 |

#### Cross Product Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 10 | Anti-commutativity | a x b = -(b x a) |
| 11 | Self-cross Zero | a x a = 0 |
| 12 | Orthogonality to First | (a x b) . a = 0 |
| 13 | Orthogonality to Second | (a x b) . b = 0 |
| 14 | Right-hand Rule (X x Y) | X x Y = Z |
| 15 | Right-hand Rule (Y x Z) | Y x Z = X |
| 16 | Right-hand Rule (Z x X) | Z x X = Y |
| 17 | Anti-right-hand | Y x X = -Z |

#### Scalar Triple Product Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 19 | Expansion a.(b x c) | vec3_dot(a, vec3_cross(b, c)) expands to 6 terms |
| 20 | Expansion b.(c x a) | vec3_dot(b, vec3_cross(c, a)) expands to 6 terms |
| 21 | Expansion c.(a x b) | vec3_dot(c, vec3_cross(a, b)) expands to 6 terms |
| 22 | Expanded Forms Equal | All three expansions are algebraically identical |
| 23 | **Scalar Triple Cyclic** | **a . (b x c) = b . (c x a) = c . (a x b)** |

> **Note**: The scalar triple product cyclic property (Theorem 23) proves that the signed volume
> of the parallelepiped formed by three vectors is invariant under cyclic permutation. This
> required proof decomposition techniques to guide Z3 through the nonlinear arithmetic.

#### Vector Space Structure

| Theorem | Property |
|---------|----------|
| 24 | Vector Space Structure | Combined axiom verification |

#### Min/Max Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 25 | Min Commutativity | min(a, b) = min(b, a) |
| 26 | Max Commutativity | max(a, b) = max(b, a) |
| 27 | Min Idempotent | min(a, a) = a |
| 28 | Max Idempotent | max(a, a) = a |
| 29 | Min-Max Sum | min(a,b) + max(a,b) = a + b |
| 30 | Min ≤ Both | min(a,b) ≤ a and min(a,b) ≤ b |

#### Abs Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 31 | Abs Non-negative | abs(v) ≥ 0 component-wise |
| 32 | Abs Idempotent | abs(abs(v)) = abs(v) |
| 33 | Abs Negation | abs(-v) = abs(v) |

#### Element-wise Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 34 | Element Sum Zero | element_sum(0) = 0 |
| 35 | Element Sum Additive | element_sum(a + b) = element_sum(a) + element_sum(b) |
| 36 | Element Sum Scale | element_sum(s * v) = s * element_sum(v) |

#### Distance Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 37 | Distance Squared Non-negative | dist²(a, b) ≥ 0 |
| 38 | Distance Squared Symmetric | dist²(a, b) = dist²(b, a) |
| 39 | Distance Squared Self | dist²(a, a) = 0 |
| 40 | Vector Space Structure | Combined axiom verification (extended) |

#### Clamp Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 41 | Clamp Bounds | lo ≤ clamp(v, lo, hi) ≤ hi |
| 42 | Clamp Identity | clamp(v, lo, hi) = v when lo ≤ v ≤ hi |
| 43 | Clamp Idempotent | clamp(clamp(v, lo, hi), lo, hi) = clamp(v, lo, hi) |
| 44 | Clamp Squeeze | clamp(v, target, target) = target |

#### Reflect Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 45 | Reflect Perpendicular | reflect(v, n) = v when v ⊥ n |
| 46 | Reflect Along Unit Normal | reflect(n, n) = -n for unit n |
| 47 | Reflect Zero | reflect(0, n) = 0 |

#### Element Product Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 48 | Element Product Zero | element_product(0) = 0 |
| 49 | Element Product Splat | element_product(splat(v)) = v³ |
| 50 | Element Product Basis Zero | element_product(basis_i) = 0 |

#### Lerp Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 51 | Lerp Zero | lerp(a, b, 0) = a |
| 52 | Lerp One | lerp(a, b, 1) = b |
| 53 | Lerp Identity | lerp(v, v, t) = v |
| 54 | Lerp Two | lerp(a, b, 2) = 2b - a |
| 55 | Lerp Zero Zero | lerp(0, 0, t) = 0 |

### Vec4 (55 Proof Functions, 90+ Verification Conditions)

All proofs verified with `0 errors`.

#### Algebraic Properties

| Theorem | Property |
|---------|----------|
| 1-9 | Vector space axioms (same structure as Vec2/Vec3) |

#### Dot Product Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 10 | Commutativity | a . b = b . a |
| 11 | Linearity (First Argument) | (s * a) . b = s * (a . b) |
| 12 | Distribution | (a + b) . c = a . c + b . c |
| 13 | Length Squared Non-negative | \|a\|^2 >= 0 |

#### Basis Orthonormality Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 14 | X-Y Orthogonal | X . Y = 0 |
| 15 | All Basis Orthogonal | X, Y, Z, W mutually orthogonal |
| 16 | Basis Unit Length | \|X\|^2 = \|Y\|^2 = \|Z\|^2 = \|W\|^2 = 1 |
| 17 | Zero Vector Length | \|0\|^2 = 0 |

#### Additional Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 18 | Subtraction Equivalence | a - b = a + (-b) |
| 19 | Component Multiplication Commutativity | a * b = b * a |
| 20 | Negation as Scaling | -v = (-1) * v |
| 21 | Length Squared Zero iff Zero | \|a\|^2 = 0 <=> a = 0 |
| 22 | Vector Space Structure | Combined axiom verification |

#### Min/Max/Splat Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 23 | Splat Zero | splat(0) = zero vector |
| 24 | Min Commutativity | min(a, b) = min(b, a) |
| 25 | Max Commutativity | max(a, b) = max(b, a) |
| 26 | Min Idempotent | min(a, a) = a |
| 27 | Max Idempotent | max(a, a) = a |
| 28 | Min-Max Sum | min(a,b) + max(a,b) = a + b |
| 29 | Min ≤ Both | min(a,b) ≤ a and min(a,b) ≤ b |

#### Abs Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 30 | Abs Non-negative | abs(v) ≥ 0 component-wise |
| 31 | Abs Idempotent | abs(abs(v)) = abs(v) |
| 32 | Abs Negation | abs(-v) = abs(v) |

#### Element-wise Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 33 | Element Sum Zero | element_sum(0) = 0 |
| 34 | Element Sum Additive | element_sum(a + b) = element_sum(a) + element_sum(b) |
| 35 | Element Sum Scale | element_sum(s * v) = s * element_sum(v) |

#### Distance Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 36 | Distance Squared Non-negative | dist²(a, b) ≥ 0 |
| 37 | Distance Squared Symmetric | dist²(a, b) = dist²(b, a) |
| 38 | Distance Squared Self | dist²(a, a) = 0 |
| 39 | Vector Space Structure | Combined axiom verification (extended) |

#### Clamp Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 40 | Clamp Bounds | lo ≤ clamp(v, lo, hi) ≤ hi |
| 41 | Clamp Identity | clamp(v, lo, hi) = v when lo ≤ v ≤ hi |
| 42 | Clamp Idempotent | clamp(clamp(v, lo, hi), lo, hi) = clamp(v, lo, hi) |
| 43 | Clamp Squeeze | clamp(v, target, target) = target |

#### Element Product Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 44 | Element Product Zero | element_product(0) = 0 |
| 45 | Element Product Splat | element_product(splat(v)) = v⁴ |
| 46 | Element Product Basis Zero | element_product(basis_i) = 0 |

#### Reflect Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 47 | Reflect Perpendicular | reflect(v, n) = v when v ⊥ n |
| 48 | Reflect Along Unit Normal | reflect(n, n) = -n for unit n |

#### Additional Properties (Extended)

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 49 | Max ≥ Both | max(a,b) ≥ a and max(a,b) ≥ b |
| 50 | Abs Zero | abs(0) = 0 |

#### Lerp Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 51 | Lerp Zero | lerp(a, b, 0) = a |
| 52 | Lerp One | lerp(a, b, 1) = b |
| 53 | Lerp Identity | lerp(v, v, t) = v |
| 54 | Lerp Two | lerp(a, b, 2) = 2b - a |
| 55 | Lerp Zero Zero | lerp(0, 0, t) = 0 |

### Mat3 (22 Proof Functions, 26 Verification Conditions)

All proofs verified with `0 errors`.

#### Matrix Addition Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 1 | Commutativity | A + B = B + A |
| 2 | Associativity | (A + B) + C = A + (B + C) |
| 3 | Additive Identity | A + 0 = A |
| 4 | Additive Inverse | A + (-A) = 0 |

#### Matrix Multiplication Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 5 | Left Identity | I * A = A |
| 6 | Right Identity | A * I = A |
| 7 | Zero Left Annihilator | 0 * A = 0 |
| 8 | Zero Right Annihilator | A * 0 = 0 |
| 9 | **Associativity** | **(A * B) * C = A * (B * C)** |

> **Note**: Matrix multiplication associativity (Theorem 9) is the critical property for
> transformation pipelines. It ensures that sequences of transformations can be grouped
> arbitrarily. The proof required decomposition into helper lemmas due to the 27 nonlinear
> arithmetic constraints (9 components x 3 terms each).

#### Scalar Multiplication Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 10 | Identity | 1 * A = A |
| 11 | Zero | 0 * A = 0 |
| 12 | Distribution | s * (A + B) = s * A + s * B |
| 13 | Associativity | (s * t) * A = s * (t * A) |

#### Transpose Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 14 | Double Transpose | (A^T)^T = A |
| 15 | Distribution over Add | (A + B)^T = A^T + B^T |
| 16 | Commutes with Scalar | (s * A)^T = s * A^T |

#### Additional Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 17 | Negation as Scaling | -A = (-1) * A |
| 18 | Ring Structure | Mat3 forms a ring with identity |

### Mat3 Extended (26 Proof Functions, 45 Verification Conditions)

All proofs verified with `0 errors`.

**File**: `mat3_extended_proofs.rs` (separated from `mat3_proofs.rs` due to Z3 resource limits
when combined with the associativity proof's 200+ helper lemma calls)

#### Helper Lemmas (Arithmetic Infrastructure)

| Lemma | Property | Mathematical Statement |
|-------|----------|------------------------|
| H1 | Distribution over Subtraction | a * (b - c) = a*b - a*c |
| H2 | Left Commutativity | (a*b)*c = (b*a)*c |
| H3 | Right Commutativity | a*(b*c) = a*(c*b) |
| H4 | Associativity | (a*b)*c = a*(b*c) |

#### Determinant Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 19 | Determinant of Identity | det(I) = 1 |
| 20 | Determinant of Zero | det(0) = 0 |
| 21 | **Determinant of Transpose** | **det(A^T) = det(A)** |
| 22 | Column Swap Negation | det(swap_cols(A)) = -det(A) |
| 23 | Diagonal Determinant | det(diag(d0,d1,d2)) = d0*d1*d2 |

> **Note**: Theorem 21 (det_transpose) required the **requires-axiom decomposition technique**
> (see [Proof Techniques](#proof-techniques-for-z3-intractable-identities) below). This is a
> degree-3 polynomial identity over 9 variables that Z3's `nonlinear_arith` cannot solve
> directly. The 4-phase decomposition pattern is reusable for any similar identity.

#### Translation Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 24 | Translation Structure | T(tx,ty) has correct matrix elements |
| 25 | Translation Determinant | det(T(tx,ty)) = 1 |
| 26 | Translate Origin | T(tx,ty) * (0,0) = (tx,ty) |
| 27 | Preserves Vectors | T(tx,ty) * v = v (w=0 homogeneous) |
| 28 | Additive Composition | T(t2) * T(t1) = T(t1+t2) |

#### Scaling Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 29 | Scaling Structure | S(sx,sy) has correct matrix elements |
| 30 | Scaling Determinant | det(S(sx,sy)) = sx*sy |
| 31 | Identity Scaling | S(1,1) = I |
| 32 | Multiplicative Composition | S(s2) * S(s1) = S(s1*s2) |
| 33 | Point Transformation | S(sx,sy) * p = (sx*px, sy*py) |

#### Shearing Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 34 | Shearing Structure | H(shx,shy) has correct matrix elements |
| 35 | Shearing Determinant | det(H(shx,shy)) = 1 - shx*shy |
| 36 | Zero Shear | H(0,0) = I |

#### Transform Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 37 | Identity Point Transform | I * p = p |
| 38 | Identity Vector Transform | I * v = v |
| 39 | Translation Point Transform | T(tx,ty) * p = (px+tx, py+ty) |
| 40 | Shearing Point Transform | H(shx,shy) * p = (px+shx*py, shy*px+py) |

### Mat4 (22 Theorems, 27 Verification Conditions)

All proofs verified with `0 errors`.

#### Matrix Addition Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 1 | Commutativity | A + B = B + A |
| 2 | Associativity | (A + B) + C = A + (B + C) |
| 3 | Additive Identity | A + 0 = A |
| 4 | Additive Inverse | A + (-A) = 0 |

#### Matrix Multiplication Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 5 | Left Identity | I * A = A |
| 6 | Right Identity | A * I = A |
| 7 | Zero Left Annihilator | 0 * A = 0 |
| 8 | Zero Right Annihilator | A * 0 = 0 |
| 9 | **Associativity** | **(A * B) * C = A * (B * C)** |

> **Note**: Mat4 multiplication associativity is essential for 3D transformation pipelines
> (model-view-projection matrices). The proof handles 64 nonlinear constraints (16 components
> x 4 terms each) using distribution and associativity helper lemmas.

#### Scalar Multiplication Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 10 | Identity | 1 * A = A |
| 11 | Zero | 0 * A = 0 |
| 12 | Distribution | s * (A + B) = s * A + s * B |
| 13 | Associativity | (s * t) * A = s * (t * A) |

#### Transpose Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 14 | Double Transpose | (A^T)^T = A |
| 15 | Distribution over Add | (A + B)^T = A^T + B^T |
| 16 | Commutes with Scalar | (s * A)^T = s * A^T |

#### Additional Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 17 | Negation as Scaling | -A = (-1) * A |
| 18 | Ring Structure | Mat4 forms a ring with identity |

### Mat4 Extended (32 Theorems, 55 Verification Conditions)

All proofs verified with `0 errors`.

#### Translation Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 19 | Translation Structure | T(tx,ty,tz) has I₃ in upper-left, translation in column 3 |
| 20 | det(Translation) = 1 | det(T(tx,ty,tz)) = 1 |
| 21 | Translate Origin | T(tx,ty,tz) * origin = (tx,ty,tz) |
| 22 | Translation Preserves Vectors | T * v = v for direction vectors (w=0) |
| 23 | Translation Composition | T(t2) * T(t1) = T(t1+t2) |
| 24 | Zero Translation = Identity | T(0,0,0) = I |
| 25 | Get Translation Roundtrip | get_translation(T(tx,ty,tz)) = (tx,ty,tz) |

#### Scaling Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 26 | Scaling Structure | S(sx,sy,sz) is diagonal with (sx,sy,sz,1) |
| 27 | det(Scaling) | det(S(sx,sy,sz)) = sx·sy·sz |
| 28 | Unit Scaling = Identity | S(1,1,1) = I |
| 29 | Scaling Composition | S(s2) * S(s1) = S(s1·s2) component-wise |
| 30 | Scaling Transforms Point | S(sx,sy,sz) * p = (sx·px, sy·py, sz·pz) |
| 31 | Uniform Scaling | uniform_scale(s) = S(s,s,s) |
| 32 | det(Uniform Scaling) | det(uniform_scale(s)) = s³ |

#### Transform Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 33 | Identity Point Transform | I * p = p |
| 34 | Identity Vector Transform | I * v = v |
| 35 | Translation Point Transform | T(tx,ty,tz) * p = p + (tx,ty,tz) |
| 36 | Scaling Vector Transform | S(sx,sy,sz) * v = (sx·vx, sy·vy, sz·vz) |
| 37 | Identity Vec4 Transform | I * v4 = v4 |
| 38 | Zero Transforms to Origin | 0 * p = origin |

#### Determinant Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 39 | det(I) = 1 | det(identity) = 1 |
| 40 | det(0) = 0 | det(zero_matrix) = 0 |
| 41 | det(Diagonal) | det(diag(d0,d1,d2,d3)) = d0·d1·d2·d3 |
| 42 | det(-A) = det(A) | det(-A) = det(A) for 4×4 ((-1)⁴=1) |

#### Trace Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 43 | tr(I) = 4 | Trace of identity is 4 |
| 44 | tr(0) = 0 | Trace of zero matrix is 0 |
| 45 | Trace Additive | tr(A+B) = tr(A) + tr(B) |
| 46 | tr(Scaling) | tr(S(sx,sy,sz)) = sx + sy + sz + 1 |
| 47 | tr(Aᵀ) = tr(A) | Trace invariant under transpose |
| 48 | tr(Translation) = 4 | Translation has trace 4 |

#### Composite Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 49 | Translation Roundtrip | get_translation(T(tx,ty,tz)) = (tx,ty,tz) |
| 50 | det(T·S) = det(S) | det(T(t)·S(s)) = sx·sy·sz |

### Color (57 Proof Functions)

All proofs verified with `0 errors`.

#### Constructor Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 1 | Component Correctness | new(r,g,b,a) sets all components correctly |
| 2 | RGB Full Alpha | rgb(r,g,b).a = 1 (opaque) |
| 3 | Gray Equal RGB | gray(v).r = gray(v).g = gray(v).b = v |
| 4 | Gray Opaque | gray(v).a = 1 |

#### Alpha Operations

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 5 | with_alpha Preserves RGB | with_alpha(c, a).rgb = c.rgb |
| 6 | fade(1) Preserves | fade(c, 1).a = c.a |
| 7 | fade(0) Zeroes Alpha | fade(c, 0).a = 0 |
| 8 | fade Preserves RGB | fade(c, f).rgb = c.rgb |

#### Interpolation Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 9 | Same-Color Identity | lerp(c, c, t) = c |
| 10 | Start Boundary | lerp(a, b, 0) = a |
| 11 | End Boundary | lerp(a, b, 1) = b |

#### Blending Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 12 | Opaque FG Covers | blend(src, dst) = src when src.a = 1 |
| 13 | Transparent FG Shows BG | blend(src, dst) = dst when src.a = 0 |

#### Premultiplication Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 14 | Full Alpha Preserves RGB | premultiplied(c).rgb = c.rgb when c.a = 1 |
| 15 | Zero Alpha Zeroes RGB | premultiplied(c).rgb = 0 when c.a = 0 |
| 16 | Preserves Alpha | premultiplied(c).a = c.a |

#### Clamping Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 17 | In-Range Identity | clamp(c) = c when c in [0,1] |
| 18 | Bounds Guarantee | 0 <= clamp(c) <= 1 |
| 19 | Idempotence | clamp(clamp(c)) = clamp(c) |

#### Luminance Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 20 | Black Luminance | luminance(black) = 0 |
| 21 | Non-negative | luminance(c) >= 0 for valid c |
| 22 | Gray Proportional | luminance(gray(v)) = 10000 * v |
| 23 | White Maximum | luminance(white) = 10000000 |

#### Extended Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 24-35 | (base theorems) | See color_proofs.rs Theorems 24-35 |
| 36 | Scale Zero | scale(c, 0) = (0, 0, 0, 0) |
| 37 | Scale Full | scale(c, 1.0) = c |
| 38 | Scale Transparent | scale(transparent, s) = transparent |
| 39 | Scale Preserves Zero | scale(c, s).component = 0 if c.component = 0 |
| 40 | Gray Luminance Monotone | v1 ≤ v2 → lum(gray(v1)) ≤ lum(gray(v2)) |
| 41 | Luminance Bounded | lum(c) ≤ 10000 × max(c.r, c.g, c.b) |
| 42 | Green Dominates Luminance | Rec. 709: green coeff (7152) > red (2126) > blue (722) |
| 43 | Mix Identity | mix(c, c) = c |
| 44 | Invert Luminance | lum(c) + lum(invert(c)) = 10000000 for valid c |
| 45 | Blend Transparent FG | blend_over(transparent, dst) = dst |

#### Contrasting Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 46 | Contrasting Black | contrasting(black) = white |
| 47 | Contrasting White | contrasting(white) = black |
| 48 | Contrasting Binary | contrasting returns black or white |
| 49 | Contrasting Black High Contrast | contrasting(black) has luminance > 5000 |
| 50 | Contrasting White High Contrast | contrasting(white) has luminance < 5000 |
| 51 | Contrasting High Contrast | contrasting(c) differs from c in luminance |

#### Darken/Lighten Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 52 | Darken Zero | darken(c, 0) = c |
| 53 | Darken Full | darken(c, 1).rgb = (0, 0, 0) |
| 54 | Darken Preserves Alpha | darken(c, amount).a = c.a |
| 55 | Lighten Zero | lighten(c, 0) = c |
| 56 | Lighten Full | lighten(c, 1).rgb = (1, 1, 1) |
| 57 | Lighten Preserves Alpha | lighten(c, amount).a = c.a |

### Rect (52 Theorems)

All proofs verified with `0 errors`.

#### Containment Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 1 | Contains Top-Left | rect contains point (x, y) |
| 2 | Contains Bottom-Right | rect contains point (x+w, y+h) |
| 3 | Contains Center | rect contains its center point |
| 4 | contains_rect Reflexive | contains_rect(r, r) = true |
| 5 | contains_rect Transitive | contains(a,b) & contains(b,c) -> contains(a,c) |

#### Intersection Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 6 | Symmetry | intersects(a, b) = intersects(b, a) |
| 7 | Self-Intersection | intersects(r, r) for valid r |
| 8 | Contains Implies Intersects | contains_rect(a, b) -> intersects(a, b) |

#### Union Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 9 | Commutativity | union(a, b) = union(b, a) |
| 10 | Contains First | contains_rect(union(a,b), a) |
| 11 | Contains Second | contains_rect(union(a,b), b) |

#### Transformation Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 12 | Translate Preserves Size | translate(r).size = r.size |
| 13 | Translate Identity | translate(r, 0, 0) = r |
| 14 | Translate Composition | translate(translate(r,d1),d2) = translate(r,d1+d2) |
| 15 | Expand-Shrink Inverse | expand(shrink(r, a), a) = r |
| 16 | Shrink-Expand Inverse | shrink(expand(r, a), a) = r |

#### Area and Perimeter Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 17 | Area Non-negative | area(r) >= 0 for valid r |
| 18 | Perimeter Non-negative | perimeter(r) >= 0 for valid r |
| 19 | Square Perimeter | perimeter(square(s)) = 4s |
| 20 | Square Area | area(square(s)) = s^2 |

#### Validity Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 21 | Valid Implies Not Empty | is_valid(r) -> !is_empty(r) |
| 22 | Zero Is Empty | is_empty(rect_zero) |
| 23 | Expand Preserves Validity | is_valid(expand(r, a)) for valid r, a >= 0 |

#### Extended Properties (Theorems 24-33)

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 24-33 | (base extended theorems) | See rect_proofs.rs Theorems 24-33 |

#### Construction Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 34 | from_points Non-negative | from_points(x1,y1,x2,y2) has w,h ≥ 0 |
| 35 | from_points Symmetric | from_points(x1,y1,x2,y2) = from_points(x2,y2,x1,y1) |
| 36 | from_points Same Point | from_points(x,y,x,y) = zero-area rect at (x,y) |
| 37 | from_points Contains Corners | Result contains both corner points |

#### Normalization Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 38 | Normalize Non-negative | normalize(r) has w,h ≥ 0 |
| 39 | Normalize Idempotent | normalize(normalize(r)) = normalize(r) |
| 40 | Normalize Preserves Area | |area(normalize(r))| = |area(r)| |

#### Expand/Scale Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 41 | expand_xy Identity | expand_xy(r, 0, 0) = r |
| 42 | expand_xy Preserves Center | center(expand_xy(r, dx, dy)) = center(r) |
| 43 | expand_xy Area Increase | area(expand_xy(r, dx, dy)) ≥ area(r) for dx,dy ≥ 0 |
| 44 | scale_from_center(1) Identity | scale_from_center(r, 1) preserves w,h |
| 45 | scale_from_center(0) Zero | scale_from_center(r, 0) has zero area |
| 46 | scale_from_center Area | area(scale(r, f)) = f²·area(r) |

#### Growth Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 47 | grow_to_contain Original | grow_to_contain(r, p) ⊇ r |
| 48 | grow_to_contain Point | grow_to_contain(r, p) contains p |
| 49 | Interior Identity | grow_to_contain(r, p) = r when p ∈ r |

#### Interpolation Properties

| Theorem | Property | Mathematical Statement |
|---------|----------|------------------------|
| 50 | lerp(0) = a | lerp(a, b, 0) = a |
| 51 | lerp(1) = b | lerp(a, b, 1) = b |
| 52 | lerp Same | lerp(r, r, t) = r |

## Verification Methodology

### Modeling Approach

We model vector operations over mathematical integers (`int` in Verus). This approach:

1. **Proves algorithmic correctness** - The mathematical formulas are correct
2. **Uses exact arithmetic** - No floating-point precision issues in proofs
3. **Enables SMT solving** - Z3 handles integer arithmetic completely

The translation to IEEE 754 floating-point (`f32`) introduces precision considerations that are documented but not formally verified (floating-point verification is a separate research domain).

### Proof Techniques

1. **SMT automation** - Most linear arithmetic proofs are automatic
2. **Nonlinear arithmetic hints** - `by(nonlinear_arith)` for multiplication
3. **Structural equality** - Direct component-wise verification
4. **Lemma chaining** - Building complex proofs from simpler ones

### Example Proof Structure

```rust
/// **Theorem 5**: Scalar multiplication is associative.
///
/// For all scalars s, t and vector v: (s * t) * v = s * (t * v)
proof fn vec2_scale_associative(s: int, t: int, v: SpecVec2)
    ensures
        vec2_scale(s * t, v) == vec2_scale(s, vec2_scale(t, v)),
{
    assert((s * t) * v.x == s * (t * v.x)) by(nonlinear_arith);
    assert((s * t) * v.y == s * (t * v.y)) by(nonlinear_arith);
}
```

## Reproducibility

## Proof Techniques for Z3-Intractable Identities

### The Requires-Axiom Decomposition Pattern

**Discovery**: Session fqynP (2026-01-29)
**Impact**: Unlocks machine-checked proofs of degree-3+ polynomial identities that Z3's
`nonlinear_arith` cannot solve directly. Previously, such theorems were removed as
"Z3-intractable" — this technique eliminates that compromise entirely.

**Problem**: Z3's `by(nonlinear_arith)` operates in an **isolated context**. It does NOT
inherit facts from helper lemma calls in the outer proof body. When a degree-3 polynomial
identity involves spec function expansion (e.g., `mat3_determinant(mat3_transpose(a))`),
`nonlinear_arith` must both expand the spec functions AND verify the polynomial equality.
For 9+ variables at degree 3, this exceeds Z3's resource limits.

**Solution**: Decouple spec-function expansion (handled by outer Z3 context) from polynomial
equality verification (handled by `nonlinear_arith` with pre-expanded forms as axioms).

#### The 4-Phase Pattern

```
Phase 1: EXPAND — Use distribution lemmas to convert spec functions into
          explicit polynomial terms. Assert the expanded form.
Phase 2: EXPAND — Do the same for the other side of the equality.
Phase 3: BRIDGE — Prove pairwise commutativity/associativity equalities
          between differing triple-product terms.
Phase 4: CLOSE  — Assert final equality using by(nonlinear_arith) with
          BOTH expanded forms as requires axioms.
```

#### Concrete Example: det(A^T) = det(A)

```rust
proof fn mat3_det_transpose(a: SpecMat3)
    ensures mat3_determinant(mat3_transpose(a)) == mat3_determinant(a),
{
    let at = mat3_transpose(a);
    let da = mat3_determinant(a);
    let dat = mat3_determinant(at);

    // Phase 1: Expand det(A) using distribution lemmas
    distrib_sub(a.m0, a.m4 * a.m8, a.m5 * a.m7);
    distrib_sub(a.m3, a.m1 * a.m8, a.m2 * a.m7);
    distrib_sub(a.m6, a.m1 * a.m5, a.m2 * a.m4);
    assert(da == a.m0 * (a.m4 * a.m8) - a.m0 * (a.m5 * a.m7)
              - a.m3 * (a.m1 * a.m8) + a.m3 * (a.m2 * a.m7)
              + a.m6 * (a.m1 * a.m5) - a.m6 * (a.m2 * a.m4));

    // Phase 2: Expand det(A^T) using distribution lemmas
    distrib_sub(a.m0, a.m4 * a.m8, a.m7 * a.m5);
    distrib_sub(a.m1, a.m3 * a.m8, a.m6 * a.m5);
    distrib_sub(a.m2, a.m3 * a.m7, a.m6 * a.m4);
    assert(dat == a.m0 * (a.m4 * a.m8) - a.m0 * (a.m7 * a.m5)
               - a.m1 * (a.m3 * a.m8) + a.m1 * (a.m6 * a.m5)
               + a.m2 * (a.m3 * a.m7) - a.m2 * (a.m6 * a.m4));

    // Phase 3: Prove triple-product commutativity equalities
    assert(a.m0 * (a.m7 * a.m5) == a.m0 * (a.m5 * a.m7)) by(nonlinear_arith);
    assert(a.m1 * (a.m3 * a.m8) == a.m3 * (a.m1 * a.m8)) by(nonlinear_arith);
    assert(a.m1 * (a.m6 * a.m5) == a.m6 * (a.m1 * a.m5)) by(nonlinear_arith);
    assert(a.m2 * (a.m3 * a.m7) == a.m3 * (a.m2 * a.m7)) by(nonlinear_arith);
    assert(a.m2 * (a.m6 * a.m4) == a.m6 * (a.m2 * a.m4)) by(nonlinear_arith);

    // Phase 4: Close with requires-axiom pattern
    assert(dat == da) by(nonlinear_arith)
        requires
            da == a.m0 * (a.m4 * a.m8) - a.m0 * (a.m5 * a.m7)
                  - a.m3 * (a.m1 * a.m8) + a.m3 * (a.m2 * a.m7)
                  + a.m6 * (a.m1 * a.m5) - a.m6 * (a.m2 * a.m4),
            dat == a.m0 * (a.m4 * a.m8) - a.m0 * (a.m7 * a.m5)
                   - a.m1 * (a.m3 * a.m8) + a.m1 * (a.m6 * a.m5)
                   + a.m2 * (a.m3 * a.m7) - a.m2 * (a.m6 * a.m4);
}
```

#### Why This Works

| Step | Who Does the Work | What They Do |
|------|-------------------|--------------|
| Phase 1-2 (assert expanded form) | Outer Z3 context | Expands `open spec fn` definitions, applies distribution lemma facts, verifies expanded form matches |
| Phase 3 (commutativity) | Individual `nonlinear_arith` blocks | Each proves a single degree-2 commutativity fact (trivial for Z3) |
| Phase 4 (final equality) | `nonlinear_arith` with axioms | Receives pre-expanded polynomials as axioms; only needs to verify two 6-term polynomials are equal using built-in commutativity — no spec function expansion needed |

**Key Insight**: The `requires` clause feeds axioms directly to `nonlinear_arith`,
bypassing the need for Z3 to expand spec functions inside the isolated arithmetic context.
This reduces a 9-variable degree-3 spec-function problem to a 9-variable degree-3
raw-integer problem where all terms are already expanded.

#### Applicability

This technique applies to ANY proof where:
1. The goal involves **spec function calls** that expand to polynomials
2. The polynomial degree is **3 or higher** (degree-2 typically works directly)
3. There are **6+ variables** (fewer variables may work without decomposition)
4. Direct `by(nonlinear_arith)` **times out or fails**

Potential future applications:
- Mat4 determinant properties (degree-4, 16 variables)
- Quaternion identities (degree-4, 4 variables)
- Cross product triple product identities (degree-3, 9 variables)
- Any Cayley-Hamilton theorem proofs

### Z3 Resource Management via File Splitting

When a single Verus file contains proofs with different Z3 resource profiles
(e.g., matrix associativity requiring 200+ helper lemmas alongside nonlinear_arith
determinant proofs), Z3's resource consumption can exceed limits. The solution is
to split into separate files with duplicated spec types for independent verification.

**Pattern**: `<type>_proofs.rs` (base algebra) + `<type>_extended_proofs.rs` (additional properties)

---

## Running Verification

### Prerequisites

1. Rust 1.92.0+ toolchain
2. Verus 0.2026.01.23+ or later

### Verification Commands

```bash
# Download and install Verus
curl -L -o verus.zip "https://github.com/verus-lang/verus/releases/download/release/0.2026.01.23.1650a05/verus-0.2026.01.23.1650a05-x86-linux.zip"
unzip verus.zip
cd verus-x86-linux
rustup install 1.92.0

# Verify Vec2 proofs
./verus /path/to/rource/crates/rource-math/proofs/vec2_proofs.rs
# Expected: verification results:: 53 verified, 0 errors

# Verify Vec3 proofs
./verus /path/to/rource/crates/rource-math/proofs/vec3_proofs.rs
# Expected: verification results:: 68 verified, 0 errors

# Verify Vec4 proofs
./verus /path/to/rource/crates/rource-math/proofs/vec4_proofs.rs
# Expected: verification results:: 68 verified, 0 errors

# Verify Mat3 base proofs (requires higher rlimit for associativity)
./verus --rlimit 20000000 /path/to/rource/crates/rource-math/proofs/mat3_proofs.rs
# Expected: verification results:: 26 verified, 0 errors

# Verify Mat3 extended proofs (determinant, transform, shearing, scaling)
./verus /path/to/rource/crates/rource-math/proofs/mat3_extended_proofs.rs
# Expected: verification results:: 45 verified, 0 errors

# Verify Mat4 base proofs (requires higher rlimit for associativity)
./verus --rlimit 30000000 /path/to/rource/crates/rource-math/proofs/mat4_proofs.rs
# Expected: verification results:: 27 verified, 0 errors

# Verify Mat4 extended proofs (translation, scaling, determinant, trace)
./verus /path/to/rource/crates/rource-math/proofs/mat4_extended_proofs.rs
# Expected: verification results:: 55 verified, 0 errors

# Verify Color proofs
./verus /path/to/rource/crates/rource-math/proofs/color_proofs.rs
# Expected: verification results:: 81 verified, 0 errors

# Verify Rect proofs
./verus /path/to/rource/crates/rource-math/proofs/rect_proofs.rs
# Expected: verification results:: 70 verified, 0 errors
```

## Verus Verification Coverage

| Crate | Status | Proof Fns | VCs | Notes |
|-------|--------|-----------|-----|-------|
| rource-math/Vec2 | VERIFIED | 61 | 87++++ | Complete vector space axioms, geometric, length, min/max, abs, clamp, distance, reflect, lerp |
| rource-math/Vec3 | VERIFIED | 61 | 89++++ | Cross product, scalar triple product, reflect, clamp, distance, element product, lerp |
| rource-math/Vec4 | VERIFIED | 55 | 90+ | 4D vector space, basis orthonormality, min/max, abs, clamp, reflect, element product, lerp |
| rource-math/Mat3 (base) | VERIFIED | 22 | 26 | Matrix multiplication associativity, ring structure |
| rource-math/Mat3 (extended) | VERIFIED | 26 | 45 | Determinant, translation, scaling, shearing, transforms |
| rource-math/Mat4 (base) | VERIFIED | 22 | 27 | 3D transformation pipelines, ring structure |
| rource-math/Mat4 (extended) | VERIFIED | 32 | 55 | Translation, scaling, determinant, trace, composite |
| rource-math/Color | VERIFIED | 64 | 81+ | Constructor, alpha, lerp, blend, clamp, luminance, scale, mix, invert, contrasting, darken, lighten |
| rource-math/Rect | VERIFIED | 52 | 70 | Containment, intersection, union, transforms, area, from_points, normalize, grow, lerp |
| rource-math/Bounds | VERIFIED | 70 | — | Bounds struct: area, containment, union, intersection, expand, shrink, translate, include_point |
| rource-math/Utils | VERIFIED | 33 | — | Scalar lerp, clamp, approx_eq properties |

**Total: 498 proof functions verified (Verus)**

---

*Last verified: 2026-01-31*
*Version: 0.2026.01.30*
*Total proof functions: 498 (Vec2: 61, Vec3: 61, Vec4: 55, Mat3: 48 [22+26], Mat4: 54 [22+32], Color: 64, Rect: 52, Bounds: 70, Utils: 33)*
*Total verification conditions: 558+ (Vec2: 87+, Vec3: 89+, Vec4: 90+, Mat3: 71 [26+45], Mat4: 82 [27+55], Color: 81+, Rect: 70, Bounds: TBD, Utils: TBD)*
*Status: All proofs verified with 0 errors across 11 files*
