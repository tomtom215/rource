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

### Vec2 (23 Theorems, 53 Verification Conditions)

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

### Vec3 (24 Theorems, 68 Verification Conditions)

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

### Vec4 (22 Theorems, 68 Verification Conditions)

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

### Mat3 (18 Theorems, 26 Verification Conditions)

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

### Mat4 (18 Theorems, 27 Verification Conditions)

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

### Color (23 Theorems)

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

### Rect (23 Theorems)

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

### Prerequisites

1. Rust 1.92.0 toolchain
2. Verus 0.2026.01.23.1650a05 or later

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

# Verify Mat3 proofs (requires higher rlimit for associativity)
./verus --rlimit 20000000 /path/to/rource/crates/rource-math/proofs/mat3_proofs.rs
# Expected: verification results:: 26 verified, 0 errors

# Verify Mat4 proofs (requires higher rlimit for associativity)
./verus --rlimit 30000000 /path/to/rource/crates/rource-math/proofs/mat4_proofs.rs
# Expected: verification results:: 27 verified, 0 errors

# Verify Color proofs
./verus /path/to/rource/crates/rource-math/proofs/color_proofs.rs
# Expected: verification results:: verified, 0 errors

# Verify Rect proofs
./verus /path/to/rource/crates/rource-math/proofs/rect_proofs.rs
# Expected: verification results:: verified, 0 errors
```

## Verus Verification Coverage

| Crate | Status | Theorems | VCs | Notes |
|-------|--------|----------|-----|-------|
| rource-math/Vec2 | VERIFIED | 23 | 53 | Complete vector space axioms |
| rource-math/Vec3 | VERIFIED | 24 | 68 | Cross product + scalar triple product |
| rource-math/Vec4 | VERIFIED | 22 | 68 | 4D vector space, basis orthonormality |
| rource-math/Mat3 | VERIFIED | 18 | 26 | Matrix multiplication associativity, ring structure |
| rource-math/Mat4 | VERIFIED | 18 | 27 | 3D transformation pipelines, ring structure |
| rource-math/Color | VERIFIED | 35 | — | Constructor, alpha, interpolation, blending, clamping, luminance, inversion, mixing |
| rource-math/Rect | VERIFIED | 33 | — | Containment, intersection, union, transformations, area/perimeter, validity, scaling |

**Total: 240 proof functions verified (Verus)**

---

*Last verified: 2026-01-29*
*Version: 0.2026.01.23.1650a05*
*Total proof functions: 240 (Vec2: 49, Vec3: 40, Vec4: 39, Mat3: 22, Mat4: 22, Color: 35, Rect: 33)*
*Total verification conditions: 360+ (Vec2: 53+, Vec3: 68+, Vec4: 68+, Mat3: 26, Mat4: 27, Color: —, Rect: —)*
*Status: All proofs verified with 0 errors*
