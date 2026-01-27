# 14. Catmull-Rom Spline Interpolation

**Implementation**: `crates/rource-core/src/animation/spline.rs`

**Category**: Animation / Curve Interpolation

---

## 14.1 Mathematical Foundation

**Definition 14.1 (Catmull-Rom Spline)**: A Catmull-Rom spline is a cubic interpolating spline that passes through all control points with C1 continuity (continuous first derivative).

Given four control points P₀, P₁, P₂, P₃, the curve segment between P₁ and P₂ is defined by:

```
C(t) = P₀·a₀(t) + P₁·a₁(t) + P₂·a₂(t) + P₃·a₃(t)
```

where t ∈ [0, 1] and the basis functions with tension parameter τ are:

```
a₀(t) = -τt³ + 2τt² - τt
a₁(t) = (2-τ)t³ + (τ-3)t² + 1
a₂(t) = (τ-2)t³ + (3-2τ)t² + τt
a₃(t) = τt³ - τt²
```

**Standard Tension**: τ = 0.5 gives the "canonical" Catmull-Rom spline.

---

## 14.2 Theorem: Interpolation Property

**Claim**: The Catmull-Rom spline passes exactly through control points P₁ and P₂.

**Proof**:

**At t = 0** (start of segment):
```
a₀(0) = 0
a₁(0) = 1
a₂(0) = 0
a₃(0) = 0

C(0) = P₀·0 + P₁·1 + P₂·0 + P₃·0 = P₁ ✓
```

**At t = 1** (end of segment):
```
a₀(1) = -τ + 2τ - τ = 0
a₁(1) = (2-τ) + (τ-3) + 1 = 0
a₂(1) = (τ-2) + (3-2τ) + τ = 1
a₃(1) = τ - τ = 0

C(1) = P₀·0 + P₁·0 + P₂·1 + P₃·0 = P₂ ✓
```

The spline passes exactly through P₁ at t=0 and P₂ at t=1. ∎

---

## 14.3 Theorem: C1 Continuity

**Claim**: Catmull-Rom splines have continuous first derivatives at control points.

**Proof**:

The derivative of C(t) is:
```
C'(t) = P₀·a₀'(t) + P₁·a₁'(t) + P₂·a₂'(t) + P₃·a₃'(t)
```

where:
```
a₀'(t) = -3τt² + 4τt - τ
a₁'(t) = 3(2-τ)t² + 2(τ-3)t
a₂'(t) = 3(τ-2)t² + 2(3-2τ)t + τ
a₃'(t) = 3τt² - 2τt
```

**Tangent at P₁** (t = 0):
```
a₀'(0) = -τ
a₁'(0) = 0
a₂'(0) = τ
a₃'(0) = 0

C'(0) = -τP₀ + τP₂ = τ(P₂ - P₀)
```

**Tangent at P₂** (t = 1):
```
a₀'(1) = -3τ + 4τ - τ = 0
a₁'(1) = 3(2-τ) + 2(τ-3) = 0
a₂'(1) = 3(τ-2) + 2(3-2τ) + τ = -τ
a₃'(1) = 3τ - 2τ = τ

C'(1) = -τP₂ + τP₃ = τ(P₃ - P₁)
```

For adjacent segments sharing point P₂:
- Segment [P₁, P₂]: tangent at P₂ is τ(P₃ - P₁)
- Segment [P₂, P₃]: tangent at P₂ is τ(P₃ - P₁)

The tangents match exactly, ensuring C1 continuity. ∎

---

## 14.4 Theorem: Tension Parameter Effect

**Claim**: The tension parameter τ controls curve "tightness" without affecting interpolation points.

**Proof**:

From Section 14.2, the interpolation property holds for any τ (the proof used symbolic τ).

The tangent magnitude at each point is proportional to τ:
```
|C'(0)| = τ|P₂ - P₀|
|C'(1)| = τ|P₃ - P₁|
```

**Effect of τ**:
- τ → 0: Tangents vanish, curve becomes piecewise linear
- τ = 0.5: Standard Catmull-Rom (balanced smoothness)
- τ → 1: Larger tangents, more overshoot possible

Implementation clamps τ ∈ [0, 1] to prevent numerical instability. ∎

---

## 14.5 Phantom Endpoint Generation

**Claim**: For endpoint segments, reflecting the adjacent point preserves curve continuity.

**Implementation**:
```rust
// First segment: need phantom P₀
let p0 = p1 + (p1 - p2);  // Reflect P₂ around P₁

// Last segment: need phantom P₃
let p3 = p2 + (p2 - p1);  // Reflect P₁ around P₂
```

**Proof of Continuity**:

At the first point (P₁) with phantom P₀ = 2P₁ - P₂:
```
C'(0) = τ(P₂ - P₀) = τ(P₂ - 2P₁ + P₂) = τ·2(P₂ - P₁)
```

This gives a tangent pointing toward P₂, which is the natural direction for the curve start. The tangent magnitude is 2τ times the distance to the next point, providing smooth entry/exit at endpoints. ∎

---

## 14.6 Computational Complexity

**Theorem 14.1**: Evaluating a Catmull-Rom spline at parameter t requires O(1) operations.

**Proof**:

The evaluation requires:
1. Compute t², t³: 2 multiplications
2. Compute basis functions a₀, a₁, a₂, a₃: 4 × O(1) = O(1) operations
3. Weighted sum: 4 vector multiplications, 3 vector additions

**Total**: O(1) operations per evaluation, independent of number of control points.

**Tessellation Complexity**:

For n control points with s segments per span:
- Number of spans: n - 1
- Total evaluations: (n - 1) × s + 1
- Complexity: O(n × s)

---

## 14.7 Numerical Precision Analysis

**Claim**: Fixed-point representation maintains sub-pixel accuracy for typical use cases.

**Analysis**:

For screen coordinates in range [-10000, 10000]:
- Using f32 (24-bit mantissa): ~10⁻³ pixel precision at extremes
- Sub-pixel error: < 0.001 pixels

For animation parameters t ∈ [0, 1]:
- f32 provides ~10⁷ distinguishable t values
- Frame-to-frame smoothness: guaranteed for any practical frame rate

---

## 14.8 Implementation

```rust
pub fn catmull_rom(p0: Vec2, p1: Vec2, p2: Vec2, p3: Vec2, t: f32, tension: f32) -> Vec2 {
    let t2 = t * t;
    let t3 = t2 * t;
    let s = tension;

    let a0 = -s * t3 + 2.0 * s * t2 - s * t;
    let a1 = (2.0 - s) * t3 + (s - 3.0) * t2 + 1.0;
    let a2 = (s - 2.0) * t3 + (3.0 - 2.0 * s) * t2 + s * t;
    let a3 = s * t3 - s * t2;

    p0 * a0 + p1 * a1 + p2 * a2 + p3 * a3
}
```

---

## References

- Catmull, E., & Rom, R. (1974). "A class of local interpolating splines." *Computer Aided Geometric Design*, Academic Press, 317-326.
- Bartels, R. H., Beatty, J. C., & Barsky, B. A. (1987). "An Introduction to Splines for Use in Computer Graphics and Geometric Modeling." Morgan Kaufmann.

---

## 14.9 Implementation (Papers With Code)

### Source Code Location

| Component | File | Lines |
|-----------|------|-------|
| catmull_rom function | `crates/rource-core/src/animation/spline.rs` | 462-477 |
| catmull_rom_tangent | `crates/rource-core/src/animation/spline.rs` | 481-492 |
| catmull_rom_spline | `crates/rource-render/src/visual.rs` | 113-145 |
| catmull_rom_interpolate | `crates/rource-render/src/visual.rs` | 169-180 |
| GPU shader | `crates/rource-render/src/backend/wgpu/shaders.rs` | 1269-1290 |

### Core Implementation

**Catmull-Rom with Tension** (`spline.rs:462-477`):

```rust
#[must_use]
pub fn catmull_rom(p0: Vec2, p1: Vec2, p2: Vec2, p3: Vec2, t: f32, tension: f32) -> Vec2 {
    let t2 = t * t;
    let t3 = t2 * t;

    // Catmull-Rom basis matrix with tension
    let s = tension;
    let a0 = -s * t3 + 2.0 * s * t2 - s * t;
    let a1 = (2.0 - s) * t3 + (s - 3.0) * t2 + 1.0;
    let a2 = (s - 2.0) * t3 + (3.0 - 2.0 * s) * t2 + s * t;
    let a3 = s * t3 - s * t2;

    p0 * a0 + p1 * a1 + p2 * a2 + p3 * a3
}
```

### Mathematical-Code Correspondence

| Theorem | Mathematical Expression | Code Location | Implementation |
|---------|------------------------|---------------|----------------|
| 14.2 | a₁(0) = 1 | `spline.rs:470` | `+ 1.0` term |
| 14.3 | C'(t) = τ(P₂-P₀) | `spline.rs:481-492` | Derivative calculation |
| 14.1 | O(1) evaluation | Function | Fixed number of operations |

### Verification Commands

```bash
# Run Catmull-Rom tests
cargo test -p rource-core catmull_rom --release -- --nocapture

# Run spline interpolation tests
cargo test -p rource-render catmull --release -- --nocapture

# Test endpoint behavior
cargo test -p rource-core test_spline_endpoints --release -- --nocapture
```

### Validation Checklist

- [x] Interpolation property: C(0) = P₁, C(1) = P₂
- [x] C1 continuity at control points
- [x] Configurable tension parameter
- [x] Phantom endpoint generation for boundaries
- [x] O(1) evaluation per point

---

*[Back to Index](./README.md)*
