# 19. Easing Functions

**Implementation**: `crates/rource-core/src/animation/tween.rs`

**Category**: Animation Mathematics

---

## 19.1 Mathematical Foundation

**Definition 19.1 (Easing Function)**: A function e: [0,1] → ℝ that maps linear progress t to curved progress, satisfying:
- e(0) = 0 (starts at beginning)
- e(1) = 1 (ends at end)

**Interpolation Formula**:
```
value(t) = start + (end - start) × e(t)
```

---

## 19.2 Polynomial Easing Functions

### Quadratic (n = 2)

| Type | Formula | Derivative at t=0 | Derivative at t=1 |
|------|---------|-------------------|-------------------|
| QuadIn | t² | 0 | 2 |
| QuadOut | 1-(1-t)² | 2 | 0 |
| QuadInOut | piecewise | 0 | 0 |

**QuadInOut**:
```
e(t) = { 2t²           if t < 0.5
       { 1 - (-2t+2)²/2  if t ≥ 0.5
```

**Proof of C0 Continuity at t = 0.5**:
```
Left:  lim(t→0.5⁻) 2t² = 2(0.25) = 0.5
Right: lim(t→0.5⁺) 1 - (-2×0.5+2)²/2 = 1 - 1²/2 = 0.5 ✓
```

### Cubic (n = 3)

| Type | Formula |
|------|---------|
| CubicIn | t³ |
| CubicOut | 1-(1-t)³ |
| CubicInOut | piecewise cubic |

### General Polynomial

**Theorem 19.1**: For polynomial ease-in of degree n:
```
e_in(t) = tⁿ
e_out(t) = 1 - (1-t)ⁿ
```

**Proof of Boundary Conditions**:
```
e_in(0) = 0ⁿ = 0 ✓
e_in(1) = 1ⁿ = 1 ✓
e_out(0) = 1 - 1ⁿ = 0 ✓
e_out(1) = 1 - 0ⁿ = 1 ✓
```

---

## 19.3 Trigonometric Easing

### Sinusoidal

| Type | Formula |
|------|---------|
| SineIn | 1 - cos(t × π/2) |
| SineOut | sin(t × π/2) |
| SineInOut | (1 - cos(t × π))/2 |

**Proof of SineInOut Smoothness**:

The function is infinitely differentiable (C∞) because cos is C∞.

At boundaries:
```
e(0) = (1 - cos(0))/2 = 0 ✓
e(1) = (1 - cos(π))/2 = (1-(-1))/2 = 1 ✓
e'(0) = (π × sin(0))/2 = 0 ✓ (starts slow)
e'(1) = (π × sin(π))/2 = 0 ✓ (ends slow)
```

---

## 19.4 Exponential Easing

| Type | Formula |
|------|---------|
| ExpoIn | 2^(10(t-1)) for t>0, else 0 |
| ExpoOut | 1 - 2^(-10t) for t<1, else 1 |
| ExpoInOut | piecewise exponential |

**Implementation Optimization**:
```rust
// Use exp2() instead of powf() - single CPU instruction
Easing::ExpoIn => {
    if t == 0.0 { 0.0 }
    else { TWO_POW_NEG_10 * f32::exp2(10.0 * t) }
}
```

Where `TWO_POW_NEG_10 = 2^(-10) = 0.0009765625`

**Performance**: `exp2(x)` is ~3 cycles vs `powf(2.0, x)` ~40-50 cycles.

---

## 19.5 Elastic Easing

**Definition**: Elastic easing simulates spring-like overshoot oscillation.

**Formula** (ElasticOut):
```
e(t) = 2^(-10t) × sin((t × 10 - 0.75) × 2π/3) + 1
```

**Properties**:
- Overshoots target (e(t) > 1 for some t)
- Settles to 1 as t → 1
- Period: 2π/C4 = 3/2 oscillations

**Amplitude Decay**:
```
amplitude(t) = 2^(-10t)
```

At t = 0.3: amplitude = 2^(-3) = 0.125 (12.5% overshoot)
At t = 0.5: amplitude = 2^(-5) = 0.031 (3.1% overshoot)

---

## 19.6 Back Easing

**Definition**: Back easing creates anticipation by slightly overshooting the start.

**Constants**:
```rust
const BACK_C1: f32 = 1.70158;      // Overshoot amount
const BACK_C3: f32 = BACK_C1 + 1.0; // = 2.70158
```

**BackIn Formula**:
```
e(t) = C3 × t³ - C1 × t²
```

**Proof of Overshoot** (BackIn goes negative):
```
e'(t) = 3C3t² - 2C1t = t(3C3t - 2C1)
e'(t) = 0 at t = 2C1/(3C3) ≈ 0.42

e(0.42) = 2.70158 × 0.074 - 1.70158 × 0.176
        ≈ 0.200 - 0.299 = -0.099
```

The minimum is at t ≈ 0.42 with value ≈ -0.099 (9.9% undershoot).

---

## 19.7 Bounce Easing

**Definition**: Simulates bouncing ball physics with decreasing bounce heights.

**BounceOut Implementation**:
```rust
fn bounce_out(t: f32) -> f32 {
    const N1: f32 = 7.5625;
    const D1: f32 = 2.75;

    if t < 1.0/D1 {
        N1 * t * t
    } else if t < 2.0/D1 {
        let t = t - 1.5/D1;
        N1 * t * t + 0.75
    } else if t < 2.5/D1 {
        let t = t - 2.25/D1;
        N1 * t * t + 0.9375
    } else {
        let t = t - 2.625/D1;
        N1 * t * t + 0.984375
    }
}
```

**Bounce Heights**:
| Bounce | Peak Time | Peak Height |
|--------|-----------|-------------|
| 1 | 1/2.75 ≈ 0.36 | 1.0 (full) |
| 2 | 1.5/2.75 ≈ 0.55 | 0.75 |
| 3 | 2.25/2.75 ≈ 0.82 | 0.9375 |
| 4 | 2.625/2.75 ≈ 0.95 | 0.984375 |

---

## 19.8 Theorem: Easing Function Invertibility

**Claim**: Monotonic easing functions (Quad, Cubic, Sine, Expo, Circ) are invertible.

**Proof**:

For QuadIn: e(t) = t² on [0,1]
- Strictly increasing: e'(t) = 2t > 0 for t ∈ (0,1]
- One-to-one: each output has unique input
- Inverse: t = √(e)

For non-monotonic functions (Elastic, Back, Bounce):
- Not globally invertible
- Multiple t values can map to same output
- Used for visual effect, not invertibility

---

## 19.9 Performance Optimization

**Direct Multiplication vs powi()**:

```rust
// Slow: uses function call
t.powi(4)

// Fast: direct multiplication (~2-3× faster)
let t2 = t * t;
t2 * t2
```

**Precomputed Constants**:
```rust
const TWO_POW_NEG_10: f32 = 0.0009765625;  // 2^(-10)
const TWO_POW_NEG_11: f32 = 0.00048828125; // 2^(-11)
const TWO_POW_10: f32 = 1024.0;            // 2^10
```

**Reciprocal Duration**:
```rust
// Precompute for Tween
let inv_duration = 1.0 / duration;

// Fast progress calculation (multiply vs divide)
let progress = elapsed * inv_duration;  // ~3 cycles
// vs
let progress = elapsed / duration;       // ~20 cycles
```

---

## 19.10 Complete Easing Function Catalog

| Category | Types | Use Case |
|----------|-------|----------|
| Polynomial | Quad, Cubic, Quart, Quint | General UI, smooth transitions |
| Trigonometric | Sine | Natural, gentle motion |
| Exponential | Expo | Dramatic acceleration/deceleration |
| Circular | Circ | Smooth arcs |
| Elastic | ElasticIn/Out | Springy, playful motion |
| Back | BackIn/Out | Anticipation, emphasis |
| Bounce | BounceIn/Out | Physical, game-like feedback |

**Total**: 30 easing functions (10 types × 3 variants each)

---

## References

- Penner, R. (2001). "Robert Penner's Easing Functions." *Flash MX Programming*.
- CSS Working Group. (2023). "CSS Easing Functions Level 2." W3C.

---

*[Back to Index](./README.md)*
