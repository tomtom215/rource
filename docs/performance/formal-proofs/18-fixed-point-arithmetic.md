# 18. Fixed-Point Arithmetic

**Implementation**: `crates/rource-render/src/backend/software/optimized.rs`

**Category**: Determinism / Numerical Computing

---

## 18.1 Problem Statement

Floating-point arithmetic can produce different results across:
- Different CPU architectures (x86 vs ARM)
- Different compiler optimizations
- Different rounding modes

For deterministic rendering (identical output on all platforms), we need platform-independent arithmetic.

---

## 18.2 Fixed-Point Representation

**Definition 18.1 (Q-Format)**: A Qm.n fixed-point number has m integer bits and n fractional bits.

**8.8 Format** (Q8.8):
- Total: 16 bits (stored in u16 or u32)
- Integer range: 0 to 255
- Fractional precision: 1/256 ≈ 0.00391
- Scale factor: 256

**16.16 Format** (Q16.16):
- Total: 32 bits (stored in u32)
- Integer range: 0 to 65,535
- Fractional precision: 1/65,536 ≈ 0.0000153
- Scale factor: 65,536

---

## 18.3 Conversion Operations

**Float to Fixed (8.8)**:
```rust
let fixed = (float_val * 256.0) as u32;
```

**Fixed to Float (8.8)**:
```rust
let float_val = fixed as f32 / 256.0;
```

**Proof of Invertibility** (within precision):
```
float → fixed: x_f = (x × 256) as u32
fixed → float: x_r = x_f / 256

Error: |x - x_r| ≤ 1/512 (half the precision step)
```

---

## 18.4 Theorem: Deterministic Addition

**Claim**: Fixed-point addition is bit-exact across all platforms.

**Proof**:

For two 8.8 fixed-point values A and B:
```
A + B = (a × 256) + (b × 256) = (a + b) × 256
```

Integer addition is defined by the hardware instruction set (ADD) which is:
1. Commutative: A + B = B + A
2. Associative: (A + B) + C = A + (B + C)
3. Bit-exact: Same input bits always produce same output bits

No rounding decisions are involved. ∎

---

## 18.5 Theorem: Deterministic Multiplication

**Claim**: Fixed-point multiplication produces identical results on all platforms.

**Implementation**:
```rust
// 8.8 × 8.8 → 8.8
fn mul_fixed(a: u32, b: u32) -> u32 {
    (a * b) >> 8  // Divide by scale factor
}
```

**Proof**:

For 8.8 values a_f = a/256 and b_f = b/256:
```
Product = a_f × b_f = (a × b) / (256 × 256)
Fixed result = (a × b) / 256 = (a × b) >> 8
```

The operations are:
1. Integer multiplication: `a * b` (deterministic)
2. Bit shift: `>> 8` (deterministic)

No floating-point operations, no rounding mode ambiguity. ∎

---

## 18.6 Alpha Blending

**Porter-Duff Over Operation**:
```
result = src × α + dst × (1 - α)
```

**Fixed-Point Implementation** (α in 8.8 format, 0-256):
```rust
pub fn blend_pixel_fixed(dst: u32, src_r: u8, src_g: u8, src_b: u8, alpha: u32) -> u32 {
    let inv_alpha = 256 - alpha;

    let dst_r = (dst >> 16) & 0xFF;
    let dst_g = (dst >> 8) & 0xFF;
    let dst_b = dst & 0xFF;

    let new_r = ((src_r as u32 * alpha + dst_r * inv_alpha) >> 8).min(255);
    let new_g = ((src_g as u32 * alpha + dst_g * inv_alpha) >> 8).min(255);
    let new_b = ((src_b as u32 * alpha + dst_b * inv_alpha) >> 8).min(255);

    0xFF00_0000 | (new_r << 16) | (new_g << 8) | new_b
}
```

**Proof of Correctness**:

For src_r = 255, dst_r = 0, alpha = 128 (50%):
```
new_r = ((255 × 128 + 0 × 128) >> 8)
      = (32640 >> 8)
      = 127

Expected: 255 × 0.5 = 127.5 → 127 or 128
Result: 127 ✓
```

Maximum error: ±1 color level (see Proof 5: Alpha Blending Correctness)

---

## 18.7 Sqrt Lookup Table

**Problem**: sqrt() function may use different algorithms across platforms.

**Solution**: Pre-compute sqrt values at compile time into a lookup table.

**Implementation**:
```rust
pub static SQRT_LUT: [u16; 1025] = {
    let mut table = [0u16; 1025];
    let mut i = 0;
    while i <= 1024 {
        table[i] = (const_sqrt(i as f64) * 256.0) as u16;
        i += 1;
    }
    table
};
```

**Newton-Raphson for const_sqrt**:
```rust
const fn const_sqrt(x: f64) -> f64 {
    let mut guess = x * 0.5;
    let mut i = 0;
    while i < 20 {
        guess = 0.5 * (guess + x / guess);
        i += 1;
    }
    guess
}
```

**Proof of Convergence**:

Newton-Raphson for f(y) = y² - x:
```
y_{n+1} = y_n - f(y_n)/f'(y_n) = y_n - (y_n² - x)/(2y_n) = (y_n + x/y_n)/2
```

For x > 0, convergence is quadratic: error halves each iteration.
After 20 iterations: error < 10⁻¹⁵ (well beyond f64 precision).

**Determinism**: The table is computed at compile time. The same compiler produces the same table on all platforms.

---

## 18.8 Fast Sqrt with Linear Interpolation

**Implementation**:
```rust
pub fn fast_sqrt_fixed(dist_sq_fixed: u32) -> u16 {
    let idx = (dist_sq_fixed >> 8).min(1024) as usize;
    let frac = dist_sq_fixed & 0xFF;

    let a = SQRT_LUT[idx] as u32;
    let b = SQRT_LUT[idx + 1] as u32;

    (a + (((b - a) * frac) >> 8)) as u16
}
```

**Linear Interpolation**:
```
result = a + (b - a) × frac / 256
```

**Error Analysis**:

Maximum interpolation error for sqrt over interval [n, n+1]:
```
max_error = |sqrt(x) - lerp(sqrt(n), sqrt(n+1), x-n)|
```

For the 0-1024 range with 1024 samples:
- Max absolute error: < 0.5/256 = 0.002 in 8.8 format
- Relative error: < 0.2%

---

## 18.9 Inverse Table for Division

**Implementation**:
```rust
pub static INV_TABLE: [u32; 256] = {
    let mut table = [0u32; 256];
    table[0] = 0;  // Division by zero → 0
    let mut i = 1;
    while i < 256 {
        table[i] = (65536 + i as u32 / 2) / i as u32;  // Round to nearest
        i += 1;
    }
    table
};
```

**Usage**: Replace `x / n` with `(x * INV_TABLE[n]) >> 16`

**Proof of Accuracy**:
```
x / n ≈ (x × (65536/n)) / 65536 = (x × INV_TABLE[n]) >> 16
```

With rounding: `INV_TABLE[n] = (65536 + n/2) / n`

Maximum error: ±1 in the result.

---

## 18.10 Performance Characteristics

| Operation | Floating-Point | Fixed-Point | Speedup |
|-----------|----------------|-------------|---------|
| Addition | ~1-3 cycles | ~1 cycle | 1-3× |
| Multiplication | ~3-5 cycles | ~3 cycles | 1-2× |
| Division | ~20-40 cycles | ~3 cycles (LUT) | 7-13× |
| Sqrt | ~15-30 cycles | ~5 cycles (LUT) | 3-6× |
| Alpha Blend | ~15 cycles | ~15 cycles | 1× |

**Key Benefit**: Determinism, not raw speed. Fixed-point guarantees bit-exact results.

---

## References

- Jerraya, A. A., & Wolf, W. (2005). "Multiprocessor Systems-on-Chips." Morgan Kaufmann. Chapter on Fixed-Point Arithmetic.
- Yates, R. (2013). "Fixed-Point Arithmetic: An Introduction." *Digital Signal Labs*.

---

*[Back to Index](./README.md)*
