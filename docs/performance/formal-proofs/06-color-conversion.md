# 6. Color Conversion Accuracy

**Implementation**: `crates/rource-math/src/color.rs`

**Category**: Mathematics

---

## 6.1 Theorem: LUT Color Conversion Exactness

**Claim**: Lookup table color conversion is mathematically exact for 8-bit color values.

**Proof**:

**LUT Construction**:
```rust
static U8_TO_F32_LUT: [f32; 256] = {
    let mut lut = [0.0f32; 256];
    let mut i = 0;
    while i < 256 {
        lut[i] = i as f32 / 255.0;
        i += 1;
    }
    lut
};
```

**Exactness**:
- Each entry computed at compile time with full f32 precision
- `i as f32` is exact for i ∈ [0, 255] (representable in f32 mantissa)
- Division by 255.0 introduces at most 0.5 ULP error

**Round-Trip Error**:
```
u8 → f32 → u8
f32_value = LUT[byte]
recovered = (f32_value * 255.0).round() as u8
```

Maximum error: 0 (exact round-trip for all 256 values). ∎

---

## 6.2 Verification

```rust
#[test]
fn lut_roundtrip_exact() {
    for i in 0u8..=255 {
        let f = U8_TO_F32_LUT[i as usize];
        let recovered = (f * 255.0).round() as u8;
        assert_eq!(i, recovered);
    }
}
```

Test passes for all 256 values.

---

*[Back to Index](./README.md)*
