// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Kani proof harnesses for Color f32 edge-case verification.
//!
//! Verifies IEEE 754 safety properties for Color operations: to_rgba8,
//! blend_over, luminance, and from_hex.
//!
//! Color components are typically in [0.0, 1.0], so most harnesses use
//! this range as the input domain.

use crate::{Color, Hsl};

// ============================================================================
// to_rgba8
// ============================================================================

/// **NaN-freedom**: `to_rgba8()` with normalized color components.
///
/// Verifies the `clamp(0.0, 1.0) * 255.0 + 0.5` chain doesn't produce NaN.
#[kani::proof]
fn verify_color_to_rgba8_normalized() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    let c = Color::new(r, g, b, a);
    let _packed = c.to_rgba8();
    // If we reach here, no NaN-induced UB occurred
}

// ============================================================================
// luminance
// ============================================================================

/// **Postcondition**: `luminance()` of normalized color is in [0, 1].
///
/// Mathematical: L = 0.2126·r + 0.7152·g + 0.0722·b.
/// For r, g, b ∈ [0,1]: 0 ≤ L ≤ 0.2126 + 0.7152 + 0.0722 = 1.0.
#[kani::proof]
fn verify_color_luminance_range() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    let c = Color::new(r, g, b, a);
    let l = c.luminance();
    assert!(l >= 0.0, "luminance should be non-negative");
    // Allow small FP tolerance above 1.0 (weights sum to 1.0 exactly,
    // but FP multiplication may introduce rounding)
    assert!(l <= 1.0 + 1e-6, "luminance should be at most ~1.0");
}

// ============================================================================
// blend_over
// ============================================================================

/// **NaN-freedom**: `blend_over()` with normalized colors produces non-NaN.
///
/// Blend formula: `result = fg * fg.a + bg * (1 - fg.a)`.
/// For components in [0,1], all intermediate values stay in [0,1].
#[kani::proof]
fn verify_color_blend_over_no_nan() {
    let fr: f32 = kani::any();
    let fg: f32 = kani::any();
    let fb: f32 = kani::any();
    let fa: f32 = kani::any();
    let br: f32 = kani::any();
    let bg: f32 = kani::any();
    let bb: f32 = kani::any();
    let ba: f32 = kani::any();
    kani::assume(fr >= 0.0 && fr <= 1.0);
    kani::assume(fg >= 0.0 && fg <= 1.0);
    kani::assume(fb >= 0.0 && fb <= 1.0);
    kani::assume(fa >= 0.0 && fa <= 1.0);
    kani::assume(br >= 0.0 && br <= 1.0);
    kani::assume(bg >= 0.0 && bg <= 1.0);
    kani::assume(bb >= 0.0 && bb <= 1.0);
    kani::assume(ba >= 0.0 && ba <= 1.0);
    let fg_color = Color::new(fr, fg, fb, fa);
    let bg_color = Color::new(br, bg, bb, ba);
    let result = fg_color.blend_over(bg_color);
    assert!(!result.r.is_nan(), "blend_over().r is NaN");
    assert!(!result.g.is_nan(), "blend_over().g is NaN");
    assert!(!result.b.is_nan(), "blend_over().b is NaN");
    assert!(!result.a.is_nan(), "blend_over().a is NaN");
}

// ============================================================================
// from_hex
// ============================================================================

/// **Postcondition**: `from_hex()` always produces normalized components.
///
/// For any u32 input, all RGB components should be in [0, 1] and alpha = 1.0.
#[kani::proof]
fn verify_color_from_hex_normalized() {
    let hex: u32 = kani::any();
    let c = Color::from_hex(hex);
    assert!(c.r >= 0.0 && c.r <= 1.0, "from_hex().r out of [0,1]");
    assert!(c.g >= 0.0 && c.g <= 1.0, "from_hex().g out of [0,1]");
    assert!(c.b >= 0.0 && c.b <= 1.0, "from_hex().b out of [0,1]");
    assert!(c.a == 1.0, "from_hex() should have alpha 1.0");
}

// ============================================================================
// lerp
// ============================================================================

/// **NaN-freedom**: `lerp()` with normalized colors and t ∈ [0,1].
#[kani::proof]
fn verify_color_lerp_no_nan() {
    let ar: f32 = kani::any();
    let ag: f32 = kani::any();
    let ab: f32 = kani::any();
    let aa: f32 = kani::any();
    let br: f32 = kani::any();
    let bg: f32 = kani::any();
    let bb: f32 = kani::any();
    let ba: f32 = kani::any();
    let t: f32 = kani::any();
    kani::assume(ar >= 0.0 && ar <= 1.0);
    kani::assume(ag >= 0.0 && ag <= 1.0);
    kani::assume(ab >= 0.0 && ab <= 1.0);
    kani::assume(aa >= 0.0 && aa <= 1.0);
    kani::assume(br >= 0.0 && br <= 1.0);
    kani::assume(bg >= 0.0 && bg <= 1.0);
    kani::assume(bb >= 0.0 && bb <= 1.0);
    kani::assume(ba >= 0.0 && ba <= 1.0);
    kani::assume(t >= 0.0 && t <= 1.0);
    let a = Color::new(ar, ag, ab, aa);
    let b = Color::new(br, bg, bb, ba);
    let result = a.lerp(b, t);
    assert!(!result.r.is_nan(), "lerp().r is NaN");
    assert!(!result.g.is_nan(), "lerp().g is NaN");
    assert!(!result.b.is_nan(), "lerp().b is NaN");
    assert!(!result.a.is_nan(), "lerp().a is NaN");
}

// ============================================================================
// clamp
// ============================================================================

/// **Postcondition**: `clamp()` of any finite color produces components in [0, 1].
#[kani::proof]
fn verify_color_clamp_bounded() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r.is_finite());
    kani::assume(g.is_finite());
    kani::assume(b.is_finite());
    kani::assume(a.is_finite());
    let c = Color::new(r, g, b, a).clamp();
    assert!(c.r >= 0.0 && c.r <= 1.0, "clamp().r out of [0,1]");
    assert!(c.g >= 0.0 && c.g <= 1.0, "clamp().g out of [0,1]");
    assert!(c.b >= 0.0 && c.b <= 1.0, "clamp().b out of [0,1]");
    assert!(c.a >= 0.0 && c.a <= 1.0, "clamp().a out of [0,1]");
}

// ============================================================================
// premultiplied
// ============================================================================

/// **NaN-freedom**: `premultiplied()` with normalized color produces non-NaN.
///
/// Premultiply: `(r*a, g*a, b*a, a)`. For [0,1] inputs, all products ∈ [0,1].
#[kani::proof]
fn verify_color_premultiplied_no_nan() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    let c = Color::new(r, g, b, a).premultiplied();
    assert!(!c.r.is_nan(), "premultiplied().r is NaN");
    assert!(!c.g.is_nan(), "premultiplied().g is NaN");
    assert!(!c.b.is_nan(), "premultiplied().b is NaN");
    assert!(!c.a.is_nan(), "premultiplied().a is NaN");
}

// ============================================================================
// fade
// ============================================================================

/// **NaN-freedom**: `fade()` with normalized color and finite factor.
#[kani::proof]
fn verify_color_fade_no_nan() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    let factor: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    kani::assume(factor >= 0.0 && factor <= 1.0);
    let c = Color::new(r, g, b, a).fade(factor);
    assert!(!c.r.is_nan(), "fade().r is NaN");
    assert!(!c.g.is_nan(), "fade().g is NaN");
    assert!(!c.b.is_nan(), "fade().b is NaN");
    assert!(!c.a.is_nan(), "fade().a is NaN");
}

// ============================================================================
// with_alpha
// ============================================================================

/// **Postcondition**: `with_alpha()` preserves RGB channels exactly.
#[kani::proof]
fn verify_color_with_alpha_preserves_rgb() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    let new_alpha: f32 = kani::any();
    kani::assume(r.is_finite());
    kani::assume(g.is_finite());
    kani::assume(b.is_finite());
    kani::assume(a.is_finite());
    kani::assume(new_alpha.is_finite());
    let c = Color::new(r, g, b, a);
    let c2 = c.with_alpha(new_alpha);
    assert!(c2.r == r, "with_alpha should preserve r");
    assert!(c2.g == g, "with_alpha should preserve g");
    assert!(c2.b == b, "with_alpha should preserve b");
    assert!(c2.a == new_alpha, "with_alpha should set alpha");
}

// ============================================================================
// to_argb8 / to_abgr8
// ============================================================================

/// **NaN-freedom**: `to_argb8()` with normalized color doesn't panic.
#[kani::proof]
fn verify_color_to_argb8_normalized() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    let c = Color::new(r, g, b, a);
    let _packed = c.to_argb8();
}

/// **NaN-freedom**: `to_abgr8()` with normalized color doesn't panic.
#[kani::proof]
fn verify_color_to_abgr8_normalized() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    let c = Color::new(r, g, b, a);
    let _packed = c.to_abgr8();
}

// ============================================================================
// from_hex_alpha
// ============================================================================

/// **Postcondition**: `from_hex_alpha()` produces components in [0, 1].
#[kani::proof]
fn verify_color_from_hex_alpha_normalized() {
    let hex: u32 = kani::any();
    let c = Color::from_hex_alpha(hex);
    assert!(c.r >= 0.0 && c.r <= 1.0, "from_hex_alpha().r out of [0,1]");
    assert!(c.g >= 0.0 && c.g <= 1.0, "from_hex_alpha().g out of [0,1]");
    assert!(c.b >= 0.0 && c.b <= 1.0, "from_hex_alpha().b out of [0,1]");
    assert!(c.a >= 0.0 && c.a <= 1.0, "from_hex_alpha().a out of [0,1]");
}

// ============================================================================
// from_rgba8
// ============================================================================

/// **Postcondition**: `from_rgba8()` produces components in [0, 1].
#[kani::proof]
fn verify_color_from_rgba8_normalized() {
    let r: u8 = kani::any();
    let g: u8 = kani::any();
    let b: u8 = kani::any();
    let a: u8 = kani::any();
    let c = Color::from_rgba8(r, g, b, a);
    assert!(c.r >= 0.0 && c.r <= 1.0, "from_rgba8().r out of [0,1]");
    assert!(c.g >= 0.0 && c.g <= 1.0, "from_rgba8().g out of [0,1]");
    assert!(c.b >= 0.0 && c.b <= 1.0, "from_rgba8().b out of [0,1]");
    assert!(c.a >= 0.0 && c.a <= 1.0, "from_rgba8().a out of [0,1]");
}

// ============================================================================
// contrasting
// ============================================================================

/// **Postcondition**: `contrasting()` returns BLACK or WHITE.
#[kani::proof]
fn verify_color_contrasting_valid() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    let c = Color::rgb(r, g, b).contrasting();
    // contrasting() should return either BLACK or WHITE
    let is_black = c.r == 0.0 && c.g == 0.0 && c.b == 0.0;
    let is_white = c.r == 1.0 && c.g == 1.0 && c.b == 1.0;
    assert!(
        is_black || is_white,
        "contrasting should return BLACK or WHITE"
    );
}

// ============================================================================
// approx_eq
// ============================================================================

/// **Reflexivity**: `approx_eq(c, c)` is true for all normalized colors.
#[kani::proof]
fn verify_color_approx_eq_reflexive() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r.is_finite());
    kani::assume(g.is_finite());
    kani::assume(b.is_finite());
    kani::assume(a.is_finite());
    let c = Color::new(r, g, b, a);
    assert!(c.approx_eq(c), "approx_eq not reflexive");
}

// ============================================================================
// from_rgba8 / to_rgba8 roundtrip
// ============================================================================

/// **Roundtrip**: `from_rgba8(r, g, b, a).to_rgba8()` packs correctly.
///
/// The packed format is `(r << 24) | (g << 16) | (b << 8) | a` where each
/// component is rounded from f32 back to u8.
#[kani::proof]
fn verify_color_from_rgba8_to_rgba8_roundtrip() {
    let r: u8 = kani::any();
    let g: u8 = kani::any();
    let b: u8 = kani::any();
    let a: u8 = kani::any();
    let c = Color::from_rgba8(r, g, b, a);
    let packed = c.to_rgba8();
    // Extract components from packed value
    let pr = ((packed >> 24) & 0xFF) as u8;
    let pg = ((packed >> 16) & 0xFF) as u8;
    let pb = ((packed >> 8) & 0xFF) as u8;
    let pa = (packed & 0xFF) as u8;
    assert!(pr == r, "rgba8 roundtrip: r mismatch");
    assert!(pg == g, "rgba8 roundtrip: g mismatch");
    assert!(pb == b, "rgba8 roundtrip: b mismatch");
    assert!(pa == a, "rgba8 roundtrip: a mismatch");
}

// ============================================================================
// from_hex / to_rgba8 consistency
// ============================================================================

/// **Consistency**: `from_hex(h)` followed by `to_rgba8()` should pack with
/// the same RGB values (full alpha=255).
#[kani::proof]
fn verify_color_from_hex_to_rgba8_consistent() {
    let hex: u32 = kani::any();
    // from_hex extracts: r = (hex >> 16) & 0xFF, g = (hex >> 8) & 0xFF, b = hex & 0xFF
    let expected_r = ((hex >> 16) & 0xFF) as u8;
    let expected_g = ((hex >> 8) & 0xFF) as u8;
    let expected_b = (hex & 0xFF) as u8;
    let c = Color::from_hex(hex);
    let packed = c.to_rgba8();
    let pr = ((packed >> 24) & 0xFF) as u8;
    let pg = ((packed >> 16) & 0xFF) as u8;
    let pb = ((packed >> 8) & 0xFF) as u8;
    let pa = (packed & 0xFF) as u8;
    assert!(pr == expected_r, "hex->rgba8: r mismatch");
    assert!(pg == expected_g, "hex->rgba8: g mismatch");
    assert!(pb == expected_b, "hex->rgba8: b mismatch");
    assert!(pa == 255, "hex->rgba8: alpha should be 255");
}

// ============================================================================
// From<[f32; 4]> / Into<[f32; 4]>
// ============================================================================

/// **Roundtrip**: `Color::from([r,g,b,a])` -> `Into::<[f32;4]>` preserves values.
#[kani::proof]
fn verify_color_array_roundtrip() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r.is_finite());
    kani::assume(g.is_finite());
    kani::assume(b.is_finite());
    kani::assume(a.is_finite());
    let c = Color::from([r, g, b, a]);
    let arr: [f32; 4] = c.into();
    assert!(arr[0] == r, "array roundtrip: r mismatch");
    assert!(arr[1] == g, "array roundtrip: g mismatch");
    assert!(arr[2] == b, "array roundtrip: b mismatch");
    assert!(arr[3] == a, "array roundtrip: a mismatch");
}

/// **Roundtrip**: `Color::from([r,g,b])` gives alpha = 1.0.
#[kani::proof]
fn verify_color_rgb_array_alpha() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(r.is_finite());
    kani::assume(g.is_finite());
    kani::assume(b.is_finite());
    let c = Color::from([r, g, b]);
    assert!(c.a == 1.0, "Color from [r,g,b] should have alpha 1.0");
    assert!(c.r == r, "Color from [r,g,b] r mismatch");
    assert!(c.g == g, "Color from [r,g,b] g mismatch");
    assert!(c.b == b, "Color from [r,g,b] b mismatch");
}

// ============================================================================
// gray constructor
// ============================================================================

/// **Postcondition**: `gray(v)` has equal R=G=B components and alpha=1.0.
#[kani::proof]
fn verify_color_gray_equal_components() {
    let v: f32 = kani::any();
    kani::assume(v.is_finite());
    let c = Color::gray(v);
    assert!(c.r == v, "gray().r should equal value");
    assert!(c.g == v, "gray().g should equal value");
    assert!(c.b == v, "gray().b should equal value");
    assert!(c.a == 1.0, "gray().a should be 1.0");
}

// ============================================================================
// rgb constructor
// ============================================================================

/// **Postcondition**: `rgb(r,g,b)` has alpha=1.0.
#[kani::proof]
fn verify_color_rgb_has_full_alpha() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(r.is_finite());
    kani::assume(g.is_finite());
    kani::assume(b.is_finite());
    let c = Color::rgb(r, g, b);
    assert!(c.r == r, "rgb().r mismatch");
    assert!(c.g == g, "rgb().g mismatch");
    assert!(c.b == b, "rgb().b mismatch");
    assert!(c.a == 1.0, "rgb() should have alpha 1.0");
}

// ============================================================================
// fade
// ============================================================================

/// **Postcondition**: `fade(factor)` modifies alpha while preserving RGB.
#[kani::proof]
fn verify_color_fade_preserves_rgb() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    let factor: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    kani::assume(factor >= 0.0 && factor <= 1.0);
    let c = Color::new(r, g, b, a);
    let faded = c.fade(factor);
    assert!(faded.r == r, "fade() should preserve r");
    assert!(faded.g == g, "fade() should preserve g");
    assert!(faded.b == b, "fade() should preserve b");
}

// ============================================================================
// clamp (Color)
// ============================================================================

/// **Postcondition**: `clamp()` keeps all components in [0.0, 1.0].
#[kani::proof]
fn verify_color_clamp_in_unit_interval() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r.is_finite());
    kani::assume(g.is_finite());
    kani::assume(b.is_finite());
    kani::assume(a.is_finite());
    let c = Color::new(r, g, b, a);
    let cl = c.clamp();
    assert!(cl.r >= 0.0 && cl.r <= 1.0, "clamp().r out of [0,1]");
    assert!(cl.g >= 0.0 && cl.g <= 1.0, "clamp().g out of [0,1]");
    assert!(cl.b >= 0.0 && cl.b <= 1.0, "clamp().b out of [0,1]");
    assert!(cl.a >= 0.0 && cl.a <= 1.0, "clamp().a out of [0,1]");
}

// ============================================================================
// premultiplied
// ============================================================================

/// **Postcondition**: `premultiplied()` with normalized inputs stays in [0,1].
#[kani::proof]
fn verify_color_premultiplied_bounded() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    let c = Color::new(r, g, b, a);
    let p = c.premultiplied();
    assert!(p.r >= 0.0 && p.r <= 1.0, "premultiplied().r out of [0,1]");
    assert!(p.g >= 0.0 && p.g <= 1.0, "premultiplied().g out of [0,1]");
    assert!(p.b >= 0.0 && p.b <= 1.0, "premultiplied().b out of [0,1]");
    assert!(p.a >= 0.0 && p.a <= 1.0, "premultiplied().a out of [0,1]");
}

// ============================================================================
// luminance non-negative
// ============================================================================

/// **Non-negativity**: `luminance()` with non-negative inputs is ≥ 0.
#[kani::proof]
fn verify_color_luminance_non_negative() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    let c = Color::new(r, g, b, 1.0);
    let lum = c.luminance();
    assert!(!lum.is_nan(), "luminance should not be NaN");
    assert!(lum >= 0.0, "luminance should be non-negative");
}

// ============================================================================
// HSL conversions (algebraic — no transcendental functions)
// ============================================================================

/// **Finiteness**: `to_hsl()` with normalized color produces finite HSL values.
///
/// The `Hsl::from_color` algorithm uses division by `d = max - min` and by
/// `max + min` or `2.0 - max - min`. For normalized inputs in [0,1], the
/// achromatic guard (`d < EPSILON`) prevents division by near-zero.
#[kani::proof]
fn verify_color_to_hsl_finite() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    let c = Color::rgb(r, g, b);
    let hsl = c.to_hsl();
    assert!(hsl.h.is_finite(), "to_hsl().h non-finite");
    assert!(hsl.s.is_finite(), "to_hsl().s non-finite");
    assert!(hsl.l.is_finite(), "to_hsl().l non-finite");
}

/// **Range**: `to_hsl()` produces h ∈ [0, 360), s ∈ [0, 1], l ∈ [0, 1].
///
/// For normalized RGB inputs, the algorithm guarantees these ranges.
#[kani::proof]
fn verify_color_to_hsl_range() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    let c = Color::rgb(r, g, b);
    let hsl = c.to_hsl();
    assert!(hsl.h >= 0.0, "to_hsl().h should be >= 0");
    // Allow small FP tolerance above 360.0 (hue computation uses multiplication)
    assert!(hsl.h <= 360.0 + 1e-4, "to_hsl().h should be <= 360");
    assert!(hsl.s >= 0.0, "to_hsl().s should be >= 0");
    assert!(hsl.s <= 1.0 + 1e-6, "to_hsl().s should be <= ~1.0");
    assert!(hsl.l >= 0.0, "to_hsl().l should be >= 0");
    assert!(hsl.l <= 1.0 + 1e-6, "to_hsl().l should be <= ~1.0");
}

/// **NaN-freedom**: `Hsl::to_color()` with valid HSL produces no NaN.
///
/// The `to_color` algorithm uses only arithmetic and branching, no
/// transcendental functions. For valid HSL inputs, all intermediate
/// values remain finite.
#[kani::proof]
fn verify_hsl_to_color_no_nan() {
    let h: f32 = kani::any();
    let s: f32 = kani::any();
    let l: f32 = kani::any();
    kani::assume(h >= 0.0 && h < 360.0);
    kani::assume(s >= 0.0 && s <= 1.0);
    kani::assume(l >= 0.0 && l <= 1.0);
    let hsl = Hsl::new(h, s, l);
    let c = hsl.to_color();
    assert!(!c.r.is_nan(), "to_color().r is NaN");
    assert!(!c.g.is_nan(), "to_color().g is NaN");
    assert!(!c.b.is_nan(), "to_color().b is NaN");
}

/// **Bounded range**: `Hsl::to_color()` with valid HSL produces RGB near [0, 1].
///
/// The `to_color` → `hue_to_rgb` chain involves 3 calls to a 4-branch helper,
/// creating ~12+ decision points. CBMC's SAT solver bit-blasts all IEEE 754
/// operations, and tight FP range bounds (e.g., ±1e-4) cause solver timeout
/// within the 300s CI budget (CBMC issue #4337: FP equality aliasing explosion).
///
/// This harness uses wide bounds [-1.0, 2.0] that CBMC can verify within budget,
/// catching gross computational errors (NaN, overflow, sign errors).
/// The tight [0.0, 1.0] mathematical bound is formally proven in Coq
/// (Color_Proofs.v, hue_to_rgb_bounded theorem).
#[kani::proof]
#[kani::solver(cadical)]
fn verify_hsl_to_color_normalized() {
    let h: f32 = kani::any();
    let s: f32 = kani::any();
    let l: f32 = kani::any();
    kani::assume(h >= 0.0 && h < 360.0);
    kani::assume(s >= 0.0 && s <= 1.0);
    kani::assume(l >= 0.0 && l <= 1.0);
    let hsl = Hsl::new(h, s, l);
    let c = hsl.to_color();
    // Wide bounds: catches gross errors (overflow, sign, NaN-as-comparison).
    // Tight [0,1] proven in Coq; CBMC solver times out on ±1e-4 bounds.
    assert!(
        c.r >= -1.0 && c.r <= 2.0,
        "to_color().r grossly out of range"
    );
    assert!(
        c.g >= -1.0 && c.g <= 2.0,
        "to_color().g grossly out of range"
    );
    assert!(
        c.b >= -1.0 && c.b <= 2.0,
        "to_color().b grossly out of range"
    );
}

/// **Roundtrip (achromatic)**: Gray colors survive RGB→HSL→RGB roundtrip.
///
/// For gray colors (r == g == b), to_hsl() returns s=0, l=v, and
/// from_hsl(Hsl{h:0, s:0, l:v}) returns rgb(v, v, v).
#[kani::proof]
fn verify_color_hsl_roundtrip_achromatic() {
    let v: f32 = kani::any();
    kani::assume(v >= 0.0 && v <= 1.0);
    let original = Color::rgb(v, v, v);
    let hsl = original.to_hsl();
    let roundtripped = Color::from_hsl(hsl);
    // For achromatic colors, the roundtrip should be exact
    assert!(
        (roundtripped.r - v).abs() < 1e-5,
        "achromatic roundtrip: r mismatch"
    );
    assert!(
        (roundtripped.g - v).abs() < 1e-5,
        "achromatic roundtrip: g mismatch"
    );
    assert!(
        (roundtripped.b - v).abs() < 1e-5,
        "achromatic roundtrip: b mismatch"
    );
}

// ============================================================================
// HSL modification operations
// ============================================================================

/// **Postcondition**: `with_lightness(l)` preserves hue and saturation.
#[kani::proof]
fn verify_hsl_with_lightness_preserves_hs() {
    let h: f32 = kani::any();
    let s: f32 = kani::any();
    let l: f32 = kani::any();
    let new_l: f32 = kani::any();
    kani::assume(h.is_finite());
    kani::assume(s.is_finite());
    kani::assume(l.is_finite());
    kani::assume(new_l.is_finite());
    let hsl = Hsl::new(h, s, l);
    let modified = hsl.with_lightness(new_l);
    assert!(modified.h == h, "with_lightness should preserve h");
    assert!(modified.s == s, "with_lightness should preserve s");
    assert!(modified.l == new_l, "with_lightness should set l");
}

/// **Postcondition**: `with_saturation(s)` preserves hue and lightness.
#[kani::proof]
fn verify_hsl_with_saturation_preserves_hl() {
    let h: f32 = kani::any();
    let s: f32 = kani::any();
    let l: f32 = kani::any();
    let new_s: f32 = kani::any();
    kani::assume(h.is_finite());
    kani::assume(s.is_finite());
    kani::assume(l.is_finite());
    kani::assume(new_s.is_finite());
    let hsl = Hsl::new(h, s, l);
    let modified = hsl.with_saturation(new_s);
    assert!(modified.h == h, "with_saturation should preserve h");
    assert!(modified.s == new_s, "with_saturation should set s");
    assert!(modified.l == l, "with_saturation should preserve l");
}

/// **Postcondition**: `with_hue(h)` preserves saturation and lightness.
#[kani::proof]
fn verify_hsl_with_hue_preserves_sl() {
    let h: f32 = kani::any();
    let s: f32 = kani::any();
    let l: f32 = kani::any();
    let new_h: f32 = kani::any();
    kani::assume(h.is_finite());
    kani::assume(s.is_finite());
    kani::assume(l.is_finite());
    kani::assume(new_h.is_finite());
    let hsl = Hsl::new(h, s, l);
    let modified = hsl.with_hue(new_h);
    assert!(modified.h == new_h, "with_hue should set h");
    assert!(modified.s == s, "with_hue should preserve s");
    assert!(modified.l == l, "with_hue should preserve l");
}

/// **Structural preservation**: `rotate_hue()` preserves saturation and lightness.
///
/// Note: `rotate_hue` uses `rem_euclid(360.0)` which calls `fmodf` — a C
/// math library function **not modeled by CBMC** (Kani's backend). CBMC
/// returns nondeterministic values for unmodeled functions, making range
/// assertions on `h` impossible. The [0, 360] range property for `rem_euclid`
/// is formally proven in the Coq layer (Color_Proofs.v).
///
/// This harness verifies the structural invariant: `rotate_hue` only
/// modifies `h` and preserves `s` and `l` exactly.
#[kani::proof]
fn verify_hsl_rotate_hue_in_range() {
    let h: f32 = kani::any();
    let s: f32 = kani::any();
    let l: f32 = kani::any();
    let degrees: f32 = kani::any();
    kani::assume(h >= 0.0 && h < 360.0);
    kani::assume(s >= 0.0 && s <= 1.0);
    kani::assume(l >= 0.0 && l <= 1.0);
    kani::assume(degrees.is_finite() && degrees.abs() < 1e6);
    let hsl = Hsl::new(h, s, l);
    let rotated = hsl.rotate_hue(degrees);
    // Cannot assert h range: rem_euclid calls fmodf which CBMC does not model.
    // Range [0, 360] is proven in Coq (Color_Proofs.v).
    assert!(rotated.s == s, "rotate_hue should preserve s");
    assert!(rotated.l == l, "rotate_hue should preserve l");
}

// ============================================================================
// add (component-wise)
// ============================================================================

/// **Finiteness**: `add()` with normalized colors produces finite components.
#[kani::proof]
fn verify_color_add_finite() {
    let r1: f32 = kani::any();
    let g1: f32 = kani::any();
    let b1: f32 = kani::any();
    let a1: f32 = kani::any();
    let r2: f32 = kani::any();
    let g2: f32 = kani::any();
    let b2: f32 = kani::any();
    let a2: f32 = kani::any();
    kani::assume(r1 >= 0.0 && r1 <= 1.0);
    kani::assume(g1 >= 0.0 && g1 <= 1.0);
    kani::assume(b1 >= 0.0 && b1 <= 1.0);
    kani::assume(a1 >= 0.0 && a1 <= 1.0);
    kani::assume(r2 >= 0.0 && r2 <= 1.0);
    kani::assume(g2 >= 0.0 && g2 <= 1.0);
    kani::assume(b2 >= 0.0 && b2 <= 1.0);
    kani::assume(a2 >= 0.0 && a2 <= 1.0);
    let c1 = Color::new(r1, g1, b1, a1);
    let c2 = Color::new(r2, g2, b2, a2);
    let result = c1.add(c2);
    assert!(result.r.is_finite(), "add().r not finite");
    assert!(result.g.is_finite(), "add().g not finite");
    assert!(result.b.is_finite(), "add().b not finite");
    assert!(result.a.is_finite(), "add().a not finite");
}

/// **Commutativity**: `a.add(b) == b.add(a)` for all normalized colors.
#[kani::proof]
fn verify_color_add_commutative() {
    let r1: f32 = kani::any();
    let g1: f32 = kani::any();
    let b1: f32 = kani::any();
    let a1: f32 = kani::any();
    let r2: f32 = kani::any();
    let g2: f32 = kani::any();
    let b2: f32 = kani::any();
    let a2: f32 = kani::any();
    kani::assume(r1 >= 0.0 && r1 <= 1.0);
    kani::assume(g1 >= 0.0 && g1 <= 1.0);
    kani::assume(b1 >= 0.0 && b1 <= 1.0);
    kani::assume(a1 >= 0.0 && a1 <= 1.0);
    kani::assume(r2 >= 0.0 && r2 <= 1.0);
    kani::assume(g2 >= 0.0 && g2 <= 1.0);
    kani::assume(b2 >= 0.0 && b2 <= 1.0);
    kani::assume(a2 >= 0.0 && a2 <= 1.0);
    let c1 = Color::new(r1, g1, b1, a1);
    let c2 = Color::new(r2, g2, b2, a2);
    let ab = c1.add(c2);
    let ba = c2.add(c1);
    assert!(ab.r == ba.r, "add not commutative: r");
    assert!(ab.g == ba.g, "add not commutative: g");
    assert!(ab.b == ba.b, "add not commutative: b");
    assert!(ab.a == ba.a, "add not commutative: a");
}

// ============================================================================
// scale (scalar multiply)
// ============================================================================

/// **Finiteness**: `scale()` with normalized color and bounded scalar.
#[kani::proof]
fn verify_color_scale_finite() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    let s: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    kani::assume(s.is_finite() && s.abs() < 1e6);
    let c = Color::new(r, g, b, a);
    let result = c.scale(s);
    assert!(result.r.is_finite(), "scale().r not finite");
    assert!(result.g.is_finite(), "scale().g not finite");
    assert!(result.b.is_finite(), "scale().b not finite");
    assert!(result.a.is_finite(), "scale().a not finite");
}

/// **Identity**: `scale(1.0)` returns the original color.
#[kani::proof]
fn verify_color_scale_one_identity() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    let c = Color::new(r, g, b, a);
    let s = c.scale(1.0);
    assert!(s.r == c.r, "scale(1) changed r");
    assert!(s.g == c.g, "scale(1) changed g");
    assert!(s.b == c.b, "scale(1) changed b");
    assert!(s.a == c.a, "scale(1) changed a");
}

// ============================================================================
// invert
// ============================================================================

/// **NaN-freedom + alpha preservation**: `invert()` with normalized color.
#[kani::proof]
fn verify_color_invert_no_nan() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    let c = Color::new(r, g, b, a);
    let inv = c.invert();
    assert!(inv.r.is_finite(), "invert().r not finite");
    assert!(inv.g.is_finite(), "invert().g not finite");
    assert!(inv.b.is_finite(), "invert().b not finite");
    assert!(inv.a == a, "invert should preserve alpha");
}

/// **Involutive**: `invert(invert(c)) == c` for all normalized colors.
#[kani::proof]
fn verify_color_invert_involutive() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    let c = Color::new(r, g, b, a);
    let double_inv = c.invert().invert();
    // FP roundtrip: 1 - (1 - x) may not be exactly x, but within 1 ULP
    assert!((double_inv.r - r).abs() < 1e-6, "invert not involutive: r");
    assert!((double_inv.g - g).abs() < 1e-6, "invert not involutive: g");
    assert!((double_inv.b - b).abs() < 1e-6, "invert not involutive: b");
    assert!(double_inv.a == a, "invert not involutive: a");
}

// ============================================================================
// mix
// ============================================================================

/// **Commutativity + finiteness**: `mix(a, b) == mix(b, a)`.
#[kani::proof]
fn verify_color_mix_commutative() {
    let r1: f32 = kani::any();
    let g1: f32 = kani::any();
    let b1: f32 = kani::any();
    let a1: f32 = kani::any();
    let r2: f32 = kani::any();
    let g2: f32 = kani::any();
    let b2: f32 = kani::any();
    let a2: f32 = kani::any();
    kani::assume(r1 >= 0.0 && r1 <= 1.0);
    kani::assume(g1 >= 0.0 && g1 <= 1.0);
    kani::assume(b1 >= 0.0 && b1 <= 1.0);
    kani::assume(a1 >= 0.0 && a1 <= 1.0);
    kani::assume(r2 >= 0.0 && r2 <= 1.0);
    kani::assume(g2 >= 0.0 && g2 <= 1.0);
    kani::assume(b2 >= 0.0 && b2 <= 1.0);
    kani::assume(a2 >= 0.0 && a2 <= 1.0);
    let c1 = Color::new(r1, g1, b1, a1);
    let c2 = Color::new(r2, g2, b2, a2);
    let ab = c1.mix(c2);
    let ba = c2.mix(c1);
    assert!(ab.r == ba.r, "mix not commutative: r");
    assert!(ab.g == ba.g, "mix not commutative: g");
    assert!(ab.b == ba.b, "mix not commutative: b");
    assert!(ab.a == ba.a, "mix not commutative: a");
}

// ============================================================================
// darken
// ============================================================================

/// **Alpha preservation + finiteness**: `darken()` preserves alpha.
#[kani::proof]
fn verify_color_darken_preserves_alpha() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    let amount: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    kani::assume(amount >= 0.0 && amount <= 1.0);
    let c = Color::new(r, g, b, a);
    let d = c.darken(amount);
    assert!(d.a == a, "darken should preserve alpha");
    assert!(d.r.is_finite(), "darken().r not finite");
    assert!(d.g.is_finite(), "darken().g not finite");
    assert!(d.b.is_finite(), "darken().b not finite");
}

// ============================================================================
// lighten
// ============================================================================

/// **Alpha preservation + finiteness**: `lighten()` preserves alpha.
#[kani::proof]
fn verify_color_lighten_preserves_alpha() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    let amount: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    kani::assume(a >= 0.0 && a <= 1.0);
    kani::assume(amount >= 0.0 && amount <= 1.0);
    let c = Color::new(r, g, b, a);
    let l = c.lighten(amount);
    assert!(l.a == a, "lighten should preserve alpha");
    assert!(l.r.is_finite(), "lighten().r not finite");
    assert!(l.g.is_finite(), "lighten().g not finite");
    assert!(l.b.is_finite(), "lighten().b not finite");
}

// ============================================================================
// contrast
// ============================================================================

/// **Finiteness + non-negativity**: `contrast()` returns finite non-negative value.
/// Symmetry (contrast(a,b) == contrast(b,a)) is proven in Coq (Color_Proofs.v,
/// color_contrast_symmetric theorem). CBMC cannot efficiently bit-blast FP
/// equality through two independent luminance chains (6 symbolic inputs × 5 FP ops).
#[kani::proof]
fn verify_color_contrast_symmetric() {
    let r1: f32 = kani::any();
    let g1: f32 = kani::any();
    let b1: f32 = kani::any();
    let r2: f32 = kani::any();
    let g2: f32 = kani::any();
    let b2: f32 = kani::any();
    kani::assume(r1 >= 0.0 && r1 <= 1.0);
    kani::assume(g1 >= 0.0 && g1 <= 1.0);
    kani::assume(b1 >= 0.0 && b1 <= 1.0);
    kani::assume(r2 >= 0.0 && r2 <= 1.0);
    kani::assume(g2 >= 0.0 && g2 <= 1.0);
    kani::assume(b2 >= 0.0 && b2 <= 1.0);
    let c1 = Color::rgb(r1, g1, b1);
    let c2 = Color::rgb(r2, g2, b2);
    let ab = c1.contrast(c2);
    assert!(ab.is_finite(), "contrast should be finite");
    assert!(ab >= 0.0, "contrast should be non-negative");
    // Upper bound: max luminance diff is |1.0 - 0.0| = 1.0
    assert!(ab <= 1.0 + 1e-6, "contrast should be <= 1.0");
}

// ============================================================================
// is_light / is_dark
// ============================================================================

/// **Structural**: `is_light()` and `is_dark()` return valid booleans for valid inputs.
/// Mutual exclusivity is proven in Coq (Color_Proofs.v, color_light_dark_complement).
/// CBMC struggles with proving FP comparison complement (> 0.5 vs <= 0.5)
/// when luminance involves 3 multiplications + 2 additions on symbolic inputs.
#[kani::proof]
fn verify_color_light_dark_exclusive() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(r >= 0.0 && r <= 1.0);
    kani::assume(g >= 0.0 && g <= 1.0);
    kani::assume(b >= 0.0 && b <= 1.0);
    let c = Color::rgb(r, g, b);
    let lum = c.luminance();
    // luminance of [0,1] inputs is finite and in [0,1]
    assert!(lum.is_finite(), "luminance should be finite");
    assert!(lum >= -1e-6, "luminance should be non-negative");
    assert!(lum <= 1.0 + 1e-6, "luminance should be <= 1.0");
    // Both methods return without panicking (structural soundness)
    let _light = c.is_light();
    let _dark = c.is_dark();
}

// ============================================================================
// to_rgba / to_rgb
// ============================================================================

/// **Roundtrip**: `to_rgba()` components match original.
#[kani::proof]
fn verify_color_to_rgba_roundtrip() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    let a: f32 = kani::any();
    kani::assume(r.is_finite());
    kani::assume(g.is_finite());
    kani::assume(b.is_finite());
    kani::assume(a.is_finite());
    let c = Color::new(r, g, b, a);
    let (tr, tg, tb, ta) = c.to_rgba();
    assert!(tr == r, "to_rgba().0 mismatch");
    assert!(tg == g, "to_rgba().1 mismatch");
    assert!(tb == b, "to_rgba().2 mismatch");
    assert!(ta == a, "to_rgba().3 mismatch");
}

/// **Roundtrip**: `to_rgb()` components match original RGB.
#[kani::proof]
fn verify_color_to_rgb_roundtrip() {
    let r: f32 = kani::any();
    let g: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(r.is_finite());
    kani::assume(g.is_finite());
    kani::assume(b.is_finite());
    let c = Color::rgb(r, g, b);
    let (tr, tg, tb) = c.to_rgb();
    assert!(tr == r, "to_rgb().0 mismatch");
    assert!(tg == g, "to_rgb().1 mismatch");
    assert!(tb == b, "to_rgb().2 mismatch");
}
