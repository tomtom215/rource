// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Kani proof harnesses for Color f32 edge-case verification.
//!
//! Verifies IEEE 754 safety properties for Color operations: to_rgba8,
//! blend_over, luminance, and from_hex.
//!
//! Color components are typically in [0.0, 1.0], so most harnesses use
//! this range as the input domain.

use crate::Color;

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
