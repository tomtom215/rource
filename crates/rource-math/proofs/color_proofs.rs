// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! # Formal Verification of Color Operations
//!
//! This module contains machine-checked proofs of correctness for Color operations
//! using the Verus formal verification tool.
//!
//! ## Verification Status
//!
//! All proofs in this file have been verified by Verus with zero admits.
//!
//! ## Properties Verified
//!
//! 1. **Constructor Properties**
//!    - `new` sets components correctly
//!    - `rgb` sets alpha to 1 (opaque)
//!    - `gray` sets equal R, G, B components
//!
//! 2. **Alpha Operations**
//!    - `with_alpha` preserves RGB, changes alpha
//!    - `fade(0)` produces zero alpha
//!    - `fade(1)` preserves alpha
//!
//! 3. **Interpolation Properties**
//!    - `lerp(c, c, t) = c` for any t (same-color identity)
//!    - `lerp(a, b, 0) = a` (start boundary)
//!    - `lerp(a, b, 1) = b` (end boundary)
//!
//! 4. **Blending Properties**
//!    - Opaque foreground covers background completely
//!    - Transparent foreground shows background completely
//!
//! 5. **Premultiplication Properties**
//!    - `premultiplied` with alpha=1 preserves RGB
//!    - `premultiplied` with alpha=0 zeroes RGB
//!
//! ## Proof Methodology
//!
//! Colors are modeled over mathematical integers (range [0, 1000] as scaled
//! fixed-point) to prove algebraic correctness. The translation to IEEE 754
//! floating point introduces precision considerations documented separately.
//! For blend_over, we use scaled arithmetic: value * 1000 represents [0.0, 1.0].
//!
//! ## Verification Command
//!
//! ```bash
//! /tmp/verus/verus crates/rource-math/proofs/color_proofs.rs
//! ```

use vstd::prelude::*;

verus! {

// =============================================================================
// Color Specification Type (Integer Model)
// =============================================================================

/// Mathematical specification of an RGBA color over integers.
/// Components are scaled by 1000 to represent [0.0, 1.0] as [0, 1000].
#[derive(PartialEq, Eq)]
pub struct SpecColor {
    pub r: int,
    pub g: int,
    pub b: int,
    pub a: int,
}

// =============================================================================
// Color Operations (Spec Functions)
// =============================================================================

/// Creates a new color with the given RGBA components.
pub open spec fn color_new(r: int, g: int, b: int, a: int) -> SpecColor {
    SpecColor { r, g, b, a }
}

/// Creates an opaque color with the given RGB components (alpha = 1000).
pub open spec fn color_rgb(r: int, g: int, b: int) -> SpecColor {
    SpecColor { r, g, b, a: 1000 }
}

/// Creates a grayscale color with given intensity (alpha = 1000).
pub open spec fn color_gray(value: int) -> SpecColor {
    SpecColor { r: value, g: value, b: value, a: 1000 }
}

/// Returns color with a different alpha value.
pub open spec fn color_with_alpha(c: SpecColor, alpha: int) -> SpecColor {
    SpecColor { r: c.r, g: c.g, b: c.b, a: alpha }
}

/// Returns color with alpha multiplied by a factor (scaled).
/// fade(c, f) means c.a * f / 1000 (since f is also scaled by 1000).
pub open spec fn color_fade(c: SpecColor, factor: int) -> SpecColor {
    SpecColor { r: c.r, g: c.g, b: c.b, a: c.a * factor / 1000 }
}

/// Linear interpolation: lerp(a, b, t) = a + (b - a) * t / 1000.
/// t is scaled by 1000 (t=0 means 0.0, t=1000 means 1.0).
pub open spec fn color_lerp(a: SpecColor, b: SpecColor, t: int) -> SpecColor {
    SpecColor {
        r: a.r + (b.r - a.r) * t / 1000,
        g: a.g + (b.g - a.g) * t / 1000,
        b: a.b + (b.b - a.b) * t / 1000,
        a: a.a + (b.a - a.a) * t / 1000,
    }
}

/// Premultiply RGB by alpha: each channel *= alpha / 1000.
pub open spec fn color_premultiplied(c: SpecColor) -> SpecColor {
    SpecColor {
        r: c.r * c.a / 1000,
        g: c.g * c.a / 1000,
        b: c.b * c.a / 1000,
        a: c.a,
    }
}

/// Alpha blending: result = src * src_alpha + dst * (1 - src_alpha).
/// All values scaled by 1000. inv_alpha = 1000 - src.a.
pub open spec fn color_blend_over(src: SpecColor, dst: SpecColor) -> SpecColor {
    let inv_alpha: int = 1000 - src.a;
    SpecColor {
        r: (src.r * src.a + dst.r * inv_alpha) / 1000,
        g: (src.g * src.a + dst.g * inv_alpha) / 1000,
        b: (src.b * src.a + dst.b * inv_alpha) / 1000,
        a: (src.a * 1000 + dst.a * inv_alpha) / 1000,
    }
}

/// Luminance (Rec. 709): 2126*R + 7152*G + 722*B (scaled by 10000).
pub open spec fn color_luminance_scaled(c: SpecColor) -> int {
    2126 * c.r + 7152 * c.g + 722 * c.b
}

/// Clamp a single value to [0, 1000].
pub open spec fn clamp_component(v: int) -> int {
    if v < 0 { 0 }
    else if v > 1000 { 1000 }
    else { v }
}

/// Clamp all color components to [0, 1000].
pub open spec fn color_clamp(c: SpecColor) -> SpecColor {
    SpecColor {
        r: clamp_component(c.r),
        g: clamp_component(c.g),
        b: clamp_component(c.b),
        a: clamp_component(c.a),
    }
}

// =============================================================================
// Named Constants
// =============================================================================

pub open spec fn color_transparent() -> SpecColor {
    SpecColor { r: 0, g: 0, b: 0, a: 0 }
}

pub open spec fn color_black() -> SpecColor {
    SpecColor { r: 0, g: 0, b: 0, a: 1000 }
}

pub open spec fn color_white() -> SpecColor {
    SpecColor { r: 1000, g: 1000, b: 1000, a: 1000 }
}

// =============================================================================
// CONSTRUCTOR PROOFS
// =============================================================================

/// **Theorem 1**: `new` correctly sets all components.
proof fn color_new_components(r: int, g: int, b: int, a: int)
    ensures ({
        let c = color_new(r, g, b, a);
        c.r == r && c.g == g && c.b == b && c.a == a
    }),
{
}

/// **Theorem 2**: `rgb` sets alpha to 1000 (opaque).
proof fn color_rgb_full_alpha(r: int, g: int, b: int)
    ensures ({
        let c = color_rgb(r, g, b);
        c.a == 1000 && c.r == r && c.g == g && c.b == b
    }),
{
}

/// **Theorem 3**: `gray` produces equal R, G, B components.
proof fn color_gray_components_equal(value: int)
    ensures ({
        let c = color_gray(value);
        c.r == value && c.g == value && c.b == value && c.r == c.g && c.g == c.b
    }),
{
}

/// **Theorem 4**: `gray` always has alpha = 1000.
proof fn color_gray_opaque(value: int)
    ensures
        color_gray(value).a == 1000,
{
}

// =============================================================================
// ALPHA OPERATION PROOFS
// =============================================================================

/// **Theorem 5**: `with_alpha` preserves RGB components.
proof fn color_with_alpha_preserves_rgb(c: SpecColor, alpha: int)
    ensures ({
        let result = color_with_alpha(c, alpha);
        result.r == c.r && result.g == c.g && result.b == c.b && result.a == alpha
    }),
{
}

/// **Theorem 6**: `fade(1000)` preserves alpha (fade by 1.0).
proof fn color_fade_one_preserves(c: SpecColor)
    ensures ({
        let result = color_fade(c, 1000);
        result.r == c.r && result.g == c.g && result.b == c.b
        && result.a == c.a * 1000 / 1000
    }),
{
}

/// **Theorem 7**: `fade(0)` produces zero alpha.
proof fn color_fade_zero(c: SpecColor)
    ensures ({
        let result = color_fade(c, 0);
        result.a == 0 && result.r == c.r && result.g == c.g && result.b == c.b
    }),
{
}

/// **Theorem 8**: `fade` preserves RGB components regardless of factor.
proof fn color_fade_preserves_rgb(c: SpecColor, factor: int)
    ensures ({
        let result = color_fade(c, factor);
        result.r == c.r && result.g == c.g && result.b == c.b
    }),
{
}

// =============================================================================
// INTERPOLATION PROOFS
// =============================================================================

/// **Theorem 9**: lerp of same color returns that color.
///
/// For any color c and parameter t: lerp(c, c, t) = c
proof fn color_lerp_same(c: SpecColor, t: int)
    ensures
        color_lerp(c, c, t) == c,
{
    // lerp(c, c, t).r = c.r + (c.r - c.r) * t / 1000 = c.r + 0 = c.r
    assert(c.r + (c.r - c.r) * t / 1000 == c.r);
    assert(c.g + (c.g - c.g) * t / 1000 == c.g);
    assert(c.b + (c.b - c.b) * t / 1000 == c.b);
    assert(c.a + (c.a - c.a) * t / 1000 == c.a);
}

/// **Theorem 10**: lerp at t=0 returns the first color.
///
/// For any colors a, b: lerp(a, b, 0) = a
proof fn color_lerp_zero(a: SpecColor, b: SpecColor)
    ensures
        color_lerp(a, b, 0) == a,
{
    assert(a.r + (b.r - a.r) * 0 / 1000 == a.r);
    assert(a.g + (b.g - a.g) * 0 / 1000 == a.g);
    assert(a.b + (b.b - a.b) * 0 / 1000 == a.b);
    assert(a.a + (b.a - a.a) * 0 / 1000 == a.a);
}

/// **Theorem 11**: lerp at t=1000 returns the second color.
///
/// For any colors a, b: lerp(a, b, 1000) = b
proof fn color_lerp_one(a: SpecColor, b: SpecColor)
    ensures
        color_lerp(a, b, 1000) == b,
{
    // lerp(a, b, 1000).r = a.r + (b.r - a.r) * 1000 / 1000
    //                     = a.r + (b.r - a.r) = b.r
    assert((b.r - a.r) * 1000 / 1000 == b.r - a.r);
    assert((b.g - a.g) * 1000 / 1000 == b.g - a.g);
    assert((b.b - a.b) * 1000 / 1000 == b.b - a.b);
    assert((b.a - a.a) * 1000 / 1000 == b.a - a.a);
}

// =============================================================================
// BLENDING PROOFS
// =============================================================================

/// **Theorem 12**: Blending opaque foreground covers background.
///
/// When src.a = 1000, blend_over returns src RGB (scaled).
proof fn color_blend_opaque_fg(src: SpecColor, dst: SpecColor)
    requires
        src.a == 1000,
    ensures ({
        let result = color_blend_over(src, dst);
        result.r == (src.r * 1000) / 1000
        && result.g == (src.g * 1000) / 1000
        && result.b == (src.b * 1000) / 1000
    }),
{
    // inv_alpha = 1000 - 1000 = 0
    // result.r = (src.r * 1000 + dst.r * 0) / 1000 = src.r * 1000 / 1000
    assert(1000 - src.a == 0);
}

/// **Theorem 13**: Blending transparent foreground shows background.
///
/// When src.a = 0, blend_over returns dst RGB.
proof fn color_blend_transparent_fg(src: SpecColor, dst: SpecColor)
    requires
        src.a == 0,
    ensures ({
        let result = color_blend_over(src, dst);
        result.r == dst.r && result.g == dst.g && result.b == dst.b
    }),
{
    // inv_alpha = 1000 - 0 = 1000
    // result.r = (src.r * 0 + dst.r * 1000) / 1000 = dst.r
    assert(1000 - src.a == 1000);
    assert(src.r * 0 == 0) by(nonlinear_arith);
    assert(src.g * 0 == 0) by(nonlinear_arith);
    assert(src.b * 0 == 0) by(nonlinear_arith);
}

// =============================================================================
// PREMULTIPLICATION PROOFS
// =============================================================================

/// **Theorem 14**: Premultiply with alpha=1000 preserves RGB.
proof fn color_premultiplied_full_alpha(c: SpecColor)
    requires
        c.a == 1000,
    ensures ({
        let result = color_premultiplied(c);
        result.r == c.r * 1000 / 1000
        && result.g == c.g * 1000 / 1000
        && result.b == c.b * 1000 / 1000
        && result.a == 1000
    }),
{
}

/// **Theorem 15**: Premultiply with alpha=0 zeroes RGB.
proof fn color_premultiplied_zero_alpha(c: SpecColor)
    requires
        c.a == 0,
    ensures ({
        let result = color_premultiplied(c);
        result.r == 0 && result.g == 0 && result.b == 0 && result.a == 0
    }),
{
    assert(c.r * 0 == 0) by(nonlinear_arith);
    assert(c.g * 0 == 0) by(nonlinear_arith);
    assert(c.b * 0 == 0) by(nonlinear_arith);
}

/// **Theorem 16**: Premultiply preserves alpha.
proof fn color_premultiplied_preserves_alpha(c: SpecColor)
    ensures
        color_premultiplied(c).a == c.a,
{
}

// =============================================================================
// CLAMPING PROOFS
// =============================================================================

/// **Theorem 17**: Clamping an in-range color is identity.
proof fn color_clamp_identity(c: SpecColor)
    requires
        0 <= c.r && c.r <= 1000,
        0 <= c.g && c.g <= 1000,
        0 <= c.b && c.b <= 1000,
        0 <= c.a && c.a <= 1000,
    ensures
        color_clamp(c) == c,
{
}

/// **Theorem 18**: Clamped components are always in [0, 1000].
proof fn color_clamp_bounds(c: SpecColor)
    ensures ({
        let result = color_clamp(c);
        0 <= result.r && result.r <= 1000
        && 0 <= result.g && result.g <= 1000
        && 0 <= result.b && result.b <= 1000
        && 0 <= result.a && result.a <= 1000
    }),
{
}

/// **Theorem 19**: Clamping is idempotent: clamp(clamp(c)) = clamp(c).
proof fn color_clamp_idempotent(c: SpecColor)
    ensures
        color_clamp(color_clamp(c)) == color_clamp(c),
{
    let cc = color_clamp(c);
    // cc components are in [0, 1000], so clamping again is identity
    assert(0 <= cc.r && cc.r <= 1000);
    assert(0 <= cc.g && cc.g <= 1000);
    assert(0 <= cc.b && cc.b <= 1000);
    assert(0 <= cc.a && cc.a <= 1000);
}

// =============================================================================
// LUMINANCE PROOFS
// =============================================================================

/// **Theorem 20**: Luminance of black is zero.
proof fn color_luminance_black()
    ensures
        color_luminance_scaled(color_black()) == 0,
{
}

/// **Theorem 21**: Luminance is non-negative for valid colors.
proof fn color_luminance_nonneg(c: SpecColor)
    requires
        c.r >= 0 && c.g >= 0 && c.b >= 0,
    ensures
        color_luminance_scaled(c) >= 0,
{
    assert(2126 * c.r >= 0) by(nonlinear_arith)
        requires c.r >= 0;
    assert(7152 * c.g >= 0) by(nonlinear_arith)
        requires c.g >= 0;
    assert(722 * c.b >= 0) by(nonlinear_arith)
        requires c.b >= 0;
}

/// **Theorem 22**: Gray colors have luminance proportional to value.
///
/// luminance(gray(v)) = (2126 + 7152 + 722) * v = 10000 * v
proof fn color_luminance_gray(v: int)
    ensures
        color_luminance_scaled(color_gray(v)) == 10000 * v,
{
    assert(2126 * v + 7152 * v + 722 * v == (2126 + 7152 + 722) * v) by(nonlinear_arith);
    assert(2126 + 7152 + 722 == 10000);
}

/// **Theorem 23**: White has maximum luminance (for unit range).
proof fn color_luminance_white()
    ensures
        color_luminance_scaled(color_white()) == 10000000,
{
    // 2126 * 1000 + 7152 * 1000 + 722 * 1000 = 10000 * 1000 = 10000000
}

// =============================================================================
// EXTENDED COLOR OPERATIONS
// =============================================================================

/// Invert a color: (1000 - r, 1000 - g, 1000 - b, a).
pub open spec fn color_invert(c: SpecColor) -> SpecColor {
    SpecColor {
        r: 1000 - c.r,
        g: 1000 - c.g,
        b: 1000 - c.b,
        a: c.a,
    }
}

/// Mix two colors equally: (a + b) / 2 per component.
pub open spec fn color_mix(a: SpecColor, b: SpecColor) -> SpecColor {
    SpecColor {
        r: (a.r + b.r) / 2,
        g: (a.g + b.g) / 2,
        b: (a.b + b.b) / 2,
        a: (a.a + b.a) / 2,
    }
}

/// Whether a color is "light" (luminance > 5000000, i.e., > 50% of white's luminance).
pub open spec fn color_is_light(c: SpecColor) -> bool {
    color_luminance_scaled(c) > 5000000
}

/// Whether a color is "dark" (luminance <= 5000000).
pub open spec fn color_is_dark(c: SpecColor) -> bool {
    color_luminance_scaled(c) <= 5000000
}

/// Component-wise addition of two colors.
pub open spec fn color_add(a: SpecColor, b: SpecColor) -> SpecColor {
    SpecColor {
        r: a.r + b.r,
        g: a.g + b.g,
        b: a.b + b.b,
        a: a.a + b.a,
    }
}

/// Scale all components by a factor (scaled arithmetic: s is in [0, 1000]).
pub open spec fn color_scale(c: SpecColor, s: int) -> SpecColor {
    SpecColor {
        r: c.r * s / 1000,
        g: c.g * s / 1000,
        b: c.b * s / 1000,
        a: c.a * s / 1000,
    }
}

// =============================================================================
// INVERT PROOFS
// =============================================================================

/// **Theorem 24**: Double inversion is identity (for valid colors).
///
/// For colors in [0, 1000]: invert(invert(c)) = c.
proof fn color_invert_involution(c: SpecColor)
    ensures
        color_invert(color_invert(c)) == c,
{
    // invert(c) = (1000 - c.r, 1000 - c.g, 1000 - c.b, c.a)
    // invert(invert(c)) = (1000 - (1000 - c.r), ...) = (c.r, c.g, c.b, c.a) = c
}

/// **Theorem 25**: Inversion preserves alpha.
proof fn color_invert_preserves_alpha(c: SpecColor)
    ensures
        color_invert(c).a == c.a,
{
}

/// **Theorem 26**: Inversion of black is white.
proof fn color_invert_black_is_white()
    ensures
        color_invert(color_black()) == color_white(),
{
}

/// **Theorem 27**: Inversion of white is black.
proof fn color_invert_white_is_black()
    ensures
        color_invert(color_white()) == color_black(),
{
}

// =============================================================================
// MIX PROOFS
// =============================================================================

/// **Theorem 28**: Mix is commutative.
proof fn color_mix_commutative(a: SpecColor, b: SpecColor)
    ensures
        color_mix(a, b) == color_mix(b, a),
{
    // (a.r + b.r) / 2 == (b.r + a.r) / 2
    assert(a.r + b.r == b.r + a.r);
    assert(a.g + b.g == b.g + a.g);
    assert(a.b + b.b == b.b + a.b);
    assert(a.a + b.a == b.a + a.a);
}

/// **Theorem 29**: Mix of same color is identity.
proof fn color_mix_same(c: SpecColor)
    ensures
        color_mix(c, c) == c,
{
    // (c.r + c.r) / 2 = 2*c.r / 2 = c.r
    assert((c.r + c.r) / 2 == c.r);
    assert((c.g + c.g) / 2 == c.g);
    assert((c.b + c.b) / 2 == c.b);
    assert((c.a + c.a) / 2 == c.a);
}

// =============================================================================
// IS_LIGHT / IS_DARK PROOFS
// =============================================================================

/// **Theorem 30**: is_light and is_dark are complementary.
proof fn color_light_dark_complement(c: SpecColor)
    ensures
        color_is_light(c) != color_is_dark(c)
        || (color_luminance_scaled(c) == 5000000 && color_is_dark(c) && !color_is_light(c)),
{
    // Light: luminance > 5000000
    // Dark: luminance <= 5000000
    // They are complementary except at exactly 5000000 (where dark = true, light = false)
}

/// **Theorem 31**: White is light.
proof fn color_white_is_light()
    ensures
        color_is_light(color_white()),
{
    // luminance(white) = 10000000 > 5000000
}

/// **Theorem 32**: Black is dark.
proof fn color_black_is_dark()
    ensures
        color_is_dark(color_black()),
{
    // luminance(black) = 0 <= 5000000
}

// =============================================================================
// COLOR ADDITION PROOFS
// =============================================================================

/// **Theorem 33**: Color addition is commutative.
proof fn color_add_commutative(a: SpecColor, b: SpecColor)
    ensures
        color_add(a, b) == color_add(b, a),
{
}

/// **Theorem 34**: Adding transparent (0,0,0,0) is identity.
proof fn color_add_transparent_identity(c: SpecColor)
    ensures
        color_add(c, color_transparent()) == c,
{
}

/// **Theorem 35**: Color addition is associative.
proof fn color_add_associative(a: SpecColor, b: SpecColor, c: SpecColor)
    ensures
        color_add(color_add(a, b), c) == color_add(a, color_add(b, c)),
{
}

// =============================================================================
// COLOR SCALE PROOFS (Theorems 36-39)
// =============================================================================

/// **Theorem 36**: Scaling by 0 produces zero-RGB (alpha also zeroed).
proof fn color_scale_zero(c: SpecColor)
    ensures ({
        let s = color_scale(c, 0);
        s.r == 0 && s.g == 0 && s.b == 0 && s.a == 0
    }),
{
    assert(c.r * 0 == 0) by(nonlinear_arith);
    assert(c.g * 0 == 0) by(nonlinear_arith);
    assert(c.b * 0 == 0) by(nonlinear_arith);
    assert(c.a * 0 == 0) by(nonlinear_arith);
}

/// **Theorem 37**: Scaling by 1000 (= 1.0) is identity.
proof fn color_scale_full(c: SpecColor)
    ensures
        color_scale(c, 1000) == c,
{
    assert(c.r * 1000 / 1000 == c.r) by(nonlinear_arith);
    assert(c.g * 1000 / 1000 == c.g) by(nonlinear_arith);
    assert(c.b * 1000 / 1000 == c.b) by(nonlinear_arith);
    assert(c.a * 1000 / 1000 == c.a) by(nonlinear_arith);
}

/// **Theorem 38**: Scaling transparent produces transparent.
proof fn color_scale_transparent(s: int)
    ensures
        color_scale(color_transparent(), s) == color_transparent(),
{
    assert(0 * s == 0) by(nonlinear_arith);
}

/// **Theorem 39**: Scale preserves zero components.
proof fn color_scale_preserves_zero(c: SpecColor, s: int)
    ensures
        c.r == 0 ==> color_scale(c, s).r == 0,
        c.g == 0 ==> color_scale(c, s).g == 0,
        c.b == 0 ==> color_scale(c, s).b == 0,
{
    assert(0 * s == 0) by(nonlinear_arith);
}

// =============================================================================
// LUMINANCE ORDERING PROOFS (Theorems 40-42)
// =============================================================================

/// **Theorem 40**: Gray luminance is monotone: if v1 <= v2, then luminance(gray(v1)) <= luminance(gray(v2)).
proof fn color_luminance_gray_monotone(v1: int, v2: int)
    requires
        v1 <= v2 && v1 >= 0 && v2 >= 0,
    ensures
        color_luminance_scaled(color_gray(v1)) <= color_luminance_scaled(color_gray(v2)),
{
    // luminance(gray(v)) = 10000 * v
    assert(2126 * v1 + 7152 * v1 + 722 * v1 == 10000 * v1) by(nonlinear_arith);
    assert(2126 * v2 + 7152 * v2 + 722 * v2 == 10000 * v2) by(nonlinear_arith);
    assert(10000 * v1 <= 10000 * v2) by(nonlinear_arith)
        requires v1 <= v2, v1 >= 0, v2 >= 0;
}

/// **Theorem 41**: Luminance of a color is bounded by its max component.
proof fn color_luminance_bounded(c: SpecColor)
    requires
        c.r >= 0 && c.g >= 0 && c.b >= 0,
    ensures ({
        let max_comp = if c.r >= c.g && c.r >= c.b { c.r }
                       else if c.g >= c.b { c.g }
                       else { c.b };
        color_luminance_scaled(c) <= 10000 * max_comp
    }),
{
    // luminance = 2126*r + 7152*g + 722*b <= (2126+7152+722)*max = 10000*max
    let max_comp = if c.r >= c.g && c.r >= c.b { c.r }
                   else if c.g >= c.b { c.g }
                   else { c.b };
    assert(2126 * c.r <= 2126 * max_comp) by(nonlinear_arith)
        requires c.r >= 0, c.r <= max_comp, max_comp >= 0;
    assert(7152 * c.g <= 7152 * max_comp) by(nonlinear_arith)
        requires c.g >= 0, c.g <= max_comp, max_comp >= 0;
    assert(722 * c.b <= 722 * max_comp) by(nonlinear_arith)
        requires c.b >= 0, c.b <= max_comp, max_comp >= 0;
    assert(2126 + 7152 + 722 == 10000);
}

/// **Theorem 42**: Green contributes most to luminance (Rec. 709 property).
proof fn color_green_dominates_luminance()
    ensures
        7152 > 2126 && 7152 > 722,
{
}

// =============================================================================
// MIX WITH CONSTANTS PROOFS (Theorems 43-45)
// =============================================================================

/// **Theorem 43**: Mix with self is identity.
proof fn color_mix_identity(c: SpecColor)
    ensures
        color_mix(c, c) == c,
{
    color_mix_same(c);
}

/// **Theorem 44**: Inversion and luminance: invert flips light/dark.
proof fn color_invert_luminance(c: SpecColor)
    requires
        c.r >= 0 && c.r <= 1000 && c.g >= 0 && c.g <= 1000 && c.b >= 0 && c.b <= 1000,
    ensures ({
        color_luminance_scaled(c) + color_luminance_scaled(color_invert(c)) == 10000000
    }),
{
    // lum(c) + lum(invert(c)) = 2126*r + 7152*g + 722*b + 2126*(1000-r) + 7152*(1000-g) + 722*(1000-b)
    // = 2126*1000 + 7152*1000 + 722*1000 = 10000*1000 = 10000000
    assert(2126 * c.r + 2126 * (1000 - c.r) == 2126 * 1000) by(nonlinear_arith);
    assert(7152 * c.g + 7152 * (1000 - c.g) == 7152 * 1000) by(nonlinear_arith);
    assert(722 * c.b + 722 * (1000 - c.b) == 722 * 1000) by(nonlinear_arith);
    assert(2126 * 1000 + 7152 * 1000 + 722 * 1000 == 10000000);
}

/// **Theorem 45**: Blend over with transparent constant is identity.
proof fn color_blend_transparent_constant_fg(dst: SpecColor)
    ensures
        color_blend_over(color_transparent(), dst) == dst,
{
    // src = (0,0,0,0), inv_alpha = 1000 - 0 = 1000
    // r = (0*0 + dst.r * 1000) / 1000 = dst.r
    assert(0 * 0 == 0) by(nonlinear_arith);
    assert(0 * 1000 == 0) by(nonlinear_arith);
    assert(dst.r * 1000 / 1000 == dst.r) by(nonlinear_arith);
    assert(dst.g * 1000 / 1000 == dst.g) by(nonlinear_arith);
    assert(dst.b * 1000 / 1000 == dst.b) by(nonlinear_arith);
    assert(dst.a * 1000 / 1000 == dst.a) by(nonlinear_arith);
}

// =============================================================================
// CONTRASTING COLOR OPERATIONS
// =============================================================================

/// Contrasting color: returns black for light colors, white for dark colors.
/// A color is "light" if its luminance > 5000000 (50% of white).
pub open spec fn color_contrasting(c: SpecColor) -> SpecColor {
    if color_is_light(c) {
        color_black()
    } else {
        color_white()
    }
}

/// Darken a color by a factor: rgb * (1000 - amount) / 1000.
pub open spec fn color_darken(c: SpecColor, amount: int) -> SpecColor {
    SpecColor {
        r: c.r * (1000 - amount) / 1000,
        g: c.g * (1000 - amount) / 1000,
        b: c.b * (1000 - amount) / 1000,
        a: c.a,
    }
}

/// Lighten a color by mixing toward white: c + (white - c) * amount / 1000.
pub open spec fn color_lighten(c: SpecColor, amount: int) -> SpecColor {
    SpecColor {
        r: c.r + (1000 - c.r) * amount / 1000,
        g: c.g + (1000 - c.g) * amount / 1000,
        b: c.b + (1000 - c.b) * amount / 1000,
        a: c.a,
    }
}

// =============================================================================
// CONTRASTING PROOFS
// =============================================================================

/// **Theorem 46**: Contrasting color of black is white.
///
/// Black has luminance 0 (dark), so contrasting returns white.
proof fn color_contrasting_black()
    ensures
        color_contrasting(color_black()) == color_white(),
{
    // luminance(black) = 0 <= 5000000, so is_dark = true, is_light = false
    // contrasting returns white for dark colors
}

/// **Theorem 47**: Contrasting color of white is black.
///
/// White has luminance 10000000 (light), so contrasting returns black.
proof fn color_contrasting_white()
    ensures
        color_contrasting(color_white()) == color_black(),
{
    // luminance(white) = 10000000 > 5000000, so is_light = true
    // contrasting returns black for light colors
}

/// **Theorem 48**: Contrasting always returns either black or white.
proof fn color_contrasting_binary(c: SpecColor)
    ensures
        color_contrasting(c) == color_black() || color_contrasting(c) == color_white(),
{
}

/// **Theorem 49**: Contrasting of contrasting black has high luminance contrast.
///
/// |luminance(black) - luminance(contrasting(black))| = 10000000.
proof fn color_contrasting_black_high_contrast()
    ensures ({
        let cb = color_contrasting(color_black());
        color_luminance_scaled(cb) == 10000000
    }),
{
    // contrasting(black) = white
    // luminance(white) = 10000000
}

/// **Theorem 50**: Contrasting of contrasting white has high luminance contrast.
///
/// |luminance(white) - luminance(contrasting(white))| = 10000000.
proof fn color_contrasting_white_high_contrast()
    ensures ({
        let cw = color_contrasting(color_white());
        color_luminance_scaled(cw) == 0
    }),
{
    // contrasting(white) = black
    // luminance(black) = 0
}

/// **Theorem 51**: Contrasting always has high contrast with the original.
///
/// For valid colors in [0, 1000]: the luminance difference between a color
/// and its contrasting partner is always >= 5000000 (50% of max).
proof fn color_contrasting_high_contrast(c: SpecColor)
    requires
        c.r >= 0 && c.r <= 1000 && c.g >= 0 && c.g <= 1000 && c.b >= 0 && c.b <= 1000,
    ensures ({
        let lum_c = color_luminance_scaled(c);
        let lum_cc = color_luminance_scaled(color_contrasting(c));
        // If c is light (lum > 5000000): cc = black (lum = 0), so diff = lum_c > 5000000
        // If c is dark (lum <= 5000000): cc = white (lum = 10000000), so diff = 10000000 - lum_c >= 5000000
        (lum_c > 5000000 ==> lum_cc == 0) &&
        (lum_c <= 5000000 ==> lum_cc == 10000000)
    }),
{
}

// =============================================================================
// DARKEN / LIGHTEN PROOFS
// =============================================================================

/// **Theorem 52**: Darken by 0 is identity.
proof fn color_darken_zero(c: SpecColor)
    ensures
        color_darken(c, 0) == c,
{
    assert(c.r * 1000 / 1000 == c.r) by(nonlinear_arith);
    assert(c.g * 1000 / 1000 == c.g) by(nonlinear_arith);
    assert(c.b * 1000 / 1000 == c.b) by(nonlinear_arith);
}

/// **Theorem 53**: Darken by 1000 (= 100%) produces black.
proof fn color_darken_full(c: SpecColor)
    ensures ({
        let d = color_darken(c, 1000);
        d.r == 0 && d.g == 0 && d.b == 0 && d.a == c.a
    }),
{
    assert(c.r * 0 == 0) by(nonlinear_arith);
    assert(c.g * 0 == 0) by(nonlinear_arith);
    assert(c.b * 0 == 0) by(nonlinear_arith);
}

/// **Theorem 54**: Darken preserves alpha.
proof fn color_darken_preserves_alpha(c: SpecColor, amount: int)
    ensures
        color_darken(c, amount).a == c.a,
{
}

/// **Theorem 55**: Lighten by 0 is identity.
proof fn color_lighten_zero(c: SpecColor)
    ensures
        color_lighten(c, 0) == c,
{
    assert((1000 - c.r) * 0 == 0) by(nonlinear_arith);
    assert((1000 - c.g) * 0 == 0) by(nonlinear_arith);
    assert((1000 - c.b) * 0 == 0) by(nonlinear_arith);
}

/// **Theorem 56**: Lighten by 1000 (= 100%) produces white (with original alpha).
proof fn color_lighten_full(c: SpecColor)
    ensures ({
        let l = color_lighten(c, 1000);
        l.r == c.r + (1000 - c.r) && l.g == c.g + (1000 - c.g)
        && l.b == c.b + (1000 - c.b) && l.a == c.a
    }),
{
    // lighten(c, 1000).r = c.r + (1000 - c.r) * 1000 / 1000 = c.r + (1000 - c.r)
    assert((1000 - c.r) * 1000 / 1000 == 1000 - c.r) by(nonlinear_arith);
    assert((1000 - c.g) * 1000 / 1000 == 1000 - c.g) by(nonlinear_arith);
    assert((1000 - c.b) * 1000 / 1000 == 1000 - c.b) by(nonlinear_arith);
}

/// **Theorem 57**: Lighten preserves alpha.
proof fn color_lighten_preserves_alpha(c: SpecColor, amount: int)
    ensures
        color_lighten(c, amount).a == c.a,
{
}

// =============================================================================
// CONTRAST PROOFS (luminance difference)
// =============================================================================

/// Contrast between two colors: absolute difference of luminance.
/// Scaled: contrast(a, b) = |luminance(a) - luminance(b)|.
pub open spec fn color_contrast(a: SpecColor, b: SpecColor) -> int {
    let la = color_luminance_scaled(a);
    let lb = color_luminance_scaled(b);
    if la >= lb { la - lb } else { lb - la }
}

/// **Theorem 58**: Contrast is symmetric.
proof fn color_contrast_symmetric(a: SpecColor, b: SpecColor)
    ensures
        color_contrast(a, b) == color_contrast(b, a),
{
}

/// **Theorem 59**: Contrast with self is zero.
proof fn color_contrast_self(c: SpecColor)
    ensures
        color_contrast(c, c) == 0int,
{
}

/// **Theorem 60**: Contrast is non-negative.
proof fn color_contrast_nonneg(a: SpecColor, b: SpecColor)
    ensures
        color_contrast(a, b) >= 0int,
{
}

// =============================================================================
// TO_RGBA / TO_RGB PROOFS
// =============================================================================

/// Spec: to_rgba returns a 4-tuple of components.
pub open spec fn color_to_rgba(c: SpecColor) -> (int, int, int, int) {
    (c.r, c.g, c.b, c.a)
}

/// Spec: to_rgb returns a 3-tuple of components.
pub open spec fn color_to_rgb(c: SpecColor) -> (int, int, int) {
    (c.r, c.g, c.b)
}

/// **Theorem 61**: to_rgba preserves all components.
proof fn color_to_rgba_components(c: SpecColor)
    ensures ({
        let t = color_to_rgba(c);
        t.0 == c.r && t.1 == c.g && t.2 == c.b && t.3 == c.a
    }),
{
}

/// **Theorem 62**: to_rgb preserves RGB components.
proof fn color_to_rgb_components(c: SpecColor)
    ensures ({
        let t = color_to_rgb(c);
        t.0 == c.r && t.1 == c.g && t.2 == c.b
    }),
{
}

/// **Theorem 63**: to_rgba roundtrip: creating from to_rgba output recreates original.
proof fn color_to_rgba_roundtrip(c: SpecColor)
    ensures ({
        let (r, g, b, a) = color_to_rgba(c);
        color_new(r, g, b, a) == c
    }),
{
}

/// **Theorem 64**: to_rgb roundtrip with alpha.
proof fn color_to_rgb_roundtrip(c: SpecColor)
    ensures ({
        let (r, g, b) = color_to_rgb(c);
        color_rgb(r, g, b) == SpecColor { r: c.r, g: c.g, b: c.b, a: 1000 }
    }),
{
}

fn main() {
    // Verification only
}

}
