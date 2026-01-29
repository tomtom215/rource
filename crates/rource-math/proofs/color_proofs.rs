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
    assert(2126 * c.r >= 0) by(nonlinear_arith);
    assert(7152 * c.g >= 0) by(nonlinear_arith);
    assert(722 * c.b >= 0) by(nonlinear_arith);
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

fn main() {
    // Verification only
}

}
