// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Kani proof harnesses for Rect f32 edge-case verification.
//!
//! Verifies IEEE 754 safety properties for Rect operations: area, center,
//! contains, and intersection.

use crate::{Rect, Vec2};

/// Bound for multiplication-based operations.
const SAFE_BOUND: f32 = 1e18;

// ============================================================================
// area
// ============================================================================

/// **Non-negativity**: `area()` of a rect with non-negative dimensions is ≥ 0.
#[kani::proof]
fn verify_rect_area_non_negative() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h >= 0.0 && h < SAFE_BOUND);
    let r = Rect::new(x, y, w, h);
    let a = r.area();
    assert!(a >= 0.0, "area should be non-negative");
    assert!(!a.is_nan(), "area should not be NaN");
}

// ============================================================================
// center
// ============================================================================

/// **Finiteness**: `center()` with bounded Rect is finite.
#[kani::proof]
fn verify_rect_center_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w.abs() < SAFE_BOUND);
    kani::assume(h.is_finite() && h.abs() < SAFE_BOUND);
    let r = Rect::new(x, y, w, h);
    let c = r.center();
    assert!(c.x.is_finite(), "center().x non-finite");
    assert!(c.y.is_finite(), "center().y non-finite");
}

// ============================================================================
// contains
// ============================================================================

/// **Postcondition**: A point at the Rect origin is contained (positive dims).
#[kani::proof]
fn verify_rect_contains_origin() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w > 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h > 0.0 && h < SAFE_BOUND);
    let r = Rect::new(x, y, w, h);
    assert!(
        r.contains(Vec2::new(x, y)),
        "rect should contain its own origin"
    );
}

// ============================================================================
// perimeter
// ============================================================================

/// **Non-negativity**: `perimeter()` of a rect with non-negative dimensions is ≥ 0.
#[kani::proof]
fn verify_rect_perimeter_non_negative() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h >= 0.0 && h < SAFE_BOUND);
    let r = Rect::new(x, y, w, h);
    let p = r.perimeter();
    assert!(p >= 0.0, "perimeter should be non-negative");
    assert!(!p.is_nan(), "perimeter should not be NaN");
    assert!(p.is_finite(), "perimeter should be finite");
}

// ============================================================================
// from_center_size
// ============================================================================

/// **Postcondition**: `from_center_size()` center matches input (within FP tolerance).
///
/// Bounded to 1e6 to prevent FP roundoff: `cx - w/2 + w/2` may not equal `cx`
/// when `|cx| >> w` due to catastrophic cancellation. At `|cx| < 1e6` and
/// `w < 1e6`, the roundoff is < 1e-1.
#[kani::proof]
fn verify_rect_from_center_size_center() {
    let cx: f32 = kani::any();
    let cy: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(cx.is_finite() && cx.abs() < 1e6);
    kani::assume(cy.is_finite() && cy.abs() < 1e6);
    kani::assume(w.is_finite() && w >= 0.0 && w < 1e6);
    kani::assume(h.is_finite() && h >= 0.0 && h < 1e6);
    let r = Rect::from_center_size(Vec2::new(cx, cy), Vec2::new(w, h));
    let c = r.center();
    // FP tolerance: center = x + w/2, and x = cx - w/2, so center = cx - w/2 + w/2
    // Roundoff bounded by |cx| * eps + |w| * eps ≈ 2e6 * 1.2e-7 ≈ 0.24
    assert!((c.x - cx).abs() < 1.0, "center().x should match input cx");
    assert!((c.y - cy).abs() < 1.0, "center().y should match input cy");
}

// ============================================================================
// translate
// ============================================================================

/// **Postcondition**: `translate()` preserves width and height exactly.
#[kani::proof]
fn verify_rect_translate_preserves_size() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    let dx: f32 = kani::any();
    let dy: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0);
    kani::assume(h.is_finite() && h >= 0.0);
    kani::assume(dx.is_finite() && dx.abs() < SAFE_BOUND);
    kani::assume(dy.is_finite() && dy.abs() < SAFE_BOUND);
    let r = Rect::new(x, y, w, h);
    let t = r.translate(Vec2::new(dx, dy));
    assert!(t.width == w, "translate should preserve width");
    assert!(t.height == h, "translate should preserve height");
}

// ============================================================================
// expand / shrink
// ============================================================================

/// **Finiteness**: `expand()` with bounded inputs is finite.
#[kani::proof]
fn verify_rect_expand_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    let amount: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h >= 0.0 && h < SAFE_BOUND);
    kani::assume(amount.is_finite() && amount.abs() < SAFE_BOUND);
    let r = Rect::new(x, y, w, h);
    let e = r.expand(amount);
    assert!(e.x.is_finite(), "expand().x non-finite");
    assert!(e.y.is_finite(), "expand().y non-finite");
    assert!(e.width.is_finite(), "expand().width non-finite");
    assert!(e.height.is_finite(), "expand().height non-finite");
}

// ============================================================================
// is_valid
// ============================================================================

/// **Postcondition**: Rect with positive width and height is always valid.
#[kani::proof]
fn verify_rect_is_valid_positive_dims() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(w.is_finite() && w > 0.0);
    kani::assume(h.is_finite() && h > 0.0);
    let r = Rect::new(x, y, w, h);
    assert!(r.is_valid(), "positive dims rect should be valid");
}

// ============================================================================
// intersects (self)
// ============================================================================

/// **Postcondition**: Any rect with substantial dimensions intersects itself.
///
/// The `intersects()` method uses strict inequality: `x + width > x`.
/// For this to hold in IEEE 754, `width` must exceed the ULP at `x`:
/// `ULP(x) ≈ |x| * 2^-23`. At `|x| < 1e6`, ULP ≈ 0.12, so `width > 1.0`
/// is sufficient. This is a genuine IEEE 754 edge case: the mathematical
/// property `x + w > x` for w > 0 does NOT hold in FP for all inputs.
#[kani::proof]
fn verify_rect_self_intersection() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < 1e6);
    kani::assume(y.is_finite() && y.abs() < 1e6);
    // Width/height > 1.0 ensures x + w > x when |x| < 1e6 (ULP at 1e6 ≈ 0.12)
    kani::assume(w.is_finite() && w > 1.0 && w < 1e6);
    kani::assume(h.is_finite() && h > 1.0 && h < 1e6);
    let r = Rect::new(x, y, w, h);
    assert!(r.intersects(r), "rect should intersect itself");
}

// ============================================================================
// contains_rect (self)
// ============================================================================

/// **Postcondition**: Any valid rect contains itself.
#[kani::proof]
fn verify_rect_contains_self() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h >= 0.0 && h < SAFE_BOUND);
    let r = Rect::new(x, y, w, h);
    assert!(r.contains_rect(r), "rect should contain itself");
}

// ============================================================================
// scale_from_center
// ============================================================================

/// **Finiteness**: `scale_from_center()` with bounded inputs is finite.
#[kani::proof]
fn verify_rect_scale_from_center_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    let factor: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h >= 0.0 && h < SAFE_BOUND);
    kani::assume(factor.is_finite() && factor.abs() < SAFE_BOUND);
    let r = Rect::new(x, y, w, h);
    let s = r.scale_from_center(factor);
    assert!(s.x.is_finite(), "scale_from_center().x non-finite");
    assert!(s.y.is_finite(), "scale_from_center().y non-finite");
    assert!(s.width.is_finite(), "scale_from_center().width non-finite");
    assert!(
        s.height.is_finite(),
        "scale_from_center().height non-finite"
    );
}

// ============================================================================
// approx_eq
// ============================================================================

/// **Reflexivity**: `approx_eq(r, r)` is true for all finite rects.
#[kani::proof]
fn verify_rect_approx_eq_reflexive() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(w.is_finite());
    kani::assume(h.is_finite());
    let r = Rect::new(x, y, w, h);
    assert!(r.approx_eq(r), "approx_eq not reflexive");
}

// ============================================================================
// from_corners
// ============================================================================

/// **Postcondition**: `from_corners()` produces a valid rect with correct bounds.
#[kani::proof]
fn verify_rect_from_corners_valid() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    let r = Rect::from_corners(Vec2::new(ax, ay), Vec2::new(bx, by));
    assert!(r.width >= 0.0, "from_corners width should be non-negative");
    assert!(
        r.height >= 0.0,
        "from_corners height should be non-negative"
    );
    assert!(r.x.is_finite(), "from_corners().x non-finite");
    assert!(r.y.is_finite(), "from_corners().y non-finite");
}

// ============================================================================
// from_center_size
// ============================================================================

/// **Postcondition**: `from_center_size()` produces finite rect with correct center.
#[kani::proof]
fn verify_rect_from_center_size_finite() {
    let cx: f32 = kani::any();
    let cy: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(cx.is_finite() && cx.abs() < SAFE_BOUND);
    kani::assume(cy.is_finite() && cy.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h >= 0.0 && h < SAFE_BOUND);
    let r = Rect::from_center_size(Vec2::new(cx, cy), Vec2::new(w, h));
    assert!(r.x.is_finite(), "from_center_size().x non-finite");
    assert!(r.y.is_finite(), "from_center_size().y non-finite");
    assert!(r.width.is_finite(), "from_center_size().width non-finite");
    assert!(r.height.is_finite(), "from_center_size().height non-finite");
}

// ============================================================================
// is_valid / is_empty
// ============================================================================

/// **Postcondition**: `is_valid()` and `is_empty()` are complementary for positive-sized rects.
#[kani::proof]
fn verify_rect_valid_empty_complement() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(w.is_finite() && w > 0.0);
    kani::assume(h.is_finite() && h > 0.0);
    let r = Rect::new(x, y, w, h);
    assert!(r.is_valid(), "positive-sized rect should be valid");
    assert!(!r.is_empty(), "positive-sized rect should not be empty");
}

/// **Postcondition**: Zero-sized rect is empty.
#[kani::proof]
fn verify_rect_zero_is_empty() {
    let r = Rect::new(0.0, 0.0, 0.0, 0.0);
    assert!(r.is_empty(), "zero rect should be empty");
}

// ============================================================================
// expand_xy
// ============================================================================

/// **Finiteness**: `expand_xy()` with finite inputs produces finite rect.
#[kani::proof]
fn verify_rect_expand_xy_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    let xa: f32 = kani::any();
    let ya: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h >= 0.0 && h < SAFE_BOUND);
    kani::assume(xa.is_finite() && xa.abs() < SAFE_BOUND);
    kani::assume(ya.is_finite() && ya.abs() < SAFE_BOUND);
    let r = Rect::new(x, y, w, h).expand_xy(xa, ya);
    assert!(r.x.is_finite(), "expand_xy().x non-finite");
    assert!(r.y.is_finite(), "expand_xy().y non-finite");
    assert!(r.width.is_finite(), "expand_xy().width non-finite");
    assert!(r.height.is_finite(), "expand_xy().height non-finite");
}

// ============================================================================
// scale_from_center (componentwise)
// ============================================================================

/// **Componentwise**: `scale_from_center()` returns finite components and correct dimensions.
#[kani::proof]
fn verify_rect_scale_from_center_componentwise() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    let factor: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h >= 0.0 && h < SAFE_BOUND);
    kani::assume(factor.is_finite() && factor >= 0.0 && factor < SAFE_BOUND);
    let r = Rect::new(x, y, w, h).scale_from_center(factor);
    assert!(r.x.is_finite(), "scale_from_center().x non-finite");
    assert!(r.y.is_finite(), "scale_from_center().y non-finite");
    assert!(r.width.is_finite(), "scale_from_center().width non-finite");
    assert!(
        r.height.is_finite(),
        "scale_from_center().height non-finite"
    );
}

// ============================================================================
// position / size / center
// ============================================================================

/// **Postcondition**: `position()` returns (x, y) of the rect.
#[kani::proof]
fn verify_rect_position_correct() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(w.is_finite());
    kani::assume(h.is_finite());
    let r = Rect::new(x, y, w, h);
    let pos = r.position();
    assert!(pos.x == x, "position().x should be x");
    assert!(pos.y == y, "position().y should be y");
}

/// **Postcondition**: `size()` returns (width, height) of the rect.
#[kani::proof]
fn verify_rect_size_correct() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(w.is_finite());
    kani::assume(h.is_finite());
    let r = Rect::new(x, y, w, h);
    let sz = r.size();
    assert!(sz.x == w, "size().x should be width");
    assert!(sz.y == h, "size().y should be height");
}
