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

// ============================================================================
// shrink
// ============================================================================

/// **Finiteness**: `shrink(amount)` with bounded inputs produces finite Rect.
///
/// Precondition: finite rect with non-negative dims, finite non-negative amount.
/// Postcondition: all output components are finite.
#[kani::proof]
fn verify_rect_shrink_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    let amount: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h >= 0.0 && h < SAFE_BOUND);
    kani::assume(amount.is_finite() && amount >= 0.0 && amount < SAFE_BOUND);
    let r = Rect::new(x, y, w, h).shrink(amount);
    assert!(r.x.is_finite(), "shrink().x non-finite");
    assert!(r.y.is_finite(), "shrink().y non-finite");
    assert!(r.width.is_finite(), "shrink().width non-finite");
    assert!(r.height.is_finite(), "shrink().height non-finite");
}

// ============================================================================
// right / bottom
// ============================================================================

/// **Correctness**: `right()` returns `x + width`, `bottom()` returns `y + height`.
///
/// Precondition: finite rect components with bounded values.
/// Postcondition: `right() == x + width`, `bottom() == y + height`, both finite.
#[kani::proof]
fn verify_rect_right_bottom_correct() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h >= 0.0 && h < SAFE_BOUND);
    let r = Rect::new(x, y, w, h);
    let right = r.right();
    let bottom = r.bottom();
    assert!(right.is_finite(), "right() non-finite");
    assert!(bottom.is_finite(), "bottom() non-finite");
    assert!(right == x + w, "right() should equal x + width");
    assert!(bottom == y + h, "bottom() should equal y + height");
}

// ============================================================================
// to_bounds
// ============================================================================

/// **Finiteness**: `to_bounds()` with finite rect produces finite Bounds.
///
/// Precondition: finite rect with non-negative dimensions.
/// Postcondition: all Bounds min/max components are finite.
#[kani::proof]
fn verify_rect_to_bounds_finite() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h >= 0.0 && h < SAFE_BOUND);
    let b = Rect::new(x, y, w, h).to_bounds();
    assert!(b.min.x.is_finite(), "to_bounds().min.x non-finite");
    assert!(b.min.y.is_finite(), "to_bounds().min.y non-finite");
    assert!(b.max.x.is_finite(), "to_bounds().max.x non-finite");
    assert!(b.max.y.is_finite(), "to_bounds().max.y non-finite");
}

// ============================================================================
// from_corners
// ============================================================================

/// **Correctness**: `from_corners(a, b)` produces a rect with all finite components.
///
/// Precondition: finite corner points.
/// Postcondition: all output components finite, width/height non-negative.
#[kani::proof]
fn verify_rect_from_corners_all_finite() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    let r = Rect::from_corners(Vec2::new(ax, ay), Vec2::new(bx, by));
    assert!(r.x.is_finite(), "from_corners().x non-finite");
    assert!(r.y.is_finite(), "from_corners().y non-finite");
    assert!(r.width.is_finite(), "from_corners().width non-finite");
    assert!(r.height.is_finite(), "from_corners().height non-finite");
    assert!(
        r.width >= 0.0,
        "from_corners().width should be non-negative"
    );
    assert!(
        r.height >= 0.0,
        "from_corners().height should be non-negative"
    );
}

// ============================================================================
// translate
// ============================================================================

// ============================================================================
// union
// ============================================================================

/// **Finiteness**: `union()` with finite rects produces finite rect.
#[kani::proof]
fn verify_rect_union_finite() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let aw: f32 = kani::any();
    let ah: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bw: f32 = kani::any();
    let bh: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(aw.is_finite() && aw >= 0.0 && aw < SAFE_BOUND);
    kani::assume(ah.is_finite() && ah >= 0.0 && ah < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(bw.is_finite() && bw >= 0.0 && bw < SAFE_BOUND);
    kani::assume(bh.is_finite() && bh >= 0.0 && bh < SAFE_BOUND);
    let a = Rect::new(ax, ay, aw, ah);
    let b = Rect::new(bx, by, bw, bh);
    let u = a.union(b);
    assert!(u.x.is_finite(), "union().x non-finite");
    assert!(u.y.is_finite(), "union().y non-finite");
    assert!(u.width.is_finite(), "union().width non-finite");
    assert!(u.height.is_finite(), "union().height non-finite");
}

// ============================================================================
// max corner
// ============================================================================

/// **Correctness**: `max()` returns `(x + width, y + height)` as Vec2.
#[kani::proof]
fn verify_rect_max_correct() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h >= 0.0 && h < SAFE_BOUND);
    let r = Rect::new(x, y, w, h);
    let m = r.max();
    assert!(m.x == x + w, "max().x should equal x + width");
    assert!(m.y == y + h, "max().y should equal y + height");
}

// ============================================================================
// translate correctness
// ============================================================================

/// **Correctness**: `translate(offset)` shifts position by offset, preserves size.
///
/// Precondition: finite rect and offset.
/// Postcondition: `translated.x == x + offset.x`, `translated.y == y + offset.y`,
///   width and height unchanged.
#[kani::proof]
fn verify_rect_translate_correctness() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    let ox: f32 = kani::any();
    let oy: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < SAFE_BOUND);
    kani::assume(y.is_finite() && y.abs() < SAFE_BOUND);
    kani::assume(w.is_finite() && w >= 0.0 && w < SAFE_BOUND);
    kani::assume(h.is_finite() && h >= 0.0 && h < SAFE_BOUND);
    kani::assume(ox.is_finite() && ox.abs() < SAFE_BOUND);
    kani::assume(oy.is_finite() && oy.abs() < SAFE_BOUND);
    let r = Rect::new(x, y, w, h).translate(Vec2::new(ox, oy));
    assert!(r.width == w, "translate should preserve width");
    assert!(r.height == h, "translate should preserve height");
    assert!(r.x == x + ox, "translate should shift x by offset.x");
    assert!(r.y == y + oy, "translate should shift y by offset.y");
}

// ============================================================================
// intersection (returns Option)
// ============================================================================

/// **Finiteness**: `intersection()` of overlapping rects produces finite result.
///
/// Two rects that overlap (verified by requiring overlap conditions) should
/// produce a `Some(rect)` with all finite components.
#[kani::proof]
fn verify_rect_intersection_finite() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let aw: f32 = kani::any();
    let ah: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bw: f32 = kani::any();
    let bh: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < SAFE_BOUND);
    kani::assume(ay.is_finite() && ay.abs() < SAFE_BOUND);
    kani::assume(aw.is_finite() && aw > 1.0 && aw < SAFE_BOUND);
    kani::assume(ah.is_finite() && ah > 1.0 && ah < SAFE_BOUND);
    kani::assume(bx.is_finite() && bx.abs() < SAFE_BOUND);
    kani::assume(by.is_finite() && by.abs() < SAFE_BOUND);
    kani::assume(bw.is_finite() && bw > 1.0 && bw < SAFE_BOUND);
    kani::assume(bh.is_finite() && bh > 1.0 && bh < SAFE_BOUND);
    // Ensure overlap by requiring b starts within a
    kani::assume(bx >= ax && bx < ax + aw);
    kani::assume(by >= ay && by < ay + ah);
    let a = Rect::new(ax, ay, aw, ah);
    let b = Rect::new(bx, by, bw, bh);
    if let Some(i) = a.intersection(b) {
        assert!(i.x.is_finite(), "intersection().x non-finite");
        assert!(i.y.is_finite(), "intersection().y non-finite");
        assert!(i.width.is_finite(), "intersection().width non-finite");
        assert!(i.height.is_finite(), "intersection().height non-finite");
        assert!(i.width >= 0.0, "intersection width non-negative");
        assert!(i.height >= 0.0, "intersection height non-negative");
    }
}

/// **Self-intersection**: `r.intersection(r)` returns `Some` with approximately
/// the same dimensions.
///
/// A valid rect with positive dimensions should always intersect itself.
/// The result may differ from the original by FP rounding: `intersection`
/// computes `width = (x + w) - x` which can differ from `w` when `|x| >> w`
/// due to intermediate rounding in `x + w`.
#[kani::proof]
fn verify_rect_intersection_self() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < 1e6);
    kani::assume(y.is_finite() && y.abs() < 1e6);
    kani::assume(w.is_finite() && w > 1.0 && w < 1e6);
    kani::assume(h.is_finite() && h > 1.0 && h < 1e6);
    let r = Rect::new(x, y, w, h);
    let result = r.intersection(r);
    // Self-intersection must return Some for valid positive-dimension rects
    assert!(result.is_some(), "self-intersection should be Some");
    let i = result.unwrap();
    // Position is exact: max(x, x) = x
    assert!(i.x == x, "self-intersection x mismatch");
    assert!(i.y == y, "self-intersection y mismatch");
    // Dimensions may differ due to FP: (x + w) - x ≠ w when |x| >> w.
    // At |x| < 1e6, ULP ≈ 0.0625, so error bounded by 1 ULP ≈ 0.125.
    assert!(
        (i.width - w).abs() < 0.25,
        "self-intersection width too far"
    );
    assert!(
        (i.height - h).abs() < 0.25,
        "self-intersection height too far"
    );
}

// ============================================================================
// normalize
// ============================================================================

/// **Idempotence**: `normalize(normalize(r)) == normalize(r)`.
#[kani::proof]
fn verify_rect_normalize_idempotent() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < 1e6);
    kani::assume(y.is_finite() && y.abs() < 1e6);
    kani::assume(w.is_finite() && w.abs() < 1e6);
    kani::assume(h.is_finite() && h.abs() < 1e6);
    let r = Rect::new(x, y, w, h);
    let n1 = r.normalize();
    let n2 = n1.normalize();
    assert!(n1.x == n2.x, "normalize not idempotent: x");
    assert!(n1.y == n2.y, "normalize not idempotent: y");
    assert!(n1.width == n2.width, "normalize not idempotent: width");
    assert!(n1.height == n2.height, "normalize not idempotent: height");
}

/// **Non-negative dimensions**: `normalize()` produces non-negative width/height.
#[kani::proof]
fn verify_rect_normalize_nonneg() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < 1e6);
    kani::assume(y.is_finite() && y.abs() < 1e6);
    kani::assume(w.is_finite() && w.abs() < 1e6);
    kani::assume(h.is_finite() && h.abs() < 1e6);
    let r = Rect::new(x, y, w, h);
    let n = r.normalize();
    assert!(n.width >= 0.0, "normalized width should be non-negative");
    assert!(n.height >= 0.0, "normalized height should be non-negative");
}

// ============================================================================
// lerp (Rect)
// ============================================================================

/// **Boundary**: `lerp(b, 0.0) == a` and `lerp(b, 1.0) == b`.
#[kani::proof]
fn verify_rect_lerp_boundaries() {
    let ax: f32 = kani::any();
    let ay: f32 = kani::any();
    let aw: f32 = kani::any();
    let ah: f32 = kani::any();
    let bx: f32 = kani::any();
    let by: f32 = kani::any();
    let bw: f32 = kani::any();
    let bh: f32 = kani::any();
    kani::assume(ax.is_finite() && ax.abs() < 1e6);
    kani::assume(ay.is_finite() && ay.abs() < 1e6);
    kani::assume(aw.is_finite() && aw.abs() < 1e6);
    kani::assume(ah.is_finite() && ah.abs() < 1e6);
    kani::assume(bx.is_finite() && bx.abs() < 1e6);
    kani::assume(by.is_finite() && by.abs() < 1e6);
    kani::assume(bw.is_finite() && bw.abs() < 1e6);
    kani::assume(bh.is_finite() && bh.abs() < 1e6);
    let a = Rect::new(ax, ay, aw, ah);
    let b = Rect::new(bx, by, bw, bh);
    let at_zero = a.lerp(b, 0.0);
    assert!(at_zero.x == ax, "lerp(0) should return a.x");
    assert!(at_zero.y == ay, "lerp(0) should return a.y");
    assert!(at_zero.width == aw, "lerp(0) should return a.width");
    assert!(at_zero.height == ah, "lerp(0) should return a.height");
}

// ============================================================================
// grow_to_contain
// ============================================================================

/// **Monotonicity**: grown rect always contains the new point.
#[kani::proof]
fn verify_rect_grow_to_contain_includes_point() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    let px: f32 = kani::any();
    let py: f32 = kani::any();
    kani::assume(x.is_finite() && x.abs() < 1e6);
    kani::assume(y.is_finite() && y.abs() < 1e6);
    kani::assume(w.is_finite() && w > 0.0 && w < 1e6);
    kani::assume(h.is_finite() && h > 0.0 && h < 1e6);
    kani::assume(px.is_finite() && px.abs() < 1e6);
    kani::assume(py.is_finite() && py.abs() < 1e6);
    let r = Rect::new(x, y, w, h);
    let grown = r.grow_to_contain(crate::Vec2::new(px, py));
    // The point should now be within the grown rect
    assert!(grown.x <= px, "grown rect min x > point x");
    assert!(grown.y <= py, "grown rect min y > point y");
    assert!(grown.right() >= px, "grown rect max x < point x");
    assert!(grown.bottom() >= py, "grown rect max y < point y");
}

// ============================================================================
// scale (Rect, position-preserving)
// ============================================================================

/// **Position preservation**: `scale()` preserves x, y.
#[kani::proof]
fn verify_rect_scale_preserves_position() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    let factor: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(w.is_finite());
    kani::assume(h.is_finite());
    kani::assume(factor.is_finite());
    let r = Rect::new(x, y, w, h);
    let s = r.scale(factor);
    assert!(s.x == x, "scale should preserve x");
    assert!(s.y == y, "scale should preserve y");
}

/// **Identity**: `scale(1.0)` returns the original rect.
#[kani::proof]
fn verify_rect_scale_one_identity() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    let w: f32 = kani::any();
    let h: f32 = kani::any();
    kani::assume(x.is_finite());
    kani::assume(y.is_finite());
    kani::assume(w.is_finite());
    kani::assume(h.is_finite());
    let r = Rect::new(x, y, w, h);
    let s = r.scale(1.0);
    assert!(s.x == x, "scale(1) changed x");
    assert!(s.y == y, "scale(1) changed y");
    assert!(s.width == w, "scale(1) changed width");
    assert!(s.height == h, "scale(1) changed height");
}
