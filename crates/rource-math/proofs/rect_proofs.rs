// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! # Formal Verification of Rect Operations
//!
//! This module contains machine-checked proofs of correctness for Rect
//! and Bounds operations using the Verus formal verification tool.
//!
//! ## Verification Status
//!
//! All proofs in this file have been verified by Verus with zero admits.
//!
//! ## Properties Verified
//!
//! 1. **Containment Properties**
//!    - A rect contains its own center
//!    - contains_rect is reflexive (a rect contains itself)
//!    - contains_rect transitivity
//!
//! 2. **Intersection Properties**
//!    - intersects is symmetric
//!    - contains_rect implies intersects (for valid rects)
//!
//! 3. **Union Properties**
//!    - union is commutative
//!    - union contains both operands
//!
//! 4. **Transformation Properties**
//!    - translate preserves size
//!    - expand/shrink inverse
//!    - area is non-negative for valid rects
//!    - perimeter = 2*(width+height)
//!
//! ## Proof Methodology
//!
//! Rect operations are modeled over mathematical integers. All operations
//! (contains, intersects, union, expand, translate) use pure integer
//! arithmetic, so these proofs are exact with no floating-point limitations.
//!
//! ## Verification Command
//!
//! ```bash
//! /tmp/verus/verus crates/rource-math/proofs/rect_proofs.rs
//! ```

use vstd::prelude::*;

verus! {

// =============================================================================
// Rect Specification Type
// =============================================================================

/// Mathematical specification of a rectangle with position and size.
#[derive(PartialEq, Eq)]
pub struct SpecRect {
    pub x: int,
    pub y: int,
    pub width: int,
    pub height: int,
}

/// Mathematical specification of a 2D point.
#[derive(PartialEq, Eq)]
pub struct SpecPoint {
    pub x: int,
    pub y: int,
}

// =============================================================================
// Rect Operations (Spec Functions)
// =============================================================================

/// Creates a new rectangle.
pub open spec fn rect_new(x: int, y: int, width: int, height: int) -> SpecRect {
    SpecRect { x, y, width, height }
}

/// A zero-sized rectangle at the origin.
pub open spec fn rect_zero() -> SpecRect {
    SpecRect { x: 0, y: 0, width: 0, height: 0 }
}

/// Right edge: x + width.
pub open spec fn rect_right(r: SpecRect) -> int {
    r.x + r.width
}

/// Bottom edge: y + height.
pub open spec fn rect_bottom(r: SpecRect) -> int {
    r.y + r.height
}

/// Center x: x + width / 2 (integer division).
pub open spec fn rect_center_x(r: SpecRect) -> int {
    r.x + r.width / 2
}

/// Center y: y + height / 2 (integer division).
pub open spec fn rect_center_y(r: SpecRect) -> int {
    r.y + r.height / 2
}

/// Area: width * height.
pub open spec fn rect_area(r: SpecRect) -> int {
    r.width * r.height
}

/// Perimeter: 2 * (width + height).
pub open spec fn rect_perimeter(r: SpecRect) -> int {
    2 * (r.width + r.height)
}

/// A rect is valid if it has positive width and height.
pub open spec fn rect_is_valid(r: SpecRect) -> bool {
    r.width > 0 && r.height > 0
}

/// A rect is empty if width or height is <= 0.
pub open spec fn rect_is_empty(r: SpecRect) -> bool {
    r.width <= 0 || r.height <= 0
}

/// Point containment: x <= p.x <= x+width AND y <= p.y <= y+height.
pub open spec fn rect_contains(r: SpecRect, p: SpecPoint) -> bool {
    p.x >= r.x && p.x <= r.x + r.width
    && p.y >= r.y && p.y <= r.y + r.height
}

/// Rect containment: other is entirely within self.
pub open spec fn rect_contains_rect(outer: SpecRect, inner: SpecRect) -> bool {
    inner.x >= outer.x
    && inner.y >= outer.y
    && inner.x + inner.width <= outer.x + outer.width
    && inner.y + inner.height <= outer.y + outer.height
}

/// Rect intersection test (strict overlap, no edge touching).
pub open spec fn rect_intersects(a: SpecRect, b: SpecRect) -> bool {
    a.x < b.x + b.width
    && a.x + a.width > b.x
    && a.y < b.y + b.height
    && a.y + a.height > b.y
}

/// Integer min.
pub open spec fn min_int(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

/// Integer max.
pub open spec fn max_int(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

/// Union of two rects: smallest rect containing both.
pub open spec fn rect_union(a: SpecRect, b: SpecRect) -> SpecRect {
    let x = min_int(a.x, b.x);
    let y = min_int(a.y, b.y);
    let right = max_int(a.x + a.width, b.x + b.width);
    let bottom = max_int(a.y + a.height, b.y + b.height);
    SpecRect { x: x, y: y, width: right - x, height: bottom - y }
}

/// Expand a rect by amount on all sides.
pub open spec fn rect_expand(r: SpecRect, amount: int) -> SpecRect {
    SpecRect {
        x: r.x - amount,
        y: r.y - amount,
        width: r.width + 2 * amount,
        height: r.height + 2 * amount,
    }
}

/// Shrink a rect (expand by negative amount).
pub open spec fn rect_shrink(r: SpecRect, amount: int) -> SpecRect {
    rect_expand(r, -amount)
}

/// Translate a rect by offset.
pub open spec fn rect_translate(r: SpecRect, dx: int, dy: int) -> SpecRect {
    SpecRect { x: r.x + dx, y: r.y + dy, width: r.width, height: r.height }
}

// =============================================================================
// CONTAINMENT PROOFS
// =============================================================================

/// **Theorem 1**: A rect contains its top-left corner.
proof fn rect_contains_top_left(r: SpecRect)
    requires
        r.width >= 0 && r.height >= 0,
    ensures
        rect_contains(r, SpecPoint { x: r.x, y: r.y }),
{
}

/// **Theorem 2**: A rect contains its bottom-right corner.
proof fn rect_contains_bottom_right(r: SpecRect)
    requires
        r.width >= 0 && r.height >= 0,
    ensures
        rect_contains(r, SpecPoint { x: r.x + r.width, y: r.y + r.height }),
{
}

/// **Theorem 3**: A valid rect contains its center (integer division).
proof fn rect_contains_center(r: SpecRect)
    requires
        r.width >= 0 && r.height >= 0,
    ensures
        rect_contains(r, SpecPoint { x: rect_center_x(r), y: rect_center_y(r) }),
{
    // center_x = x + width/2, and x <= x + width/2 <= x + width
    assert(r.width / 2 >= 0);
    assert(r.width / 2 <= r.width);
    assert(r.height / 2 >= 0);
    assert(r.height / 2 <= r.height);
}

/// **Theorem 4**: contains_rect is reflexive (a rect contains itself).
proof fn rect_contains_rect_reflexive(r: SpecRect)
    ensures
        rect_contains_rect(r, r),
{
}

/// **Theorem 5**: contains_rect is transitive.
proof fn rect_contains_rect_transitive(a: SpecRect, b: SpecRect, c: SpecRect)
    requires
        rect_contains_rect(a, b) && rect_contains_rect(b, c),
    ensures
        rect_contains_rect(a, c),
{
}

// =============================================================================
// INTERSECTION PROOFS
// =============================================================================

/// **Theorem 6**: intersects is symmetric.
proof fn rect_intersects_symmetric(a: SpecRect, b: SpecRect)
    ensures
        rect_intersects(a, b) == rect_intersects(b, a),
{
}

/// **Theorem 7**: A valid rect intersects itself.
proof fn rect_intersects_self(r: SpecRect)
    requires
        rect_is_valid(r),
    ensures
        rect_intersects(r, r),
{
}

/// **Theorem 8**: If a valid rect contains another valid rect, they intersect.
proof fn rect_contains_implies_intersects(a: SpecRect, b: SpecRect)
    requires
        rect_contains_rect(a, b) && rect_is_valid(b),
    ensures
        rect_intersects(a, b),
{
    // From contains_rect: b.x >= a.x, b.x + b.width <= a.x + a.width
    // From is_valid: b.width > 0, b.height > 0
    // Need: a.x < b.x + b.width -- true since b.x >= a.x and b.width > 0
    //       a.x + a.width > b.x -- true since a.x + a.width >= b.x + b.width > b.x
    assert(b.width > 0);
    assert(b.height > 0);
}

// =============================================================================
// UNION PROOFS
// =============================================================================

/// **Theorem 9**: Union is commutative.
proof fn rect_union_commutative(a: SpecRect, b: SpecRect)
    ensures
        rect_union(a, b) == rect_union(b, a),
{
    // min(a.x, b.x) == min(b.x, a.x)
    assert(min_int(a.x, b.x) == min_int(b.x, a.x));
    assert(min_int(a.y, b.y) == min_int(b.y, a.y));
    assert(max_int(a.x + a.width, b.x + b.width) == max_int(b.x + b.width, a.x + a.width));
    assert(max_int(a.y + a.height, b.y + b.height) == max_int(b.y + b.height, a.y + a.height));
}

/// **Theorem 10**: Union contains the first rect.
proof fn rect_union_contains_first(a: SpecRect, b: SpecRect)
    ensures
        rect_contains_rect(rect_union(a, b), a),
{
    let u = rect_union(a, b);
    // u.x = min(a.x, b.x) <= a.x
    assert(u.x <= a.x);
    assert(u.y <= a.y);
    // u.x + u.width = max(a.right, b.right) >= a.right = a.x + a.width
    assert(u.x + u.width >= a.x + a.width);
    assert(u.y + u.height >= a.y + a.height);
}

/// **Theorem 11**: Union contains the second rect.
proof fn rect_union_contains_second(a: SpecRect, b: SpecRect)
    ensures
        rect_contains_rect(rect_union(a, b), b),
{
    let u = rect_union(a, b);
    assert(u.x <= b.x);
    assert(u.y <= b.y);
    assert(u.x + u.width >= b.x + b.width);
    assert(u.y + u.height >= b.y + b.height);
}

// =============================================================================
// TRANSFORMATION PROOFS
// =============================================================================

/// **Theorem 12**: Translate preserves width and height.
proof fn rect_translate_preserves_size(r: SpecRect, dx: int, dy: int)
    ensures ({
        let t = rect_translate(r, dx, dy);
        t.width == r.width && t.height == r.height
    }),
{
}

/// **Theorem 13**: Translate identity (by 0,0) returns the same rect.
proof fn rect_translate_identity(r: SpecRect)
    ensures
        rect_translate(r, 0, 0) == r,
{
}

/// **Theorem 14**: Translate composition.
///
/// translate(translate(r, dx1, dy1), dx2, dy2) = translate(r, dx1+dx2, dy1+dy2)
proof fn rect_translate_compose(r: SpecRect, dx1: int, dy1: int, dx2: int, dy2: int)
    ensures
        rect_translate(rect_translate(r, dx1, dy1), dx2, dy2)
        == rect_translate(r, dx1 + dx2, dy1 + dy2),
{
}

/// **Theorem 15**: Expand then shrink by same amount is identity.
proof fn rect_expand_shrink_inverse(r: SpecRect, amount: int)
    ensures
        rect_expand(rect_shrink(r, amount), amount) == r,
{
    // shrink(r, amount) = expand(r, -amount)
    // expand(expand(r, -amount), amount):
    //   x: (r.x - (-amount)) - amount = r.x + amount - amount = r.x
    //   width: (r.width + 2*(-amount)) + 2*amount = r.width
    let s = rect_shrink(r, amount);
    assert(s.x == r.x + amount);
    assert(s.y == r.y + amount);
    assert(s.width == r.width + 2 * (-amount));
    assert(s.height == r.height + 2 * (-amount));
    let e = rect_expand(s, amount);
    assert(e.x == s.x - amount);
    assert(e.y == s.y - amount);
    assert(e.width == s.width + 2 * amount);
    assert(e.height == s.height + 2 * amount);
}

/// **Theorem 16**: Shrink then expand by same amount is identity.
proof fn rect_shrink_expand_inverse(r: SpecRect, amount: int)
    ensures
        rect_shrink(rect_expand(r, amount), amount) == r,
{
    let e = rect_expand(r, amount);
    let s = rect_shrink(e, amount);
    assert(s.x == e.x + amount);
    assert(s.y == e.y + amount);
}

// =============================================================================
// AREA AND PERIMETER PROOFS
// =============================================================================

/// **Theorem 17**: Area is non-negative for valid rects.
proof fn rect_area_nonneg(r: SpecRect)
    requires
        r.width >= 0 && r.height >= 0,
    ensures
        rect_area(r) >= 0,
{
    assert(r.width * r.height >= 0) by(nonlinear_arith)
        requires r.width >= 0 && r.height >= 0;
}

/// **Theorem 18**: Perimeter is non-negative for valid rects.
proof fn rect_perimeter_nonneg(r: SpecRect)
    requires
        r.width >= 0 && r.height >= 0,
    ensures
        rect_perimeter(r) >= 0,
{
    assert(r.width + r.height >= 0);
    assert(2 * (r.width + r.height) >= 0) by(nonlinear_arith)
        requires r.width + r.height >= 0;
}

/// **Theorem 19**: Perimeter of a square is 4 * side length.
proof fn rect_square_perimeter(side: int)
    requires
        side >= 0,
    ensures
        rect_perimeter(rect_new(0, 0, side, side)) == 4 * side,
{
    assert(2 * (side + side) == 4 * side) by(nonlinear_arith);
}

/// **Theorem 20**: Area of a square is side * side.
proof fn rect_square_area(side: int)
    ensures
        rect_area(rect_new(0, 0, side, side)) == side * side,
{
}

// =============================================================================
// VALIDITY PROOFS
// =============================================================================

/// **Theorem 21**: is_valid and is_empty are complementary for typical rects.
proof fn rect_valid_empty_complement(r: SpecRect)
    ensures
        rect_is_valid(r) ==> !rect_is_empty(r),
{
}

/// **Theorem 22**: A rect with zero area is empty.
proof fn rect_zero_area_is_empty()
    ensures
        rect_is_empty(rect_zero()),
{
}

/// **Theorem 23**: Expand with positive amount preserves validity.
proof fn rect_expand_preserves_validity(r: SpecRect, amount: int)
    requires
        rect_is_valid(r) && amount >= 0,
    ensures
        rect_is_valid(rect_expand(r, amount)),
{
    let e = rect_expand(r, amount);
    assert(e.width == r.width + 2 * amount);
    assert(e.height == r.height + 2 * amount);
    assert(e.width > 0);
    assert(e.height > 0);
}

// =============================================================================
// EXTENDED RECT OPERATIONS
// =============================================================================

/// Compute the intersection rectangle (may be empty).
pub open spec fn rect_intersection(a: SpecRect, b: SpecRect) -> SpecRect {
    let x = max_int(a.x, b.x);
    let y = max_int(a.y, b.y);
    let right = min_int(a.x + a.width, b.x + b.width);
    let bottom = min_int(a.y + a.height, b.y + b.height);
    SpecRect {
        x: x,
        y: y,
        width: if right > x { right - x } else { 0 },
        height: if bottom > y { bottom - y } else { 0 },
    }
}

/// Create a rectangle from center point and dimensions.
pub open spec fn rect_from_center(cx: int, cy: int, width: int, height: int) -> SpecRect {
    SpecRect {
        x: cx - width / 2,
        y: cy - height / 2,
        width: width,
        height: height,
    }
}

/// Scale a rectangle's dimensions by a factor (width and height only).
pub open spec fn rect_scale(r: SpecRect, factor: int) -> SpecRect {
    SpecRect {
        x: r.x,
        y: r.y,
        width: r.width * factor,
        height: r.height * factor,
    }
}

// =============================================================================
// INTERSECTION PROOFS
// =============================================================================

/// **Theorem 24**: Intersection is commutative.
proof fn rect_intersection_commutative(a: SpecRect, b: SpecRect)
    ensures
        rect_intersection(a, b) == rect_intersection(b, a),
{
    assert(max_int(a.x, b.x) == max_int(b.x, a.x));
    assert(max_int(a.y, b.y) == max_int(b.y, a.y));
    assert(min_int(a.x + a.width, b.x + b.width) == min_int(b.x + b.width, a.x + a.width));
    assert(min_int(a.y + a.height, b.y + b.height) == min_int(b.y + b.height, a.y + a.height));
}

/// **Theorem 25**: Intersection of a rect with itself is itself.
proof fn rect_intersection_self(r: SpecRect)
    requires
        r.width >= 0 && r.height >= 0,
    ensures
        rect_intersection(r, r) == r,
{
    assert(max_int(r.x, r.x) == r.x);
    assert(max_int(r.y, r.y) == r.y);
    assert(min_int(r.x + r.width, r.x + r.width) == r.x + r.width);
    assert(min_int(r.y + r.height, r.y + r.height) == r.y + r.height);
}

/// **Theorem 26**: Intersection has non-negative width and height.
proof fn rect_intersection_nonneg(a: SpecRect, b: SpecRect)
    ensures ({
        let i = rect_intersection(a, b);
        i.width >= 0 && i.height >= 0
    }),
{
}

/// **Theorem 27**: If intersection is non-empty, it is contained in both operands.
proof fn rect_intersection_contained(a: SpecRect, b: SpecRect)
    requires ({
        let i = rect_intersection(a, b);
        i.width > 0 && i.height > 0
    }),
    ensures
        rect_contains_rect(a, rect_intersection(a, b)),
        rect_contains_rect(b, rect_intersection(a, b)),
{
    let i = rect_intersection(a, b);
    // i.x = max(a.x, b.x) >= a.x and >= b.x
    // i.x + i.width <= min(a.right, b.right) <= a.right and <= b.right
}

// =============================================================================
// FROM_CENTER PROOFS
// =============================================================================

/// **Theorem 28**: from_center produces a rect with the given dimensions.
proof fn rect_from_center_dimensions(cx: int, cy: int, w: int, h: int)
    ensures ({
        let r = rect_from_center(cx, cy, w, h);
        r.width == w && r.height == h
    }),
{
}

/// **Theorem 29**: from_center center_x is within 1 of input cx (integer division rounding).
proof fn rect_from_center_x_near(cx: int, w: int)
    requires
        w >= 0,
    ensures ({
        let r = rect_from_center(cx, 0, w, 0);
        // center_x = x + w/2 = (cx - w/2) + w/2 = cx
        rect_center_x(r) == cx
    }),
{
    // r.x = cx - w/2
    // center_x(r) = r.x + w/2 = (cx - w/2) + w/2 = cx
}

// =============================================================================
// SCALE PROOFS
// =============================================================================

/// **Theorem 30**: Scaling by 1 is identity.
proof fn rect_scale_identity(r: SpecRect)
    ensures
        rect_scale(r, 1) == r,
{
    assert(r.width * 1 == r.width) by(nonlinear_arith);
    assert(r.height * 1 == r.height) by(nonlinear_arith);
}

/// **Theorem 31**: Scaling preserves position.
proof fn rect_scale_preserves_position(r: SpecRect, factor: int)
    ensures ({
        let s = rect_scale(r, factor);
        s.x == r.x && s.y == r.y
    }),
{
}

/// **Theorem 32**: Area after scaling by factor is factor² × original area.
proof fn rect_scale_area(r: SpecRect, factor: int)
    ensures
        rect_area(rect_scale(r, factor)) == factor * factor * rect_area(r),
{
    // scaled.width * scaled.height = (r.width * factor) * (r.height * factor)
    //                                = r.width * r.height * factor * factor
    assert((r.width * factor) * (r.height * factor) == factor * factor * (r.width * r.height))
        by(nonlinear_arith);
}

/// **Theorem 33**: Scaling by 0 produces zero area.
proof fn rect_scale_zero_area(r: SpecRect)
    ensures
        rect_area(rect_scale(r, 0)) == 0,
{
    assert(r.width * 0 == 0) by(nonlinear_arith);
    assert(r.height * 0 == 0) by(nonlinear_arith);
}

fn main() {
    // Verification only
}

}
