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
