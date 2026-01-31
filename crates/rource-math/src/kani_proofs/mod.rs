// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Kani proof harnesses for bit-precise f32/f64 verification.
//!
//! This module contains bounded model checking harnesses using Kani (CBMC)
//! to verify IEEE 754 floating-point edge-case safety properties that
//! algebraic proofs (Verus/Coq) cannot express.
//!
//! # Verification Tiers
//!
//! Each harness belongs to one of three verification tiers:
//!
//! - **Tier 1 (Safety)**: No assumptions on input — verifies the function
//!   does not panic or trigger undefined behavior for ANY f32 bit pattern,
//!   including NaN, ±infinity, subnormals, and ±0.
//!
//! - **Tier 2 (NaN-freedom)**: Assumes `is_finite()` inputs — verifies the
//!   function never produces NaN output from finite inputs. Infinity output
//!   is acceptable (overflow is defined behavior in IEEE 754).
//!
//! - **Tier 3 (Finiteness)**: Assumes bounded inputs (e.g., |x| < 1e18) —
//!   verifies the function produces finite output, proving absence of both
//!   NaN and overflow for realistic input ranges.
//!
//! # Architecture
//!
//! Kani operates via CBMC (C Bounded Model Checker) and symbolically
//! explores ALL 2^32 bit patterns for each `kani::any::<f32>()` call.
//! This provides exhaustive verification within the bounded domain,
//! complementing our Verus (475 proof functions) and Coq (1570 theorems)
//! algebraic proofs which verify mathematical identities but cannot
//! reason about IEEE 754 special values.
//!
//! # Harness Count (177 total)
//!
//! - Vec2: 21, Vec3: 23, Vec4: 22
//! - Mat3: 14, Mat4: 26
//! - Color: 24, Rect: 20, Bounds: 20, Utils: 7
//!
//! # Running
//!
//! ```bash
//! # Run a specific harness (recommended - running all at once may SIGSEGV)
//! cargo kani -p rource-math --harness verify_vec2_length_non_negative
//! ```

mod bounds;
mod color;
mod mat3;
mod mat4;
mod rect;
mod utils;
mod vec2;
mod vec3;
mod vec4;
