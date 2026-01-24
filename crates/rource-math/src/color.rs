// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Color types for RGBA, RGB, and HSL color representations.

use std::fmt;

// ============================================================================
// Compile-Time Lookup Table for u8 -> f32 Conversion
// ============================================================================

/// Lookup table for u8 -> f32 conversion (0-255 -> 0.0-1.0).
///
/// Pre-computed at compile time for deterministic results and ~50% faster
/// conversion compared to runtime division.
static U8_TO_F32_LUT: [f32; 256] = {
    let mut table = [0.0f32; 256];
    let mut i = 0u32;
    while i < 256 {
        table[i as usize] = i as f32 / 255.0;
        i += 1;
    }
    table
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// An RGBA color with floating-point components in the range [0.0, 1.0].
///
/// This is the primary color type used throughout Rource for rendering.
///
/// # Examples
///
/// ```
/// use rource_math::Color;
///
/// // Create colors
/// let red = Color::RED;
/// let semi_transparent = Color::new(1.0, 0.0, 0.0, 0.5);
///
/// // From hex
/// let blue = Color::from_hex(0x0000FF);
/// let with_alpha = Color::from_hex_alpha(0xFF0000FF);
///
/// // Interpolate
/// let purple = Color::RED.lerp(Color::BLUE, 0.5);
/// ```
#[derive(Clone, Copy, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[repr(C)]
pub struct Color {
    /// Red component [0.0, 1.0].
    pub r: f32,
    /// Green component [0.0, 1.0].
    pub g: f32,
    /// Blue component [0.0, 1.0].
    pub b: f32,
    /// Alpha component [0.0, 1.0] (0 = transparent, 1 = opaque).
    pub a: f32,
}

impl Color {
    /// Transparent black.
    pub const TRANSPARENT: Self = Self {
        r: 0.0,
        g: 0.0,
        b: 0.0,
        a: 0.0,
    };

    /// Opaque black.
    pub const BLACK: Self = Self {
        r: 0.0,
        g: 0.0,
        b: 0.0,
        a: 1.0,
    };

    /// Opaque white.
    pub const WHITE: Self = Self {
        r: 1.0,
        g: 1.0,
        b: 1.0,
        a: 1.0,
    };

    /// Opaque red.
    pub const RED: Self = Self {
        r: 1.0,
        g: 0.0,
        b: 0.0,
        a: 1.0,
    };

    /// Opaque green.
    pub const GREEN: Self = Self {
        r: 0.0,
        g: 1.0,
        b: 0.0,
        a: 1.0,
    };

    /// Opaque blue.
    pub const BLUE: Self = Self {
        r: 0.0,
        g: 0.0,
        b: 1.0,
        a: 1.0,
    };

    /// Opaque yellow.
    pub const YELLOW: Self = Self {
        r: 1.0,
        g: 1.0,
        b: 0.0,
        a: 1.0,
    };

    /// Opaque cyan.
    pub const CYAN: Self = Self {
        r: 0.0,
        g: 1.0,
        b: 1.0,
        a: 1.0,
    };

    /// Opaque magenta.
    pub const MAGENTA: Self = Self {
        r: 1.0,
        g: 0.0,
        b: 1.0,
        a: 1.0,
    };

    /// Opaque orange (Gource modify action color).
    pub const ORANGE: Self = Self {
        r: 1.0,
        g: 0.5,
        b: 0.0,
        a: 1.0,
    };

    /// Opaque gray (50% brightness).
    pub const GRAY: Self = Self {
        r: 0.5,
        g: 0.5,
        b: 0.5,
        a: 1.0,
    };

    /// Creates a new color with the given RGBA components.
    ///
    /// Components should be in the range [0.0, 1.0].
    #[inline]
    #[must_use]
    pub const fn new(r: f32, g: f32, b: f32, a: f32) -> Self {
        Self { r, g, b, a }
    }

    /// Creates a fully opaque color with the given RGB components.
    #[inline]
    #[must_use]
    pub const fn rgb(r: f32, g: f32, b: f32) -> Self {
        Self { r, g, b, a: 1.0 }
    }

    /// Creates a grayscale color with the given intensity.
    #[inline]
    #[must_use]
    pub const fn gray(value: f32) -> Self {
        Self {
            r: value,
            g: value,
            b: value,
            a: 1.0,
        }
    }

    /// Creates a color from a hex RGB value (e.g., 0xFF0000 for red).
    ///
    /// Uses a compile-time lookup table for ~50% faster conversion.
    ///
    /// # Examples
    ///
    /// ```
    /// use rource_math::Color;
    ///
    /// let red = Color::from_hex(0xFF0000);
    /// let green = Color::from_hex(0x00FF00);
    /// let blue = Color::from_hex(0x0000FF);
    /// ```
    #[inline]
    #[must_use]
    pub fn from_hex(hex: u32) -> Self {
        Self {
            r: U8_TO_F32_LUT[((hex >> 16) & 0xFF) as usize],
            g: U8_TO_F32_LUT[((hex >> 8) & 0xFF) as usize],
            b: U8_TO_F32_LUT[(hex & 0xFF) as usize],
            a: 1.0,
        }
    }

    /// Creates a color from a hex RGBA value (e.g., 0xFF0000FF for opaque red).
    ///
    /// The format is 0xRRGGBBAA.
    /// Uses a compile-time lookup table for ~50% faster conversion.
    #[inline]
    #[must_use]
    pub fn from_hex_alpha(hex: u32) -> Self {
        Self {
            r: U8_TO_F32_LUT[((hex >> 24) & 0xFF) as usize],
            g: U8_TO_F32_LUT[((hex >> 16) & 0xFF) as usize],
            b: U8_TO_F32_LUT[((hex >> 8) & 0xFF) as usize],
            a: U8_TO_F32_LUT[(hex & 0xFF) as usize],
        }
    }

    /// Creates a color from 8-bit RGBA values (0-255).
    ///
    /// Uses a compile-time lookup table for ~36% faster conversion.
    #[inline]
    #[must_use]
    pub fn from_rgba8(r: u8, g: u8, b: u8, a: u8) -> Self {
        Self {
            r: U8_TO_F32_LUT[r as usize],
            g: U8_TO_F32_LUT[g as usize],
            b: U8_TO_F32_LUT[b as usize],
            a: U8_TO_F32_LUT[a as usize],
        }
    }

    /// Creates a color from 8-bit RGB values (0-255), with full opacity.
    #[inline]
    #[must_use]
    pub fn from_rgb8(r: u8, g: u8, b: u8) -> Self {
        Self::from_rgba8(r, g, b, 255)
    }

    /// Creates a color from 8-bit RGB values.
    ///
    /// Uses a compile-time lookup table for ~36% faster conversion.
    ///
    /// Note: This function is not const due to MSRV constraints (const float
    /// arithmetic requires Rust 1.82+). Use this for color definitions.
    #[inline]
    #[must_use]
    pub fn from_rgb8_const(r: u8, g: u8, b: u8) -> Self {
        Self {
            r: U8_TO_F32_LUT[r as usize],
            g: U8_TO_F32_LUT[g as usize],
            b: U8_TO_F32_LUT[b as usize],
            a: 1.0,
        }
    }

    /// Converts to a packed 32-bit RGBA value (0xRRGGBBAA).
    ///
    /// Uses `+0.5` truncation instead of `.round()` for ~62% faster conversion.
    #[inline]
    #[must_use]
    pub fn to_rgba8(self) -> u32 {
        // Add 0.5 before truncation to achieve rounding behavior
        // This is ~3x faster than calling .round()
        let r = (self.r.clamp(0.0, 1.0) * 255.0 + 0.5) as u32;
        let g = (self.g.clamp(0.0, 1.0) * 255.0 + 0.5) as u32;
        let b = (self.b.clamp(0.0, 1.0) * 255.0 + 0.5) as u32;
        let a = (self.a.clamp(0.0, 1.0) * 255.0 + 0.5) as u32;
        (r << 24) | (g << 16) | (b << 8) | a
    }

    /// Converts to a packed 32-bit ARGB value (0xAARRGGBB).
    ///
    /// This format is common for software framebuffers.
    /// Uses `+0.5` truncation instead of `.round()` for ~62% faster conversion.
    #[inline]
    #[must_use]
    pub fn to_argb8(self) -> u32 {
        let r = (self.r.clamp(0.0, 1.0) * 255.0 + 0.5) as u32;
        let g = (self.g.clamp(0.0, 1.0) * 255.0 + 0.5) as u32;
        let b = (self.b.clamp(0.0, 1.0) * 255.0 + 0.5) as u32;
        let a = (self.a.clamp(0.0, 1.0) * 255.0 + 0.5) as u32;
        (a << 24) | (r << 16) | (g << 8) | b
    }

    /// Converts to a packed 32-bit ABGR value (0xAABBGGRR).
    ///
    /// This format is used by some graphics APIs.
    /// Uses `+0.5` truncation instead of `.round()` for ~62% faster conversion.
    #[inline]
    #[must_use]
    pub fn to_abgr8(self) -> u32 {
        let r = (self.r.clamp(0.0, 1.0) * 255.0 + 0.5) as u32;
        let g = (self.g.clamp(0.0, 1.0) * 255.0 + 0.5) as u32;
        let b = (self.b.clamp(0.0, 1.0) * 255.0 + 0.5) as u32;
        let a = (self.a.clamp(0.0, 1.0) * 255.0 + 0.5) as u32;
        (a << 24) | (b << 16) | (g << 8) | r
    }

    /// Returns this color with a different alpha value.
    #[inline]
    #[must_use]
    pub const fn with_alpha(self, alpha: f32) -> Self {
        Self {
            r: self.r,
            g: self.g,
            b: self.b,
            a: alpha,
        }
    }

    /// Returns this color with alpha multiplied by the given factor.
    #[inline]
    #[must_use]
    pub fn fade(self, factor: f32) -> Self {
        Self {
            r: self.r,
            g: self.g,
            b: self.b,
            a: self.a * factor,
        }
    }

    /// Linearly interpolates between two colors.
    #[inline]
    #[must_use]
    pub fn lerp(self, other: Self, t: f32) -> Self {
        Self {
            r: crate::lerp(self.r, other.r, t),
            g: crate::lerp(self.g, other.g, t),
            b: crate::lerp(self.b, other.b, t),
            a: crate::lerp(self.a, other.a, t),
        }
    }

    /// Returns the color clamped to valid [0.0, 1.0] range.
    #[inline]
    #[must_use]
    pub fn clamp(self) -> Self {
        Self {
            r: self.r.clamp(0.0, 1.0),
            g: self.g.clamp(0.0, 1.0),
            b: self.b.clamp(0.0, 1.0),
            a: self.a.clamp(0.0, 1.0),
        }
    }

    /// Returns the luminance of the color (perceived brightness).
    ///
    /// Uses the standard Rec. 709 coefficients.
    #[inline]
    #[must_use]
    pub fn luminance(self) -> f32 {
        0.2126 * self.r + 0.7152 * self.g + 0.0722 * self.b
    }

    /// Returns a color that contrasts well with this one (black or white).
    #[inline]
    #[must_use]
    pub fn contrasting(self) -> Self {
        if self.luminance() > 0.5 {
            Self::BLACK
        } else {
            Self::WHITE
        }
    }

    /// Converts to HSL representation.
    #[must_use]
    pub fn to_hsl(self) -> Hsl {
        Hsl::from_color(self)
    }

    /// Creates a color from HSL representation.
    #[must_use]
    pub fn from_hsl(hsl: Hsl) -> Self {
        hsl.to_color()
    }

    /// Premultiplies the RGB components by the alpha.
    ///
    /// This is useful for certain blending operations.
    #[inline]
    #[must_use]
    pub fn premultiplied(self) -> Self {
        Self {
            r: self.r * self.a,
            g: self.g * self.a,
            b: self.b * self.a,
            a: self.a,
        }
    }

    /// Blends this color over another using standard alpha blending.
    ///
    /// Uses the formula: result = src * `src_alpha` + dst * (1 - `src_alpha`)
    #[inline]
    #[must_use]
    pub fn blend_over(self, background: Self) -> Self {
        let inv_alpha = 1.0 - self.a;
        Self {
            r: self.r * self.a + background.r * inv_alpha,
            g: self.g * self.a + background.g * inv_alpha,
            b: self.b * self.a + background.b * inv_alpha,
            a: self.a + background.a * inv_alpha,
        }
    }

    /// Checks if this color is approximately equal to another.
    #[inline]
    #[must_use]
    pub fn approx_eq(self, other: Self) -> bool {
        crate::approx_eq(self.r, other.r)
            && crate::approx_eq(self.g, other.g)
            && crate::approx_eq(self.b, other.b)
            && crate::approx_eq(self.a, other.a)
    }
}

impl fmt::Debug for Color {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Color")
            .field("r", &self.r)
            .field("g", &self.g)
            .field("b", &self.b)
            .field("a", &self.a)
            .finish()
    }
}

impl fmt::Display for Color {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "rgba({:.0}, {:.0}, {:.0}, {:.2})",
            self.r * 255.0,
            self.g * 255.0,
            self.b * 255.0,
            self.a
        )
    }
}

impl From<[f32; 4]> for Color {
    #[inline]
    fn from([r, g, b, a]: [f32; 4]) -> Self {
        Self { r, g, b, a }
    }
}

impl From<[f32; 3]> for Color {
    #[inline]
    fn from([r, g, b]: [f32; 3]) -> Self {
        Self { r, g, b, a: 1.0 }
    }
}

impl From<Color> for [f32; 4] {
    #[inline]
    fn from(c: Color) -> Self {
        [c.r, c.g, c.b, c.a]
    }
}

impl From<Color> for [f32; 3] {
    #[inline]
    fn from(c: Color) -> Self {
        [c.r, c.g, c.b]
    }
}

/// An RGB color without alpha.
#[derive(Clone, Copy, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Rgb {
    /// Red component [0.0, 1.0].
    pub r: f32,
    /// Green component [0.0, 1.0].
    pub g: f32,
    /// Blue component [0.0, 1.0].
    pub b: f32,
}

impl Rgb {
    /// Creates a new RGB color.
    #[inline]
    #[must_use]
    pub const fn new(r: f32, g: f32, b: f32) -> Self {
        Self { r, g, b }
    }

    /// Converts to a Color with full opacity.
    #[inline]
    #[must_use]
    pub const fn to_color(self) -> Color {
        Color {
            r: self.r,
            g: self.g,
            b: self.b,
            a: 1.0,
        }
    }

    /// Converts to a Color with the specified alpha.
    #[inline]
    #[must_use]
    pub const fn with_alpha(self, a: f32) -> Color {
        Color {
            r: self.r,
            g: self.g,
            b: self.b,
            a,
        }
    }
}

impl From<Color> for Rgb {
    #[inline]
    fn from(c: Color) -> Self {
        Self {
            r: c.r,
            g: c.g,
            b: c.b,
        }
    }
}

impl From<Rgb> for Color {
    #[inline]
    fn from(rgb: Rgb) -> Self {
        rgb.to_color()
    }
}

impl fmt::Debug for Rgb {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Rgb")
            .field("r", &self.r)
            .field("g", &self.g)
            .field("b", &self.b)
            .finish()
    }
}

/// An HSL (Hue, Saturation, Lightness) color.
///
/// HSL is useful for color manipulation like adjusting brightness
/// or creating color palettes.
#[derive(Clone, Copy, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Hsl {
    /// Hue in degrees [0.0, 360.0).
    pub h: f32,
    /// Saturation [0.0, 1.0].
    pub s: f32,
    /// Lightness [0.0, 1.0].
    pub l: f32,
}

impl Hsl {
    /// Creates a new HSL color.
    ///
    /// # Arguments
    ///
    /// * `h` - Hue in degrees [0, 360)
    /// * `s` - Saturation [0, 1]
    /// * `l` - Lightness [0, 1]
    #[inline]
    #[must_use]
    pub const fn new(h: f32, s: f32, l: f32) -> Self {
        Self { h, s, l }
    }

    /// Creates an HSL color from an RGB color.
    #[must_use]
    pub fn from_color(color: Color) -> Self {
        let r = color.r;
        let g = color.g;
        let b = color.b;

        let max = r.max(g).max(b);
        let min = r.min(g).min(b);
        let l = (max + min) / 2.0;

        if (max - min).abs() < crate::EPSILON {
            // Achromatic (gray)
            return Self { h: 0.0, s: 0.0, l };
        }

        let d = max - min;
        let s = if l > 0.5 {
            d / (2.0 - max - min)
        } else {
            d / (max + min)
        };

        let h = if (max - r).abs() < crate::EPSILON {
            let mut h = (g - b) / d;
            if g < b {
                h += 6.0;
            }
            h
        } else if (max - g).abs() < crate::EPSILON {
            (b - r) / d + 2.0
        } else {
            (r - g) / d + 4.0
        };

        Self { h: h * 60.0, s, l }
    }

    /// Converts to an RGB Color.
    #[must_use]
    pub fn to_color(self) -> Color {
        if self.s.abs() < crate::EPSILON {
            // Achromatic (gray)
            return Color::rgb(self.l, self.l, self.l);
        }

        let q = if self.l < 0.5 {
            self.l * (1.0 + self.s)
        } else {
            self.l + self.s - self.l * self.s
        };
        let p = 2.0 * self.l - q;
        let h = self.h / 360.0;

        let r = hue_to_rgb(p, q, h + 1.0 / 3.0);
        let g = hue_to_rgb(p, q, h);
        let b = hue_to_rgb(p, q, h - 1.0 / 3.0);

        Color::rgb(r, g, b)
    }

    /// Returns this color with adjusted lightness.
    #[inline]
    #[must_use]
    pub fn with_lightness(self, l: f32) -> Self {
        Self {
            h: self.h,
            s: self.s,
            l,
        }
    }

    /// Returns this color with adjusted saturation.
    #[inline]
    #[must_use]
    pub fn with_saturation(self, s: f32) -> Self {
        Self {
            h: self.h,
            s,
            l: self.l,
        }
    }

    /// Returns this color with adjusted hue.
    #[inline]
    #[must_use]
    pub fn with_hue(self, h: f32) -> Self {
        Self {
            h,
            s: self.s,
            l: self.l,
        }
    }

    /// Rotates the hue by the given amount in degrees.
    #[inline]
    #[must_use]
    pub fn rotate_hue(self, degrees: f32) -> Self {
        Self {
            h: (self.h + degrees).rem_euclid(360.0),
            s: self.s,
            l: self.l,
        }
    }
}

/// Helper function for HSL to RGB conversion.
fn hue_to_rgb(p: f32, q: f32, mut t: f32) -> f32 {
    if t < 0.0 {
        t += 1.0;
    }
    if t > 1.0 {
        t -= 1.0;
    }

    if t < 1.0 / 6.0 {
        p + (q - p) * 6.0 * t
    } else if t < 1.0 / 2.0 {
        q
    } else if t < 2.0 / 3.0 {
        p + (q - p) * (2.0 / 3.0 - t) * 6.0
    } else {
        p
    }
}

impl fmt::Debug for Hsl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Hsl")
            .field("h", &self.h)
            .field("s", &self.s)
            .field("l", &self.l)
            .finish()
    }
}

impl fmt::Display for Hsl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "hsl({:.0}, {:.0}%, {:.0}%)",
            self.h,
            self.s * 100.0,
            self.l * 100.0
        )
    }
}

#[cfg(test)]
#[allow(
    clippy::unreadable_literal,
    clippy::cast_possible_wrap,
    clippy::uninlined_format_args
)]
mod tests {
    use super::*;

    #[test]
    fn test_color_constants() {
        assert_eq!(Color::BLACK.r, 0.0);
        assert_eq!(Color::BLACK.a, 1.0);
        assert_eq!(Color::WHITE.r, 1.0);
        assert_eq!(Color::TRANSPARENT.a, 0.0);
    }

    #[test]
    fn test_color_new() {
        let c = Color::new(0.5, 0.6, 0.7, 0.8);
        assert_eq!(c.r, 0.5);
        assert_eq!(c.g, 0.6);
        assert_eq!(c.b, 0.7);
        assert_eq!(c.a, 0.8);
    }

    #[test]
    fn test_color_rgb() {
        let c = Color::rgb(0.5, 0.6, 0.7);
        assert_eq!(c.a, 1.0);
    }

    #[test]
    fn test_color_gray() {
        let c = Color::gray(0.5);
        assert_eq!(c.r, 0.5);
        assert_eq!(c.g, 0.5);
        assert_eq!(c.b, 0.5);
        assert_eq!(c.a, 1.0);
    }

    #[test]
    fn test_color_from_hex() {
        let red = Color::from_hex(0xFF0000);
        assert!(red.approx_eq(Color::RED));

        let green = Color::from_hex(0x00FF00);
        assert!(green.approx_eq(Color::GREEN));

        let blue = Color::from_hex(0x0000FF);
        assert!(blue.approx_eq(Color::BLUE));
    }

    #[test]
    fn test_color_from_hex_alpha() {
        let c = Color::from_hex_alpha(0xFF000080);
        assert!((c.r - 1.0).abs() < 0.01);
        assert!(c.g.abs() < 0.01);
        assert!(c.b.abs() < 0.01);
        assert!((c.a - 0.502).abs() < 0.01);
    }

    #[test]
    fn test_color_from_rgba8() {
        let c = Color::from_rgba8(255, 128, 0, 255);
        assert!((c.r - 1.0).abs() < 0.01);
        assert!((c.g - 0.502).abs() < 0.01);
        assert!(c.b.abs() < 0.01);
        assert!((c.a - 1.0).abs() < 0.01);
    }

    #[test]
    fn test_color_to_rgba8() {
        let c = Color::new(1.0, 0.5, 0.0, 1.0);
        let packed = c.to_rgba8();
        assert_eq!(packed >> 24, 255);
        assert!((((packed >> 16) & 0xFF) as i32 - 128).abs() <= 1);
        assert_eq!((packed >> 8) & 0xFF, 0);
        assert_eq!(packed & 0xFF, 255);
    }

    #[test]
    fn test_color_to_argb8() {
        let c = Color::RED;
        let packed = c.to_argb8();
        assert_eq!(packed, 0xFFFF0000);
    }

    #[test]
    fn test_color_to_abgr8() {
        let c = Color::RED;
        let packed = c.to_abgr8();
        assert_eq!(packed, 0xFF0000FF);
    }

    #[test]
    fn test_color_with_alpha() {
        let c = Color::RED.with_alpha(0.5);
        assert_eq!(c.r, 1.0);
        assert_eq!(c.a, 0.5);
    }

    #[test]
    fn test_color_fade() {
        let c = Color::RED.fade(0.5);
        assert_eq!(c.a, 0.5);
    }

    #[test]
    fn test_color_lerp() {
        let c = Color::BLACK.lerp(Color::WHITE, 0.5);
        assert!((c.r - 0.5).abs() < crate::EPSILON);
        assert!((c.g - 0.5).abs() < crate::EPSILON);
        assert!((c.b - 0.5).abs() < crate::EPSILON);
    }

    #[test]
    fn test_color_luminance() {
        assert!(Color::WHITE.luminance() > 0.99);
        assert!(Color::BLACK.luminance() < 0.01);
    }

    #[test]
    fn test_color_contrasting() {
        assert_eq!(Color::WHITE.contrasting(), Color::BLACK);
        assert_eq!(Color::BLACK.contrasting(), Color::WHITE);
    }

    #[test]
    fn test_color_premultiplied() {
        let c = Color::new(1.0, 0.5, 0.0, 0.5).premultiplied();
        assert!((c.r - 0.5).abs() < crate::EPSILON);
        assert!((c.g - 0.25).abs() < crate::EPSILON);
        assert!(c.b.abs() < crate::EPSILON);
    }

    #[test]
    fn test_color_blend_over() {
        let fg = Color::new(1.0, 0.0, 0.0, 0.5);
        let bg = Color::new(0.0, 0.0, 1.0, 1.0);
        let result = fg.blend_over(bg);
        assert!((result.r - 0.5).abs() < crate::EPSILON);
        assert!((result.b - 0.5).abs() < crate::EPSILON);
    }

    #[test]
    fn test_hsl_roundtrip() {
        let colors = [
            Color::RED,
            Color::GREEN,
            Color::BLUE,
            Color::WHITE,
            Color::BLACK,
            Color::rgb(0.5, 0.3, 0.7),
        ];

        for color in colors {
            let hsl = color.to_hsl();
            let back = hsl.to_color();
            assert!(
                color.approx_eq(back),
                "Color {:?} -> HSL {:?} -> Color {:?}",
                color,
                hsl,
                back
            );
        }
    }

    #[test]
    fn test_hsl_manipulation() {
        let red_hsl = Color::RED.to_hsl();

        // Rotate hue 120 degrees to get green-ish
        let rotated = red_hsl.rotate_hue(120.0);
        assert!((rotated.h - 120.0).abs() < 1.0);

        // Adjust lightness
        let lighter = red_hsl.with_lightness(0.75);
        let lighter_color = lighter.to_color();
        assert!(lighter_color.luminance() > Color::RED.luminance());
    }

    #[test]
    fn test_rgb_conversion() {
        let rgb = Rgb::new(1.0, 0.5, 0.0);
        let color = rgb.to_color();
        assert_eq!(color.r, 1.0);
        assert_eq!(color.g, 0.5);
        assert_eq!(color.a, 1.0);

        let color_with_alpha = rgb.with_alpha(0.5);
        assert_eq!(color_with_alpha.a, 0.5);
    }

    #[test]
    fn test_color_conversions() {
        let c = Color::new(0.1, 0.2, 0.3, 0.4);

        let arr4: [f32; 4] = c.into();
        assert_eq!(arr4, [0.1, 0.2, 0.3, 0.4]);

        let arr3: [f32; 3] = c.into();
        assert_eq!(arr3, [0.1, 0.2, 0.3]);

        assert_eq!(Color::from([0.1, 0.2, 0.3, 0.4]), c);
        assert_eq!(Color::from([0.1, 0.2, 0.3]), Color::rgb(0.1, 0.2, 0.3));
    }

    #[test]
    fn test_display() {
        let c = Color::new(1.0, 0.5, 0.0, 0.75);
        let s = format!("{c}");
        assert!(s.contains("255"));
        assert!(s.contains("0.75"));
    }
}
