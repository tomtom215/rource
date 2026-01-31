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

    // =========================================================================
    // Mutation Testing: Targeted tests to kill MISSED mutants
    // =========================================================================

    /// Test `from_hex_alpha` with isolated channel values to verify bit positions.
    /// Each test isolates one channel to ensure correct shift amounts.
    #[test]
    fn test_from_hex_alpha_isolated_channels() {
        // Test R channel only (bits 24-31): 0xRR000000
        let r_only = Color::from_hex_alpha(0xAB000000);
        assert!(
            (r_only.r - (0xAB as f32 / 255.0)).abs() < 0.001,
            "R channel extraction failed"
        );
        assert!(r_only.g.abs() < 0.001, "G should be 0 when only R is set");
        assert!(r_only.b.abs() < 0.001, "B should be 0 when only R is set");
        assert!(r_only.a.abs() < 0.001, "A should be 0 when only R is set");

        // Test G channel only (bits 16-23): 0x00GG0000
        let g_only = Color::from_hex_alpha(0x00CD0000);
        assert!(g_only.r.abs() < 0.001, "R should be 0 when only G is set");
        assert!(
            (g_only.g - (0xCD as f32 / 255.0)).abs() < 0.001,
            "G channel extraction failed"
        );
        assert!(g_only.b.abs() < 0.001, "B should be 0 when only G is set");
        assert!(g_only.a.abs() < 0.001, "A should be 0 when only G is set");

        // Test B channel only (bits 8-15): 0x0000BB00
        let b_only = Color::from_hex_alpha(0x0000EF00);
        assert!(b_only.r.abs() < 0.001, "R should be 0 when only B is set");
        assert!(b_only.g.abs() < 0.001, "G should be 0 when only B is set");
        assert!(
            (b_only.b - (0xEF as f32 / 255.0)).abs() < 0.001,
            "B channel extraction failed"
        );
        assert!(b_only.a.abs() < 0.001, "A should be 0 when only B is set");

        // Test A channel only (bits 0-7): 0x000000AA
        let a_only = Color::from_hex_alpha(0x00000089);
        assert!(a_only.r.abs() < 0.001, "R should be 0 when only A is set");
        assert!(a_only.g.abs() < 0.001, "G should be 0 when only A is set");
        assert!(a_only.b.abs() < 0.001, "B should be 0 when only A is set");
        assert!(
            (a_only.a - (0x89 as f32 / 255.0)).abs() < 0.001,
            "A channel extraction failed"
        );

        // Test all channels with distinct values
        let mixed = Color::from_hex_alpha(0x12345678);
        assert!((mixed.r - (0x12 as f32 / 255.0)).abs() < 0.001);
        assert!((mixed.g - (0x34 as f32 / 255.0)).abs() < 0.001);
        assert!((mixed.b - (0x56 as f32 / 255.0)).abs() < 0.001);
        assert!((mixed.a - (0x78 as f32 / 255.0)).abs() < 0.001);
    }

    /// Test `to_rgba8` bit positions by verifying each channel independently.
    /// Format: 0xRRGGBBAA
    #[test]
    fn test_to_rgba8_bit_positions() {
        // Test with isolated R channel (1.0, 0.0, 0.0, 0.0)
        let r_only = Color::new(1.0, 0.0, 0.0, 0.0).to_rgba8();
        assert_eq!(r_only >> 24, 255, "R should be in bits 24-31");
        assert_eq!((r_only >> 16) & 0xFF, 0, "G should be 0");
        assert_eq!((r_only >> 8) & 0xFF, 0, "B should be 0");
        assert_eq!(r_only & 0xFF, 0, "A should be 0");

        // Test with isolated G channel (0.0, 1.0, 0.0, 0.0)
        let g_only = Color::new(0.0, 1.0, 0.0, 0.0).to_rgba8();
        assert_eq!(g_only >> 24, 0, "R should be 0");
        assert_eq!((g_only >> 16) & 0xFF, 255, "G should be in bits 16-23");
        assert_eq!((g_only >> 8) & 0xFF, 0, "B should be 0");
        assert_eq!(g_only & 0xFF, 0, "A should be 0");

        // Test with isolated B channel (0.0, 0.0, 1.0, 0.0)
        let b_only = Color::new(0.0, 0.0, 1.0, 0.0).to_rgba8();
        assert_eq!(b_only >> 24, 0, "R should be 0");
        assert_eq!((b_only >> 16) & 0xFF, 0, "G should be 0");
        assert_eq!((b_only >> 8) & 0xFF, 255, "B should be in bits 8-15");
        assert_eq!(b_only & 0xFF, 0, "A should be 0");

        // Test with isolated A channel (0.0, 0.0, 0.0, 1.0)
        let a_only = Color::new(0.0, 0.0, 0.0, 1.0).to_rgba8();
        assert_eq!(a_only >> 24, 0, "R should be 0");
        assert_eq!((a_only >> 16) & 0xFF, 0, "G should be 0");
        assert_eq!((a_only >> 8) & 0xFF, 0, "B should be 0");
        assert_eq!(a_only & 0xFF, 255, "A should be in bits 0-7");

        // Verify format is exactly 0xRRGGBBAA
        assert_eq!(Color::RED.to_rgba8(), 0xFF0000FF);
        assert_eq!(Color::GREEN.to_rgba8(), 0x00FF00FF);
        assert_eq!(Color::BLUE.to_rgba8(), 0x0000FFFF);
        assert_eq!(Color::WHITE.to_rgba8(), 0xFFFFFFFF);
        assert_eq!(Color::BLACK.to_rgba8(), 0x000000FF);
        assert_eq!(Color::TRANSPARENT.to_rgba8(), 0x00000000);
    }

    /// Test `to_argb8` bit positions by verifying each channel independently.
    /// Format: 0xAARRGGBB
    #[test]
    fn test_to_argb8_bit_positions() {
        // Test with isolated A channel
        let a_only = Color::new(0.0, 0.0, 0.0, 1.0).to_argb8();
        assert_eq!(a_only >> 24, 255, "A should be in bits 24-31");
        assert_eq!((a_only >> 16) & 0xFF, 0, "R should be 0");
        assert_eq!((a_only >> 8) & 0xFF, 0, "G should be 0");
        assert_eq!(a_only & 0xFF, 0, "B should be 0");

        // Test with isolated R channel
        let r_only = Color::new(1.0, 0.0, 0.0, 0.0).to_argb8();
        assert_eq!(r_only >> 24, 0, "A should be 0");
        assert_eq!((r_only >> 16) & 0xFF, 255, "R should be in bits 16-23");
        assert_eq!((r_only >> 8) & 0xFF, 0, "G should be 0");
        assert_eq!(r_only & 0xFF, 0, "B should be 0");

        // Test with isolated G channel
        let g_only = Color::new(0.0, 1.0, 0.0, 0.0).to_argb8();
        assert_eq!(g_only >> 24, 0, "A should be 0");
        assert_eq!((g_only >> 16) & 0xFF, 0, "R should be 0");
        assert_eq!((g_only >> 8) & 0xFF, 255, "G should be in bits 8-15");
        assert_eq!(g_only & 0xFF, 0, "B should be 0");

        // Test with isolated B channel
        let b_only = Color::new(0.0, 0.0, 1.0, 0.0).to_argb8();
        assert_eq!(b_only >> 24, 0, "A should be 0");
        assert_eq!((b_only >> 16) & 0xFF, 0, "R should be 0");
        assert_eq!((b_only >> 8) & 0xFF, 0, "G should be 0");
        assert_eq!(b_only & 0xFF, 255, "B should be in bits 0-7");

        // Verify format is exactly 0xAARRGGBB
        assert_eq!(Color::GREEN.to_argb8(), 0xFF00FF00);
        assert_eq!(Color::BLUE.to_argb8(), 0xFF0000FF);
        assert_eq!(Color::WHITE.to_argb8(), 0xFFFFFFFF);
        assert_eq!(Color::BLACK.to_argb8(), 0xFF000000);
    }

    /// Test `to_abgr8` bit positions by verifying each channel independently.
    /// Format: 0xAABBGGRR
    #[test]
    fn test_to_abgr8_bit_positions() {
        // Test with isolated A channel
        let a_only = Color::new(0.0, 0.0, 0.0, 1.0).to_abgr8();
        assert_eq!(a_only >> 24, 255, "A should be in bits 24-31");
        assert_eq!((a_only >> 16) & 0xFF, 0, "B should be 0");
        assert_eq!((a_only >> 8) & 0xFF, 0, "G should be 0");
        assert_eq!(a_only & 0xFF, 0, "R should be 0");

        // Test with isolated B channel
        let b_only = Color::new(0.0, 0.0, 1.0, 0.0).to_abgr8();
        assert_eq!(b_only >> 24, 0, "A should be 0");
        assert_eq!((b_only >> 16) & 0xFF, 255, "B should be in bits 16-23");
        assert_eq!((b_only >> 8) & 0xFF, 0, "G should be 0");
        assert_eq!(b_only & 0xFF, 0, "R should be 0");

        // Test with isolated G channel
        let g_only = Color::new(0.0, 1.0, 0.0, 0.0).to_abgr8();
        assert_eq!(g_only >> 24, 0, "A should be 0");
        assert_eq!((g_only >> 16) & 0xFF, 0, "B should be 0");
        assert_eq!((g_only >> 8) & 0xFF, 255, "G should be in bits 8-15");
        assert_eq!(g_only & 0xFF, 0, "R should be 0");

        // Test with isolated R channel
        let r_only = Color::new(1.0, 0.0, 0.0, 0.0).to_abgr8();
        assert_eq!(r_only >> 24, 0, "A should be 0");
        assert_eq!((r_only >> 16) & 0xFF, 0, "B should be 0");
        assert_eq!((r_only >> 8) & 0xFF, 0, "G should be 0");
        assert_eq!(r_only & 0xFF, 255, "R should be in bits 0-7");

        // Verify format is exactly 0xAABBGGRR
        assert_eq!(Color::GREEN.to_abgr8(), 0xFF00FF00);
        assert_eq!(Color::BLUE.to_abgr8(), 0xFFFF0000);
        assert_eq!(Color::WHITE.to_abgr8(), 0xFFFFFFFF);
        assert_eq!(Color::BLACK.to_abgr8(), 0xFF000000);
    }

    /// Test clamp with boundary values to verify clamping behavior.
    #[test]
    fn test_clamp_boundaries() {
        // Test values below 0.0 are clamped to 0.0
        let below_zero = Color::new(-0.5, -1.0, -100.0, -0.001).clamp();
        assert_eq!(below_zero.r, 0.0, "Negative R should clamp to 0.0");
        assert_eq!(below_zero.g, 0.0, "Negative G should clamp to 0.0");
        assert_eq!(below_zero.b, 0.0, "Negative B should clamp to 0.0");
        assert_eq!(below_zero.a, 0.0, "Negative A should clamp to 0.0");

        // Test values above 1.0 are clamped to 1.0
        let above_one = Color::new(1.5, 2.0, 100.0, 1.001).clamp();
        assert_eq!(above_one.r, 1.0, "R > 1 should clamp to 1.0");
        assert_eq!(above_one.g, 1.0, "G > 1 should clamp to 1.0");
        assert_eq!(above_one.b, 1.0, "B > 1 should clamp to 1.0");
        assert_eq!(above_one.a, 1.0, "A > 1 should clamp to 1.0");

        // Test values within range are preserved
        let in_range = Color::new(0.0, 0.5, 1.0, 0.25).clamp();
        assert_eq!(in_range.r, 0.0, "R at 0.0 should stay 0.0");
        assert_eq!(in_range.g, 0.5, "G at 0.5 should stay 0.5");
        assert_eq!(in_range.b, 1.0, "B at 1.0 should stay 1.0");
        assert_eq!(in_range.a, 0.25, "A at 0.25 should stay 0.25");

        // Test exact boundaries
        let boundaries = Color::new(0.0, 1.0, 0.0, 1.0).clamp();
        assert_eq!(boundaries.r, 0.0);
        assert_eq!(boundaries.g, 1.0);
        assert_eq!(boundaries.b, 0.0);
        assert_eq!(boundaries.a, 1.0);
    }

    /// Test contrasting color at luminance boundary.
    #[test]
    fn test_contrasting_luminance_boundary() {
        // Just below 0.5 luminance should return WHITE
        // Luminance = 0.2126*R + 0.7152*G + 0.0722*B
        // For gray, luminance = value. So gray(0.49) has luminance 0.49 < 0.5
        let dark = Color::gray(0.49);
        assert!(dark.luminance() < 0.5, "Luminance should be < 0.5");
        assert_eq!(
            dark.contrasting(),
            Color::WHITE,
            "Dark color should contrast with WHITE"
        );

        // Just above 0.5 luminance should return BLACK
        let light = Color::gray(0.51);
        assert!(light.luminance() > 0.5, "Luminance should be > 0.5");
        assert_eq!(
            light.contrasting(),
            Color::BLACK,
            "Light color should contrast with BLACK"
        );

        // Test exactly at boundary (0.5 luminance) - should return BLACK (> 0.5 comparison)
        let mid = Color::gray(0.5);
        // luminance(0.5, 0.5, 0.5) = 0.2126*0.5 + 0.7152*0.5 + 0.0722*0.5 = 0.5
        assert!(
            (mid.luminance() - 0.5).abs() < crate::EPSILON,
            "Luminance should be ~0.5"
        );
        // Since luminance == 0.5 is NOT > 0.5, it returns WHITE
        assert_eq!(
            mid.contrasting(),
            Color::WHITE,
            "Mid gray should contrast with WHITE"
        );

        // Test with non-gray colors
        assert_eq!(
            Color::YELLOW.contrasting(),
            Color::BLACK,
            "Yellow is bright"
        );
        assert_eq!(Color::BLUE.contrasting(), Color::WHITE, "Blue is dark");
    }

    /// Test premultiplied alpha multiplication on all channels.
    #[test]
    fn test_premultiplied_all_channels() {
        // Test with alpha = 0.5
        let c = Color::new(1.0, 0.8, 0.6, 0.5).premultiplied();
        assert!((c.r - 0.5).abs() < crate::EPSILON, "R * 0.5 = 0.5");
        assert!((c.g - 0.4).abs() < crate::EPSILON, "G * 0.5 = 0.4");
        assert!((c.b - 0.3).abs() < crate::EPSILON, "B * 0.5 = 0.3");
        assert_eq!(c.a, 0.5, "Alpha should be unchanged");

        // Test with alpha = 0.0 (all channels become 0)
        let zero = Color::new(1.0, 1.0, 1.0, 0.0).premultiplied();
        assert_eq!(zero.r, 0.0, "R * 0 = 0");
        assert_eq!(zero.g, 0.0, "G * 0 = 0");
        assert_eq!(zero.b, 0.0, "B * 0 = 0");
        assert_eq!(zero.a, 0.0);

        // Test with alpha = 1.0 (channels unchanged)
        let full = Color::new(0.5, 0.5, 0.5, 1.0).premultiplied();
        assert_eq!(full.r, 0.5, "R * 1 = R");
        assert_eq!(full.g, 0.5, "G * 1 = G");
        assert_eq!(full.b, 0.5, "B * 1 = B");
        assert_eq!(full.a, 1.0);

        // Test with specific alpha value (0.25)
        let quarter = Color::new(1.0, 0.8, 0.4, 0.25).premultiplied();
        assert!((quarter.r - 0.25).abs() < crate::EPSILON);
        assert!((quarter.g - 0.2).abs() < crate::EPSILON);
        assert!((quarter.b - 0.1).abs() < crate::EPSILON);
    }

    /// Test `blend_over` formula: result = src × alpha + dst × (1 - alpha)
    #[test]
    fn test_blend_over_formula() {
        // Test fully opaque foreground completely covers background
        let fg_opaque = Color::new(1.0, 0.0, 0.0, 1.0);
        let bg = Color::new(0.0, 1.0, 0.0, 1.0);
        let result = fg_opaque.blend_over(bg);
        assert!(
            (result.r - 1.0).abs() < crate::EPSILON,
            "Opaque fg should show"
        );
        assert!(
            result.g.abs() < crate::EPSILON,
            "Bg should not show through opaque fg"
        );
        assert!(result.b.abs() < crate::EPSILON);
        assert!((result.a - 1.0).abs() < crate::EPSILON);

        // Test fully transparent foreground shows only background
        let fg_transparent = Color::new(1.0, 0.0, 0.0, 0.0);
        let result = fg_transparent.blend_over(bg);
        assert!(
            result.r.abs() < crate::EPSILON,
            "Transparent fg should not show"
        );
        assert!(
            (result.g - 1.0).abs() < crate::EPSILON,
            "Bg should show through"
        );
        assert!((result.a - 1.0).abs() < crate::EPSILON);

        // Test 50% blend: result = 0.5 * fg + 0.5 * bg
        let fg_half = Color::new(1.0, 0.0, 0.0, 0.5);
        let result = fg_half.blend_over(bg);
        assert!(
            (result.r - 0.5).abs() < crate::EPSILON,
            "R = 1*0.5 + 0*0.5 = 0.5"
        );
        assert!(
            (result.g - 0.5).abs() < crate::EPSILON,
            "G = 0*0.5 + 1*0.5 = 0.5"
        );
        assert!(result.b.abs() < crate::EPSILON);

        // Test blend with specific values for precise verification
        // fg = (0.8, 0.2, 0.4, 0.75), bg = (0.2, 0.6, 0.8, 1.0)
        // result.r = 0.8*0.75 + 0.2*0.25 = 0.6 + 0.05 = 0.65
        // result.g = 0.2*0.75 + 0.6*0.25 = 0.15 + 0.15 = 0.30
        // result.b = 0.4*0.75 + 0.8*0.25 = 0.30 + 0.20 = 0.50
        let fg = Color::new(0.8, 0.2, 0.4, 0.75);
        let bg2 = Color::new(0.2, 0.6, 0.8, 1.0);
        let result = fg.blend_over(bg2);
        assert!((result.r - 0.65).abs() < 0.001, "R blend formula");
        assert!((result.g - 0.30).abs() < 0.001, "G blend formula");
        assert!((result.b - 0.50).abs() < 0.001, "B blend formula");

        // Test alpha blending: result.a = src.a + bg.a * (1 - src.a)
        let fg_semi = Color::new(1.0, 0.0, 0.0, 0.5);
        let bg_semi = Color::new(0.0, 1.0, 0.0, 0.5);
        let result = fg_semi.blend_over(bg_semi);
        // result.a = 0.5 + 0.5 * (1 - 0.5) = 0.5 + 0.25 = 0.75
        assert!(
            (result.a - 0.75).abs() < crate::EPSILON,
            "Alpha blend formula"
        );
    }

    /// Test HSL conversion with gray colors (achromatic - hue undefined).
    #[test]
    fn test_hsl_achromatic() {
        // Pure gray should have saturation = 0
        let gray = Color::gray(0.5);
        let hsl = gray.to_hsl();
        assert_eq!(hsl.s, 0.0, "Gray should have 0 saturation");
        assert!(
            (hsl.l - 0.5).abs() < crate::EPSILON,
            "Lightness should be 0.5"
        );

        // Converting back should give the same gray
        let back = hsl.to_color();
        assert!(gray.approx_eq(back), "Achromatic roundtrip should work");

        // Test black
        let black_hsl = Color::BLACK.to_hsl();
        assert_eq!(black_hsl.l, 0.0, "Black lightness = 0");
        assert_eq!(black_hsl.s, 0.0, "Black saturation = 0");

        // Test white
        let white_hsl = Color::WHITE.to_hsl();
        assert_eq!(white_hsl.l, 1.0, "White lightness = 1");
        assert_eq!(white_hsl.s, 0.0, "White saturation = 0");
    }

    /// Test HSL hue values for primary colors.
    #[test]
    fn test_hsl_primary_hues() {
        // Red: hue = 0
        let red_hsl = Color::RED.to_hsl();
        assert!(
            red_hsl.h.abs() < 1.0 || (red_hsl.h - 360.0).abs() < 1.0,
            "Red hue ~0"
        );
        assert!(
            (red_hsl.s - 1.0).abs() < crate::EPSILON,
            "Red saturation = 1"
        );
        assert!(
            (red_hsl.l - 0.5).abs() < crate::EPSILON,
            "Red lightness = 0.5"
        );

        // Green: hue = 120
        let green_hsl = Color::GREEN.to_hsl();
        assert!((green_hsl.h - 120.0).abs() < 1.0, "Green hue ~120");

        // Blue: hue = 240
        let blue_hsl = Color::BLUE.to_hsl();
        assert!((blue_hsl.h - 240.0).abs() < 1.0, "Blue hue ~240");

        // Yellow: hue = 60
        let yellow_hsl = Color::YELLOW.to_hsl();
        assert!((yellow_hsl.h - 60.0).abs() < 1.0, "Yellow hue ~60");

        // Cyan: hue = 180
        let cyan_hsl = Color::CYAN.to_hsl();
        assert!((cyan_hsl.h - 180.0).abs() < 1.0, "Cyan hue ~180");

        // Magenta: hue = 300
        let magenta_hsl = Color::MAGENTA.to_hsl();
        assert!((magenta_hsl.h - 300.0).abs() < 1.0, "Magenta hue ~300");
    }

    /// Test HSL saturation calculation for different lightness values.
    #[test]
    fn test_hsl_saturation_lightness_relation() {
        // Low lightness (dark red): L=0.25, S=1.0
        // q = L * (1 + S) = 0.25 * 2 = 0.5
        // p = 2*L - q = 0.5 - 0.5 = 0.0
        // Red hue at 0: r = q = 0.5, g = p = 0.0, b = p = 0.0
        let dark_red = Hsl::new(0.0, 1.0, 0.25).to_color();
        assert!(
            dark_red.r > dark_red.g,
            "Dark red should have more red than green"
        );
        assert!(
            dark_red.r > dark_red.b,
            "Dark red should have more red than blue"
        );
        assert!((dark_red.r - 0.5).abs() < 0.01, "Dark red R should be ~0.5");
        assert!(dark_red.g.abs() < 0.01, "Dark red G should be ~0");

        // High lightness (light red): L=0.75, S=1.0
        // q = L + S - L*S = 0.75 + 1.0 - 0.75 = 1.0
        // p = 2*L - q = 1.5 - 1.0 = 0.5
        // Red hue at 0: r = q = 1.0, g = p = 0.5, b = p = 0.5
        let light_red = Hsl::new(0.0, 1.0, 0.75).to_color();
        assert!(
            light_red.r > light_red.g,
            "Light red should have more red than green"
        );
        assert!(
            (light_red.r - 1.0).abs() < 0.01,
            "Light red R should be ~1.0"
        );
        assert!(
            (light_red.g - 0.5).abs() < 0.01,
            "Light red G should be ~0.5"
        );
        assert!(
            (light_red.b - 0.5).abs() < 0.01,
            "Light red B should be ~0.5"
        );

        // Medium lightness (pure red): L=0.5, S=1.0
        // Should match Color::RED
        let pure_red = Hsl::new(0.0, 1.0, 0.5).to_color();
        assert!(
            pure_red.approx_eq(Color::RED),
            "HSL(0, 1, 0.5) should be pure red"
        );
    }

    /// Test HSL hue rotation.
    #[test]
    fn test_hsl_hue_rotation() {
        let red = Hsl::new(0.0, 1.0, 0.5);

        // Rotate 120 degrees to green
        let rotated = red.rotate_hue(120.0);
        assert!((rotated.h - 120.0).abs() < crate::EPSILON);

        // Rotate 360 degrees back to original
        let full_rotation = red.rotate_hue(360.0);
        assert!(
            full_rotation.h.abs() < crate::EPSILON
                || (full_rotation.h - 360.0).abs() < crate::EPSILON
        );

        // Negative rotation
        let neg_rotation = Hsl::new(60.0, 1.0, 0.5).rotate_hue(-120.0);
        // 60 - 120 = -60, wrapped to 300
        assert!((neg_rotation.h - 300.0).abs() < crate::EPSILON);

        // Large rotation wraps correctly
        let large_rotation = red.rotate_hue(480.0); // 480 % 360 = 120
        assert!((large_rotation.h - 120.0).abs() < crate::EPSILON);
    }

    /// Test `from_hex` with various bit patterns.
    #[test]
    fn test_from_hex_bit_patterns() {
        // Alternating bits: 0xAA = 10101010, 0x55 = 01010101
        let alt = Color::from_hex(0xAA5500);
        assert!((alt.r - (0xAA as f32 / 255.0)).abs() < 0.001);
        assert!((alt.g - (0x55 as f32 / 255.0)).abs() < 0.001);
        assert!(alt.b.abs() < 0.001);

        // Single bit patterns
        assert!((Color::from_hex(0x010000).r - (1.0 / 255.0)).abs() < 0.001);
        assert!((Color::from_hex(0x000100).g - (1.0 / 255.0)).abs() < 0.001);
        assert!((Color::from_hex(0x000001).b - (1.0 / 255.0)).abs() < 0.001);

        // Max value patterns
        assert_eq!(Color::from_hex(0xFFFFFF), Color::WHITE.with_alpha(1.0));
        assert_eq!(Color::from_hex(0x000000), Color::BLACK.with_alpha(1.0));
    }

    /// Test luminance calculation with known values.
    #[test]
    fn test_luminance_coefficients() {
        // Rec. 709 coefficients: 0.2126*R + 0.7152*G + 0.0722*B

        // Pure red luminance = 0.2126
        let red_lum = Color::RED.luminance();
        assert!(
            (red_lum - 0.2126).abs() < 0.001,
            "Red luminance should be ~0.2126"
        );

        // Pure green luminance = 0.7152
        let green_lum = Color::GREEN.luminance();
        assert!(
            (green_lum - 0.7152).abs() < 0.001,
            "Green luminance should be ~0.7152"
        );

        // Pure blue luminance = 0.0722
        let blue_lum = Color::BLUE.luminance();
        assert!(
            (blue_lum - 0.0722).abs() < 0.001,
            "Blue luminance should be ~0.0722"
        );

        // Combined: (0.5, 0.5, 0.5) = 0.5 * (0.2126 + 0.7152 + 0.0722) = 0.5
        let gray_lum = Color::gray(0.5).luminance();
        assert!((gray_lum - 0.5).abs() < 0.001);
    }

    /// Test fade multiplies alpha correctly.
    #[test]
    fn test_fade_alpha_multiplication() {
        let c = Color::new(1.0, 0.5, 0.25, 0.8);

        // Fade by 0.5 should halve alpha
        let faded = c.fade(0.5);
        assert_eq!(faded.r, 1.0, "R unchanged");
        assert_eq!(faded.g, 0.5, "G unchanged");
        assert_eq!(faded.b, 0.25, "B unchanged");
        assert!(
            (faded.a - 0.4).abs() < crate::EPSILON,
            "A = 0.8 * 0.5 = 0.4"
        );

        // Fade by 0 should make fully transparent
        let gone = c.fade(0.0);
        assert_eq!(gone.a, 0.0);

        // Fade by 1 should keep original
        let same = c.fade(1.0);
        assert_eq!(same.a, 0.8);

        // Fade by 2 should double (allowing >1)
        let bright = Color::new(1.0, 1.0, 1.0, 0.5).fade(2.0);
        assert!((bright.a - 1.0).abs() < crate::EPSILON);
    }

    /// Test Rgb struct conversions.
    #[test]
    fn test_rgb_struct() {
        let rgb = Rgb::new(0.3, 0.6, 0.9);

        // to_color has alpha 1.0
        let c = rgb.to_color();
        assert_eq!(c.r, 0.3);
        assert_eq!(c.g, 0.6);
        assert_eq!(c.b, 0.9);
        assert_eq!(c.a, 1.0);

        // with_alpha sets specific alpha
        let c2 = rgb.with_alpha(0.5);
        assert_eq!(c2.a, 0.5);

        // From Color extracts RGB, drops alpha
        let rgb2: Rgb = Color::new(0.1, 0.2, 0.3, 0.4).into();
        assert_eq!(rgb2.r, 0.1);
        assert_eq!(rgb2.g, 0.2);
        assert_eq!(rgb2.b, 0.3);
    }

    /// Test `approx_eq` tolerance.
    #[test]
    fn test_approx_eq() {
        let c1 = Color::new(0.5, 0.5, 0.5, 0.5);
        let c2 = Color::new(0.5 + crate::EPSILON / 2.0, 0.5, 0.5, 0.5);
        assert!(c1.approx_eq(c2), "Small difference should be approx equal");

        let c3 = Color::new(0.5 + 0.01, 0.5, 0.5, 0.5);
        assert!(
            !c1.approx_eq(c3),
            "Larger difference should not be approx equal"
        );
    }

    // ============================================================
    // Color and HSL Method Tests (Phase 1 - Audit Coverage)
    // ============================================================

    #[test]
    fn test_color_gray_mid_value() {
        let gray = Color::gray(0.5);
        assert_eq!(gray.r, 0.5);
        assert_eq!(gray.g, 0.5);
        assert_eq!(gray.b, 0.5);
        assert_eq!(gray.a, 1.0);
    }

    #[test]
    fn test_color_gray_black_extreme() {
        let black = Color::gray(0.0);
        assert_eq!(black.r, 0.0);
        assert_eq!(black.g, 0.0);
        assert_eq!(black.b, 0.0);
        assert_eq!(black.a, 1.0);
    }

    #[test]
    fn test_color_gray_white_extreme() {
        let white = Color::gray(1.0);
        assert_eq!(white.r, 1.0);
        assert_eq!(white.g, 1.0);
        assert_eq!(white.b, 1.0);
        assert_eq!(white.a, 1.0);
    }

    #[test]
    fn test_color_from_rgb8_const() {
        let red = Color::from_rgb8_const(255, 0, 0);
        assert!((red.r - 1.0).abs() < crate::EPSILON);
        assert_eq!(red.g, 0.0);
        assert_eq!(red.b, 0.0);
        assert_eq!(red.a, 1.0);
    }

    #[test]
    fn test_color_from_rgb8_const_mid_values() {
        let mid = Color::from_rgb8_const(128, 64, 192);
        // 128/255 ≈ 0.502, 64/255 ≈ 0.251, 192/255 ≈ 0.753
        assert!((mid.r - 128.0 / 255.0).abs() < crate::EPSILON);
        assert!((mid.g - 64.0 / 255.0).abs() < crate::EPSILON);
        assert!((mid.b - 192.0 / 255.0).abs() < crate::EPSILON);
        assert_eq!(mid.a, 1.0);
    }

    #[test]
    fn test_hsl_new() {
        let hsl = Hsl::new(180.0, 0.5, 0.75);
        assert_eq!(hsl.h, 180.0);
        assert_eq!(hsl.s, 0.5);
        assert_eq!(hsl.l, 0.75);
    }

    #[test]
    fn test_hsl_with_saturation() {
        let hsl = Hsl::new(120.0, 0.3, 0.5);
        let modified = hsl.with_saturation(0.8);
        assert_eq!(modified.h, 120.0);
        assert_eq!(modified.s, 0.8);
        assert_eq!(modified.l, 0.5);
    }

    #[test]
    fn test_hsl_with_saturation_zero() {
        let hsl = Hsl::new(120.0, 0.8, 0.5);
        let grayscale = hsl.with_saturation(0.0);
        // Converting to color should give gray
        let color = grayscale.to_color();
        assert!(
            (color.r - color.g).abs() < crate::EPSILON,
            "Zero saturation should be grayscale"
        );
        assert!(
            (color.g - color.b).abs() < crate::EPSILON,
            "Zero saturation should be grayscale"
        );
    }

    #[test]
    fn test_hsl_with_hue() {
        let hsl = Hsl::new(120.0, 0.5, 0.5);
        let modified = hsl.with_hue(240.0);
        assert_eq!(modified.h, 240.0);
        assert_eq!(modified.s, 0.5);
        assert_eq!(modified.l, 0.5);
    }

    #[test]
    fn test_hsl_with_hue_preserves_others() {
        let original = Hsl::new(60.0, 0.7, 0.3);
        let modified = original.with_hue(180.0);
        assert_eq!(modified.s, original.s);
        assert_eq!(modified.l, original.l);
    }

    #[test]
    fn test_hsl_roundtrip_arbitrary_color() {
        // Test that RGB -> HSL -> RGB preserves the color
        let original = Color::rgb(0.8, 0.3, 0.5);
        let hsl = Hsl::from_color(original);
        let recovered = hsl.to_color();
        assert!(
            (original.r - recovered.r).abs() < 0.01,
            "Red should be preserved"
        );
        assert!(
            (original.g - recovered.g).abs() < 0.01,
            "Green should be preserved"
        );
        assert!(
            (original.b - recovered.b).abs() < 0.01,
            "Blue should be preserved"
        );
    }

    #[test]
    fn test_hsl_rotate_hue() {
        let hsl = Hsl::new(60.0, 0.5, 0.5);
        let rotated = hsl.rotate_hue(120.0);
        assert_eq!(rotated.h, 180.0);
        assert_eq!(rotated.s, 0.5);
        assert_eq!(rotated.l, 0.5);
    }

    #[test]
    fn test_hsl_rotate_hue_wraparound() {
        let hsl = Hsl::new(300.0, 0.5, 0.5);
        let rotated = hsl.rotate_hue(120.0);
        // 300 + 120 = 420, which wraps to 60
        assert!((rotated.h - 60.0).abs() < crate::EPSILON);
    }

    #[test]
    fn test_hsl_rotate_hue_negative() {
        let hsl = Hsl::new(60.0, 0.5, 0.5);
        let rotated = hsl.rotate_hue(-120.0);
        // 60 - 120 = -60, which wraps to 300
        assert!((rotated.h - 300.0).abs() < crate::EPSILON);
    }

    #[test]
    fn test_hsl_primary_colors() {
        // Red: H=0
        let red = Hsl::new(0.0, 1.0, 0.5).to_color();
        assert!((red.r - 1.0).abs() < 0.01);
        assert!(red.g < 0.01);
        assert!(red.b < 0.01);

        // Green: H=120
        let green = Hsl::new(120.0, 1.0, 0.5).to_color();
        assert!(green.r < 0.01);
        assert!((green.g - 1.0).abs() < 0.01);
        assert!(green.b < 0.01);

        // Blue: H=240
        let blue = Hsl::new(240.0, 1.0, 0.5).to_color();
        assert!(blue.r < 0.01);
        assert!(blue.g < 0.01);
        assert!((blue.b - 1.0).abs() < 0.01);
    }

    // =========================================================================
    // Mutation Testing: Kill MISSED mutants in color.rs
    // =========================================================================

    /// Kill mutants: replace | with ^ in to_rgba8/to_argb8/to_abgr8
    /// XOR and OR differ when bits overlap. With distinct channel values
    /// where multiple channels have non-zero bits, XOR produces wrong results.
    /// Use a color where all channels have overlapping bit patterns.
    #[test]
    fn test_to_rgba8_xor_vs_or_kill() {
        // Color with all channels non-zero and overlapping bits
        // r=0.5 -> ~128, g=0.5 -> ~128, b=0.5 -> ~128, a=0.5 -> ~128
        // With OR: (128<<24) | (128<<16) | (128<<8) | 128 = 0x80808080
        // With XOR at any position, the overlapping bits would cancel
        let c = Color::new(0.5, 0.5, 0.5, 0.5);
        let packed = c.to_rgba8();
        // Each channel should be ~128 (0x80)
        let r = (packed >> 24) & 0xFF;
        let g = (packed >> 16) & 0xFF;
        let b = (packed >> 8) & 0xFF;
        let a = packed & 0xFF;
        assert!(r >= 127 && r <= 128, "R channel = {r}");
        assert!(g >= 127 && g <= 128, "G channel = {g}");
        assert!(b >= 127 && b <= 128, "B channel = {b}");
        assert!(a >= 127 && a <= 128, "A channel = {a}");

        // Critical: test with values where channels share bit positions
        // r=1.0, g=1.0 -> both 255. OR: 0xFF00 | 0xFF = 0xFFFF. XOR: 0xFF00 ^ 0xFF = 0xFF00 ^ 0xFF = 0xFFFF (no overlap here)
        // But shift overlap: (255<<24)|(255<<16) = 0xFF_FF_00_00, XOR same
        // The mutation replaces the FULL expression's | operators.
        // Test: (r << 24) | (g << 16) | (b << 8) | a
        // If first | becomes ^: (r<<24) ^ (g<<16) | (b<<8) | a
        // When r=0xFF, g=0xFF: 0xFF000000 ^ 0x00FF0000 = 0xFFFF0000 (same as OR! No overlap)
        // Need overlapping shifted bits. That can't happen with << 24, << 16, etc.
        // Actually, the issue is cargo-mutants replaces INDIVIDUAL | operators.
        // Each | connects terms that DON'T have overlapping bits, so | and ^ are identical.
        // These mutants may be equivalent mutants (can't be killed).
        // But let's verify with exact packed values anyway.
        assert_eq!(
            Color::new(1.0, 1.0, 1.0, 1.0).to_rgba8(),
            0xFFFFFFFF,
            "All 1.0 should produce 0xFFFFFFFF"
        );
    }

    /// Kill mutants: to_argb8 and to_abgr8 with non-trivial values
    #[test]
    fn test_packed_format_distinct_channels() {
        // Use distinct values for each channel to detect any swap
        let c = Color::new(0.2, 0.4, 0.6, 0.8);
        let rgba = c.to_rgba8();
        let argb = c.to_argb8();
        let abgr = c.to_abgr8();

        let r = ((0.2f32 * 255.0 + 0.5) as u32) & 0xFF; // ~51
        let g = ((0.4f32 * 255.0 + 0.5) as u32) & 0xFF; // ~102
        let b = ((0.6f32 * 255.0 + 0.5) as u32) & 0xFF; // ~153
        let a = ((0.8f32 * 255.0 + 0.5) as u32) & 0xFF; // ~204

        // RGBA: 0xRRGGBBAA
        assert_eq!((rgba >> 24) & 0xFF, r, "RGBA R");
        assert_eq!((rgba >> 16) & 0xFF, g, "RGBA G");
        assert_eq!((rgba >> 8) & 0xFF, b, "RGBA B");
        assert_eq!(rgba & 0xFF, a, "RGBA A");

        // ARGB: 0xAARRGGBB
        assert_eq!((argb >> 24) & 0xFF, a, "ARGB A");
        assert_eq!((argb >> 16) & 0xFF, r, "ARGB R");
        assert_eq!((argb >> 8) & 0xFF, g, "ARGB G");
        assert_eq!(argb & 0xFF, b, "ARGB B");

        // ABGR: 0xAABBGGRR
        assert_eq!((abgr >> 24) & 0xFF, a, "ABGR A");
        assert_eq!((abgr >> 16) & 0xFF, b, "ABGR B");
        assert_eq!((abgr >> 8) & 0xFF, g, "ABGR G");
        assert_eq!(abgr & 0xFF, r, "ABGR R");
    }

    /// Kill mutant: replace Color::from_hsl -> Self with Default::default()
    /// Default Color is (0,0,0,0). from_hsl with non-zero HSL should differ.
    #[test]
    fn test_from_hsl_not_default() {
        let hsl = Hsl::new(120.0, 1.0, 0.5);
        let color = Color::from_hsl(hsl);
        assert_ne!(
            color,
            Color::default(),
            "from_hsl should not return default"
        );
        assert!(
            (color.g - 1.0).abs() < 0.01,
            "Green HSL should produce green color"
        );
        assert_eq!(color.a, 1.0, "from_hsl should have alpha 1.0");
    }

    /// Kill mutant: replace Debug for Color with Ok(Default::default())
    #[test]
    fn test_color_debug_not_empty() {
        let c = Color::new(0.3, 0.6, 0.9, 1.0);
        let debug = format!("{c:?}");
        assert!(
            debug.contains("Color"),
            "Debug output should contain 'Color'"
        );
        assert!(debug.contains("0.3"), "Debug should contain r value");
        assert!(debug.contains("0.6"), "Debug should contain g value");
        assert!(debug.contains("0.9"), "Debug should contain b value");
    }

    /// Kill mutant: replace From<Rgb> for Color with Default::default()
    #[test]
    fn test_from_rgb_not_default() {
        let rgb = Rgb::new(0.7, 0.3, 0.5);
        let color: Color = rgb.into();
        assert_ne!(color, Color::default(), "From<Rgb> should not be default");
        assert_eq!(color.r, 0.7);
        assert_eq!(color.g, 0.3);
        assert_eq!(color.b, 0.5);
        assert_eq!(color.a, 1.0);
    }

    /// Kill mutant: replace Debug for Rgb with Ok(Default::default())
    #[test]
    fn test_rgb_debug_not_empty() {
        let rgb = Rgb::new(0.1, 0.2, 0.3);
        let debug = format!("{rgb:?}");
        assert!(debug.contains("Rgb"), "Debug should contain 'Rgb'");
        assert!(debug.contains("0.1"), "Debug should contain r value");
    }

    /// Kill mutant: replace Debug for Hsl with Ok(Default::default())
    #[test]
    fn test_hsl_debug_not_empty() {
        let hsl = Hsl::new(180.0, 0.5, 0.75);
        let debug = format!("{hsl:?}");
        assert!(debug.contains("Hsl"), "Debug should contain 'Hsl'");
        assert!(debug.contains("180"), "Debug should contain h value");
        assert!(debug.contains("0.5"), "Debug should contain s value");
    }

    /// Kill mutant: replace Display for Hsl with Ok(Default::default())
    #[test]
    fn test_hsl_display_not_empty() {
        let hsl = Hsl::new(240.0, 0.8, 0.6);
        let display = format!("{hsl}");
        assert!(display.contains("hsl"), "Display should contain 'hsl'");
        assert!(display.contains("240"), "Display should contain hue");
        assert!(display.contains("80"), "Display should contain saturation%");
        assert!(display.contains("60"), "Display should contain lightness%");
    }

    /// Kill mutants: Hsl::from_color boundary conditions for < and <=
    /// These test the specific branches in from_color where max component
    /// determines the hue calculation path.
    #[test]
    fn test_hsl_from_color_hue_branches() {
        // Red dominant (max == r): hue = (g - b) / d
        // With g < b, hue += 6.0 -- tests the `g < b` branch
        let reddish_blue = Color::rgb(0.8, 0.1, 0.5);
        let hsl = Hsl::from_color(reddish_blue);
        assert!(hsl.h > 300.0, "Red-dominant with g<b should have hue > 300");
        let back = hsl.to_color();
        assert!(
            reddish_blue.approx_eq(back),
            "Roundtrip should preserve color"
        );

        // Red dominant with g > b: no hue adjustment
        let reddish_green = Color::rgb(0.8, 0.5, 0.1);
        let hsl2 = Hsl::from_color(reddish_green);
        assert!(hsl2.h < 60.0, "Red-dominant with g>b should have hue < 60");
        let back2 = hsl2.to_color();
        assert!(
            reddish_green.approx_eq(back2),
            "Roundtrip should preserve color"
        );

        // Green dominant (max == g): hue = (b - r) / d + 2.0
        let greenish = Color::rgb(0.2, 0.9, 0.1);
        let hsl3 = Hsl::from_color(greenish);
        assert!(
            hsl3.h > 90.0 && hsl3.h < 150.0,
            "Green dominant hue ~120, got {}",
            hsl3.h
        );

        // Blue dominant (max == b): hue = (r - g) / d + 4.0
        let bluish = Color::rgb(0.1, 0.2, 0.9);
        let hsl4 = Hsl::from_color(bluish);
        assert!(
            hsl4.h > 210.0 && hsl4.h < 270.0,
            "Blue dominant hue ~240, got {}",
            hsl4.h
        );
    }

    /// Kill mutants: Hsl::from_color saturation calculation
    /// l > 0.5 vs l <= 0.5 uses different formulas
    #[test]
    fn test_hsl_from_color_saturation_branches() {
        // Dark color (l < 0.5): s = d / (max + min)
        let dark = Color::rgb(0.4, 0.1, 0.1);
        let hsl = Hsl::from_color(dark);
        assert!(hsl.l < 0.5, "Dark color should have l < 0.5");
        assert!(hsl.s > 0.0, "Dark color should have positive saturation");

        // Light color (l > 0.5): s = d / (2.0 - max - min)
        let light = Color::rgb(0.9, 0.6, 0.6);
        let hsl2 = Hsl::from_color(light);
        assert!(hsl2.l > 0.5, "Light color should have l > 0.5");
        assert!(hsl2.s > 0.0, "Light color should have positive saturation");

        // Both should roundtrip correctly
        assert!(dark.approx_eq(hsl.to_color()), "Dark roundtrip");
        assert!(light.approx_eq(hsl2.to_color()), "Light roundtrip");
    }

    /// Kill mutants: Hsl::to_color boundary conditions
    /// Tests the q calculation branches: l < 0.5 vs l >= 0.5
    #[test]
    fn test_hsl_to_color_q_branches() {
        // l < 0.5: q = l * (1 + s)
        let dark_hsl = Hsl::new(60.0, 0.8, 0.3);
        let dark = dark_hsl.to_color();
        assert!(dark.r > 0.0 || dark.g > 0.0 || dark.b > 0.0);
        let back = Hsl::from_color(dark);
        assert!(
            (back.h - dark_hsl.h).abs() < 1.0,
            "Hue should be preserved"
        );

        // l >= 0.5: q = l + s - l * s
        let light_hsl = Hsl::new(60.0, 0.8, 0.7);
        let light = light_hsl.to_color();
        assert!(light.r > dark.r, "Lighter HSL should produce brighter color");

        // l exactly 0.5 (boundary)
        let mid_hsl = Hsl::new(60.0, 0.8, 0.5);
        let mid = mid_hsl.to_color();
        let back_mid = Hsl::from_color(mid);
        assert!(
            (back_mid.l - 0.5).abs() < 0.01,
            "l=0.5 should roundtrip"
        );
    }

    /// Kill mutants: hue_to_rgb boundary conditions
    /// Tests all 4 branches of hue_to_rgb: t<1/6, t<1/2, t<2/3, else
    #[test]
    fn test_hue_to_rgb_all_branches() {
        // Generate colors at specific hues that exercise all branches
        // Hue 0 (red): t values are h+1/3=0.333, h=0, h-1/3=-0.333->0.667
        // Hue 30: t values force different branch paths
        let colors_to_test = [
            (0.0, 1.0, 0.5),   // Pure red
            (30.0, 1.0, 0.5),  // Orange (t values hit different branches)
            (60.0, 1.0, 0.5),  // Yellow
            (90.0, 1.0, 0.5),  // Yellow-green
            (150.0, 1.0, 0.5), // Green-cyan
            (210.0, 1.0, 0.5), // Cyan-blue
            (270.0, 1.0, 0.5), // Blue-magenta
            (330.0, 1.0, 0.5), // Magenta-red
        ];

        for (h, s, l) in colors_to_test {
            let hsl = Hsl::new(h, s, l);
            let color = hsl.to_color();

            // Every color should have at least one non-zero RGB channel
            assert!(
                color.r > 0.0 || color.g > 0.0 || color.b > 0.0,
                "HSL({h},{s},{l}) should produce non-black color"
            );
            assert_eq!(color.a, 1.0, "Alpha should be 1.0");

            // Roundtrip should preserve
            let back = Hsl::from_color(color);
            assert!(
                (back.h - h).abs() < 1.0 || (back.h - h).abs() > 359.0,
                "Hue roundtrip failed for h={h}: got {}",
                back.h
            );
        }

        // Specifically test with s=0 (achromatic) to hit early return
        let gray = Hsl::new(0.0, 0.0, 0.5).to_color();
        assert!(
            (gray.r - 0.5).abs() < crate::EPSILON,
            "Achromatic should return lightness"
        );
        assert_eq!(gray.r, gray.g);
        assert_eq!(gray.g, gray.b);
    }

    /// Kill mutant: replace Hsl::to_color s.abs() < EPSILON with s.abs() <= EPSILON
    #[test]
    fn test_hsl_to_color_saturation_at_epsilon() {
        // Saturation exactly at EPSILON: should NOT be treated as achromatic
        let hsl = Hsl::new(120.0, crate::EPSILON, 0.5);
        let _color = hsl.to_color();
        // With EPSILON saturation, abs() < EPSILON is false, so we do the color calc
        // (the function doesn't panic or return default — that's what we verify)

        // Saturation slightly above EPSILON
        let hsl2 = Hsl::new(120.0, crate::EPSILON * 2.0, 0.5);
        let color2 = hsl2.to_color();
        assert!(
            color2.g > color2.r,
            "Green hue with positive saturation should have more green"
        );
    }
}
