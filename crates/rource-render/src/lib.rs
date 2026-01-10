//! # Rource Render
//!
//! Rendering abstraction and software rasterizer for Rource.
//!
//! This crate provides a multi-backend rendering architecture with:
//! - A common [`Renderer`] trait for all backends
//! - A pure-CPU [`SoftwareRenderer`] for maximum portability
//! - Draw command batching for performance
//! - Font rendering via fontdue
//!
//! ## Example
//!
//! ```
//! use rource_render::{Renderer, SoftwareRenderer};
//! use rource_math::{Color, Vec2};
//!
//! let mut renderer = SoftwareRenderer::new(800, 600);
//!
//! renderer.begin_frame();
//! renderer.clear(Color::BLACK);
//! renderer.draw_disc(Vec2::new(400.0, 300.0), 50.0, Color::WHITE);
//! renderer.end_frame();
//!
//! // Access the pixel buffer
//! let pixels = renderer.pixels();
//! ```

pub mod backend;
pub mod command;
pub mod default_font;
pub mod effects;
pub mod font;
pub mod texture;

pub use backend::software::SoftwareRenderer;
pub use command::{DrawCommand, DrawQueue};
pub use font::FontCache;
pub use texture::{Texture, TextureId};

use rource_math::{Bounds, Color, Mat4, Vec2};

/// A unique identifier for fonts in the renderer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct FontId(u32);

impl FontId {
    /// Creates a new font ID.
    #[inline]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Returns the raw ID value.
    #[inline]
    pub const fn raw(self) -> u32 {
        self.0
    }
}

/// The core rendering trait implemented by all backends.
///
/// This trait defines the interface for drawing primitives that the
/// visualization uses. Implementations may be CPU-based (software rasterizer)
/// or GPU-accelerated (WebGL2).
pub trait Renderer {
    /// Begins a new frame. Call this before any draw calls.
    fn begin_frame(&mut self);

    /// Ends the current frame and presents/flushes the results.
    fn end_frame(&mut self);

    /// Clears the framebuffer with the given color.
    fn clear(&mut self, color: Color);

    /// Draws an outlined circle (ring).
    ///
    /// # Arguments
    /// * `center` - Center point in world coordinates
    /// * `radius` - Radius of the circle
    /// * `width` - Line width of the outline
    /// * `color` - Color of the circle outline
    fn draw_circle(&mut self, center: Vec2, radius: f32, width: f32, color: Color);

    /// Draws a filled circle (disc).
    ///
    /// # Arguments
    /// * `center` - Center point in world coordinates
    /// * `radius` - Radius of the disc
    /// * `color` - Fill color
    fn draw_disc(&mut self, center: Vec2, radius: f32, color: Color);

    /// Draws a line segment with the given width.
    ///
    /// # Arguments
    /// * `start` - Start point in world coordinates
    /// * `end` - End point in world coordinates
    /// * `width` - Line width in pixels
    /// * `color` - Line color
    fn draw_line(&mut self, start: Vec2, end: Vec2, width: f32, color: Color);

    /// Draws a spline curve through the given control points.
    ///
    /// # Arguments
    /// * `points` - Control points for the spline
    /// * `width` - Line width
    /// * `color` - Spline color
    fn draw_spline(&mut self, points: &[Vec2], width: f32, color: Color);

    /// Draws a textured or colored quad.
    ///
    /// # Arguments
    /// * `bounds` - The bounding box of the quad
    /// * `texture` - Optional texture ID (None for solid color)
    /// * `color` - Color to multiply with texture (or solid fill if no texture)
    fn draw_quad(&mut self, bounds: Bounds, texture: Option<TextureId>, color: Color);

    /// Draws text at the given position.
    ///
    /// # Arguments
    /// * `text` - The text to render
    /// * `position` - Top-left corner position
    /// * `font` - Font ID to use
    /// * `size` - Font size in pixels
    /// * `color` - Text color
    fn draw_text(&mut self, text: &str, position: Vec2, font: FontId, size: f32, color: Color);

    /// Sets the current transformation matrix.
    ///
    /// The transform is applied to all subsequent draw calls until changed.
    fn set_transform(&mut self, transform: Mat4);

    /// Gets the current transformation matrix.
    fn transform(&self) -> Mat4;

    /// Pushes a clipping rectangle onto the clip stack.
    ///
    /// Drawing is restricted to the intersection of all active clip bounds.
    fn push_clip(&mut self, bounds: Bounds);

    /// Pops the top clipping rectangle from the stack.
    fn pop_clip(&mut self);

    /// Returns the current viewport width.
    fn width(&self) -> u32;

    /// Returns the current viewport height.
    fn height(&self) -> u32;

    /// Resizes the rendering viewport.
    fn resize(&mut self, width: u32, height: u32);

    /// Loads a texture from raw RGBA8 data.
    ///
    /// Returns a texture ID that can be used with `draw_quad`.
    fn load_texture(&mut self, width: u32, height: u32, data: &[u8]) -> TextureId;

    /// Unloads a previously loaded texture.
    fn unload_texture(&mut self, texture: TextureId);

    /// Loads a font from raw data.
    ///
    /// Returns a font ID that can be used with `draw_text`.
    fn load_font(&mut self, data: &[u8]) -> Option<FontId>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_font_id_new() {
        let id = FontId::new(42);
        assert_eq!(id.raw(), 42);
    }

    #[test]
    fn test_font_id_default() {
        let id = FontId::default();
        assert_eq!(id.raw(), 0);
    }
}
