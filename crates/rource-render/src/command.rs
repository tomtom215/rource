//! Draw command batching system.
//!
//! Draw commands represent individual drawing operations that can be
//! batched and sorted for optimal rendering performance.

use rource_math::{Bounds, Color, Vec2};

use crate::{FontId, TextureId};

/// A single draw command representing a primitive to render.
///
/// Each variant represents a different drawing operation with its parameters.
/// Commands can be batched and sorted using [`DrawQueue`] for optimal rendering.
#[derive(Debug, Clone)]
#[allow(missing_docs)] // Fields are self-explanatory from variant docs
pub enum DrawCommand {
    /// Clear the framebuffer
    Clear { color: Color },

    /// Draw an outlined circle
    Circle {
        center: Vec2,
        radius: f32,
        width: f32,
        color: Color,
    },

    /// Draw a filled circle
    Disc { center: Vec2, radius: f32, color: Color },

    /// Draw a line segment
    Line {
        start: Vec2,
        end: Vec2,
        width: f32,
        color: Color,
    },

    /// Draw a spline curve
    Spline {
        points: Vec<Vec2>,
        width: f32,
        color: Color,
    },

    /// Draw a textured or colored quad
    Quad {
        bounds: Bounds,
        texture: Option<TextureId>,
        color: Color,
    },

    /// Draw text
    Text {
        text: String,
        position: Vec2,
        font: FontId,
        size: f32,
        color: Color,
    },
}

impl DrawCommand {
    /// Returns the sort key for this command.
    ///
    /// Commands are sorted by:
    /// 1. Texture batch (to minimize texture switches)
    /// 2. Blend mode (opaque before transparent)
    /// 3. Z-order
    #[inline]
    pub fn sort_key(&self) -> u64 {
        match self {
            Self::Clear { .. } => 0,
            Self::Quad { texture, color, .. } => {
                let tex_id = texture.map_or(0, |t| u64::from(t.raw()));
                let blend = if color.a < 1.0 { 1u64 << 32 } else { 0 };
                tex_id | blend | (2 << 48)
            }
            Self::Disc { color, .. } => {
                let blend = if color.a < 1.0 { 1u64 << 32 } else { 0 };
                blend | (3 << 48)
            }
            Self::Circle { color, .. } => {
                let blend = if color.a < 1.0 { 1u64 << 32 } else { 0 };
                blend | (4 << 48)
            }
            Self::Line { color, .. } => {
                let blend = if color.a < 1.0 { 1u64 << 32 } else { 0 };
                blend | (5 << 48)
            }
            Self::Spline { color, .. } => {
                let blend = if color.a < 1.0 { 1u64 << 32 } else { 0 };
                blend | (6 << 48)
            }
            Self::Text { .. } => 7 << 48, // Text always last (usually transparent)
        }
    }

    /// Returns true if this command requires alpha blending.
    #[inline]
    pub fn needs_blend(&self) -> bool {
        match self {
            Self::Clear { .. } => false,
            Self::Circle { color, .. }
            | Self::Disc { color, .. }
            | Self::Line { color, .. }
            | Self::Spline { color, .. }
            | Self::Quad { color, .. }
            | Self::Text { color, .. } => color.a < 1.0,
        }
    }
}

/// A queue of draw commands to be processed.
#[derive(Debug, Default, Clone)]
pub struct DrawQueue {
    commands: Vec<DrawCommand>,
}

impl DrawQueue {
    /// Creates a new empty draw queue.
    #[inline]
    pub fn new() -> Self {
        Self {
            commands: Vec::new(),
        }
    }

    /// Creates a draw queue with the given capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            commands: Vec::with_capacity(capacity),
        }
    }

    /// Pushes a draw command onto the queue.
    #[inline]
    pub fn push(&mut self, command: DrawCommand) {
        self.commands.push(command);
    }

    /// Clears all commands from the queue.
    #[inline]
    pub fn clear(&mut self) {
        self.commands.clear();
    }

    /// Returns the number of commands in the queue.
    #[inline]
    pub fn len(&self) -> usize {
        self.commands.len()
    }

    /// Returns true if the queue is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.commands.is_empty()
    }

    /// Sorts commands for optimal rendering order.
    ///
    /// This groups commands by texture and blend mode to minimize
    /// state changes during rendering.
    pub fn sort(&mut self) {
        self.commands.sort_by_key(DrawCommand::sort_key);
    }

    /// Returns an iterator over the commands.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &DrawCommand> {
        self.commands.iter()
    }

    /// Drains all commands from the queue.
    #[inline]
    pub fn drain(&mut self) -> impl Iterator<Item = DrawCommand> + '_ {
        self.commands.drain(..)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_draw_queue_new() {
        let queue = DrawQueue::new();
        assert!(queue.is_empty());
        assert_eq!(queue.len(), 0);
    }

    #[test]
    fn test_draw_queue_push() {
        let mut queue = DrawQueue::new();
        queue.push(DrawCommand::Clear {
            color: Color::BLACK,
        });
        assert_eq!(queue.len(), 1);
        assert!(!queue.is_empty());
    }

    #[test]
    fn test_draw_queue_clear() {
        let mut queue = DrawQueue::new();
        queue.push(DrawCommand::Clear {
            color: Color::BLACK,
        });
        queue.push(DrawCommand::Disc {
            center: Vec2::ZERO,
            radius: 10.0,
            color: Color::WHITE,
        });
        assert_eq!(queue.len(), 2);

        queue.clear();
        assert!(queue.is_empty());
    }

    #[test]
    fn test_draw_command_sort_key() {
        let clear = DrawCommand::Clear {
            color: Color::BLACK,
        };
        let disc = DrawCommand::Disc {
            center: Vec2::ZERO,
            radius: 10.0,
            color: Color::WHITE,
        };
        let text = DrawCommand::Text {
            text: "test".to_string(),
            position: Vec2::ZERO,
            font: FontId::default(),
            size: 12.0,
            color: Color::WHITE,
        };

        // Clear should come first
        assert!(clear.sort_key() < disc.sort_key());
        // Text should come last
        assert!(disc.sort_key() < text.sort_key());
    }

    #[test]
    fn test_draw_queue_sort() {
        let mut queue = DrawQueue::new();

        queue.push(DrawCommand::Text {
            text: "test".to_string(),
            position: Vec2::ZERO,
            font: FontId::default(),
            size: 12.0,
            color: Color::WHITE,
        });
        queue.push(DrawCommand::Clear {
            color: Color::BLACK,
        });
        queue.push(DrawCommand::Disc {
            center: Vec2::ZERO,
            radius: 10.0,
            color: Color::WHITE,
        });

        queue.sort();

        let commands: Vec<_> = queue.iter().collect();
        assert!(matches!(commands[0], DrawCommand::Clear { .. }));
        assert!(matches!(commands[1], DrawCommand::Disc { .. }));
        assert!(matches!(commands[2], DrawCommand::Text { .. }));
    }

    #[test]
    fn test_draw_command_needs_blend() {
        let opaque = DrawCommand::Disc {
            center: Vec2::ZERO,
            radius: 10.0,
            color: Color::WHITE,
        };
        assert!(!opaque.needs_blend());

        let transparent = DrawCommand::Disc {
            center: Vec2::ZERO,
            radius: 10.0,
            color: Color::WHITE.with_alpha(0.5),
        };
        assert!(transparent.needs_blend());
    }

    #[test]
    fn test_draw_queue_drain() {
        let mut queue = DrawQueue::new();
        queue.push(DrawCommand::Clear {
            color: Color::BLACK,
        });
        queue.push(DrawCommand::Disc {
            center: Vec2::ZERO,
            radius: 10.0,
            color: Color::WHITE,
        });

        assert_eq!(queue.drain().count(), 2);
        assert!(queue.is_empty());
    }
}
