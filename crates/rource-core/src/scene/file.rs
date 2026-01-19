//! File entity for the visualization.
//!
//! Files are represented as nodes that belong to directories and can
//! be modified by user actions (create, modify, delete).

use std::path::{Path, PathBuf};

use rource_math::{Color, Hsl, Vec2};

use crate::entity::{DirId, FileId};

/// How fast files fade in/out (per second).
pub const FADE_RATE: f32 = 2.0;

/// Default visual radius for files.
pub const DEFAULT_FILE_RADIUS: f32 = 5.0;

/// Duration of touch effect (seconds).
pub const TOUCH_DURATION: f32 = 1.0;

/// A file entity in the scene.
///
/// Files are visual nodes that represent source files in the repository.
/// They have position, color (based on extension), and can show temporary
/// "touch" effects when modified.
#[derive(Debug, Clone)]
pub struct FileNode {
    /// The file ID.
    id: FileId,

    /// File name (not full path).
    name: String,

    /// Full path from repository root.
    path: PathBuf,

    /// File extension (for coloring).
    extension: Option<String>,

    /// Parent directory.
    directory: DirId,

    /// Position in 2D space.
    position: Vec2,

    /// Target position (for layout animation).
    target: Vec2,

    /// Visual radius.
    radius: f32,

    /// Base color (from extension).
    color: Color,

    /// Touch color (temporary after action).
    touch_color: Option<Color>,

    /// Touch fade timer (0.0 to 1.0).
    touch_time: f32,

    /// Visibility alpha (0.0 = invisible, 1.0 = fully visible).
    alpha: f32,

    /// Is being removed (fading out).
    removing: bool,

    /// Time since last modification.
    idle_time: f32,

    /// Whether this file is pinned (fixed in place).
    pinned: bool,

    /// Whether this file is highlighted (hovered/selected).
    highlighted: bool,
}

impl FileNode {
    /// Creates a new file node.
    #[must_use]
    pub fn new(id: FileId, path: impl Into<PathBuf>, directory: DirId) -> Self {
        let path = path.into();
        let name = path
            .file_name()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_default();
        let extension = path.extension().map(|s| s.to_string_lossy().to_string());

        let color = extension
            .as_ref()
            .map_or(Color::GRAY, |ext| Self::color_from_extension(ext));

        Self {
            id,
            name,
            path,
            extension,
            directory,
            position: Vec2::ZERO,
            target: Vec2::ZERO,
            radius: DEFAULT_FILE_RADIUS,
            color,
            touch_color: None,
            touch_time: 0.0,
            alpha: 0.0, // Start invisible, fade in
            removing: false,
            idle_time: 0.0,
            pinned: false,
            highlighted: false,
        }
    }

    /// Returns the file ID.
    #[inline]
    #[must_use]
    pub const fn id(&self) -> FileId {
        self.id
    }

    /// Returns the file name.
    #[inline]
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the full path.
    #[inline]
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Returns the file extension, if any.
    #[inline]
    #[must_use]
    pub fn extension(&self) -> Option<&str> {
        self.extension.as_deref()
    }

    /// Returns the parent directory ID.
    #[inline]
    #[must_use]
    pub const fn directory(&self) -> DirId {
        self.directory
    }

    /// Returns the current position.
    #[inline]
    #[must_use]
    pub const fn position(&self) -> Vec2 {
        self.position
    }

    /// Sets the position.
    #[inline]
    pub fn set_position(&mut self, position: Vec2) {
        self.position = position;
    }

    /// Returns the target position.
    #[inline]
    #[must_use]
    pub const fn target(&self) -> Vec2 {
        self.target
    }

    /// Sets the target position.
    #[inline]
    pub fn set_target(&mut self, target: Vec2) {
        self.target = target;
    }

    /// Returns the visual radius.
    #[inline]
    #[must_use]
    pub const fn radius(&self) -> f32 {
        self.radius
    }

    /// Sets the visual radius.
    #[inline]
    pub fn set_radius(&mut self, radius: f32) {
        self.radius = radius.max(1.0);
    }

    /// Returns the base color.
    #[inline]
    #[must_use]
    pub const fn color(&self) -> Color {
        self.color
    }

    /// Sets the base color.
    #[inline]
    pub fn set_color(&mut self, color: Color) {
        self.color = color;
    }

    /// Returns the current alpha (visibility).
    #[inline]
    #[must_use]
    pub const fn alpha(&self) -> f32 {
        self.alpha
    }

    /// Returns true if this file is being removed.
    #[inline]
    #[must_use]
    pub const fn is_removing(&self) -> bool {
        self.removing
    }

    /// Returns the time since last modification.
    #[inline]
    #[must_use]
    pub const fn idle_time(&self) -> f32 {
        self.idle_time
    }

    /// Returns the current touch time (0.0 to 1.0).
    #[inline]
    #[must_use]
    pub const fn touch_time(&self) -> f32 {
        self.touch_time
    }

    /// Returns whether this file is pinned (fixed in place).
    #[inline]
    #[must_use]
    pub const fn is_pinned(&self) -> bool {
        self.pinned
    }

    /// Sets whether this file is pinned.
    #[inline]
    pub fn set_pinned(&mut self, pinned: bool) {
        self.pinned = pinned;
    }

    /// Returns whether this file is highlighted.
    #[inline]
    #[must_use]
    pub const fn is_highlighted(&self) -> bool {
        self.highlighted
    }

    /// Sets whether this file is highlighted.
    #[inline]
    pub fn set_highlighted(&mut self, highlighted: bool) {
        self.highlighted = highlighted;
    }

    /// Gets the color for a file extension.
    ///
    /// This provides consistent colors for common file types.
    #[must_use]
    pub fn color_from_extension(ext: &str) -> Color {
        match ext.to_lowercase().as_str() {
            // Rust
            "rs" => Color::from_rgb8(222, 165, 132),

            // JavaScript/TypeScript
            "js" | "mjs" | "cjs" => Color::from_rgb8(247, 223, 30),
            "ts" | "mts" | "cts" => Color::from_rgb8(49, 120, 198),
            "jsx" | "tsx" => Color::from_rgb8(97, 218, 251),

            // Python
            "py" | "pyi" | "pyw" => Color::from_rgb8(53, 114, 165),

            // Go
            "go" => Color::from_rgb8(0, 173, 216),

            // Java/Kotlin
            "java" => Color::from_rgb8(176, 114, 25),
            "kt" | "kts" => Color::from_rgb8(167, 139, 250),

            // C/C++
            "c" | "h" => Color::from_rgb8(85, 85, 255),
            "cpp" | "cc" | "cxx" | "hpp" | "hxx" | "hh" => Color::from_rgb8(0, 89, 156),

            // C#
            "cs" => Color::from_rgb8(155, 79, 150),

            // Web
            "html" | "htm" => Color::from_rgb8(227, 76, 38),
            "css" => Color::from_rgb8(86, 61, 124),
            "scss" | "sass" | "less" => Color::from_rgb8(205, 103, 153),
            "vue" => Color::from_rgb8(65, 184, 131),
            "svelte" => Color::from_rgb8(255, 62, 0),

            // Data/Config
            "json" => Color::from_rgb8(128, 128, 128),
            "yaml" | "yml" => Color::from_rgb8(203, 23, 30),
            "toml" => Color::from_rgb8(156, 66, 33),
            "xml" => Color::from_rgb8(0, 96, 172),
            "ini" | "cfg" | "conf" => Color::from_rgb8(160, 160, 160),

            // Documentation
            "md" | "markdown" => Color::from_rgb8(200, 200, 200),
            "txt" | "text" => Color::from_rgb8(180, 180, 180),
            "rst" => Color::from_rgb8(141, 85, 36),

            // Shell
            "sh" | "bash" | "zsh" | "fish" => Color::from_rgb8(0, 128, 0),
            "ps1" | "psm1" => Color::from_rgb8(1, 36, 86),
            "bat" | "cmd" => Color::from_rgb8(0, 100, 0),

            // Database
            "sql" => Color::from_rgb8(255, 128, 0),

            // Ruby
            "rb" | "rake" | "gemspec" => Color::from_rgb8(204, 52, 45),

            // PHP
            "php" => Color::from_rgb8(119, 123, 179),

            // Swift
            "swift" => Color::from_rgb8(240, 81, 56),

            // Elixir/Erlang
            "ex" | "exs" => Color::from_rgb8(110, 74, 126),
            "erl" | "hrl" => Color::from_rgb8(184, 57, 80),

            // Haskell
            "hs" | "lhs" => Color::from_rgb8(94, 80, 134),

            // Scala
            "scala" | "sc" => Color::from_rgb8(220, 50, 47),

            // Clojure
            "clj" | "cljs" | "cljc" => Color::from_rgb8(99, 177, 243),

            // Lua
            "lua" => Color::from_rgb8(0, 0, 128),

            // R
            "r" => Color::from_rgb8(25, 140, 231),

            // Default: generate from extension hash
            _ => {
                let hash = ext.bytes().fold(0u32, |acc, b| {
                    acc.wrapping_mul(31).wrapping_add(u32::from(b))
                });
                let hue = (hash % 360) as f32;
                Color::from_hsl(Hsl::new(hue, 0.5, 0.5))
            }
        }
    }

    /// Applies a touch effect to the file (from an action).
    ///
    /// The touch color will fade over time.
    pub fn touch(&mut self, color: Color) {
        self.touch_color = Some(color);
        self.touch_time = TOUCH_DURATION;
        self.idle_time = 0.0;
    }

    /// Marks this file for removal (it will fade out).
    pub fn mark_for_removal(&mut self) {
        self.removing = true;
    }

    /// Updates the file state.
    ///
    /// This handles:
    /// - Touch effect fading
    /// - Idle time tracking
    /// - Fade in/out animation
    /// - Position interpolation towards target
    pub fn update(&mut self, dt: f32) {
        // Update touch fade
        if self.touch_time > 0.0 {
            self.touch_time = (self.touch_time - dt).max(0.0);
            if self.touch_time == 0.0 {
                self.touch_color = None;
            }
        }

        // Update idle time
        self.idle_time += dt;

        // Fade in/out
        if self.removing {
            self.alpha = (self.alpha - FADE_RATE * dt).max(0.0);
        } else {
            self.alpha = (self.alpha + FADE_RATE * dt).min(1.0);
        }

        // Move towards target
        let delta = self.target - self.position;
        let distance = delta.length();
        if distance > 0.1 {
            // Smooth interpolation (lerp towards target)
            let t = (dt * 5.0).min(1.0);
            self.position = self.position.lerp(self.target, t);
        } else {
            self.position = self.target;
        }
    }

    /// Gets the current display color, including touch effect.
    #[must_use]
    pub fn current_color(&self) -> Color {
        self.touch_color.map_or(self.color, |touch| {
            // Lerp from touch color back to base color as touch_time decreases
            let t = self.touch_time / TOUCH_DURATION;
            self.color.lerp(touch, t)
        })
    }

    /// Returns true if the file has fully faded out and can be removed.
    #[must_use]
    pub fn should_remove(&self) -> bool {
        self.removing && self.alpha <= 0.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_file_node_new() {
        let id = FileId::from_index(0);
        let dir_id = DirId::from_index(0);
        let file = FileNode::new(id, "src/main.rs", dir_id);

        assert_eq!(file.id(), id);
        assert_eq!(file.name(), "main.rs");
        assert_eq!(file.path(), Path::new("src/main.rs"));
        assert_eq!(file.extension(), Some("rs"));
        assert_eq!(file.directory(), dir_id);
        assert_eq!(file.alpha(), 0.0); // Starts invisible
    }

    #[test]
    fn test_file_node_no_extension() {
        let id = FileId::from_index(0);
        let dir_id = DirId::from_index(0);
        let file = FileNode::new(id, "Makefile", dir_id);

        assert_eq!(file.name(), "Makefile");
        assert_eq!(file.extension(), None);
        assert_eq!(file.color(), Color::GRAY);
    }

    #[test]
    fn test_file_node_color_from_extension() {
        // Test some known extensions
        let rust_color = FileNode::color_from_extension("rs");
        assert_eq!(rust_color, Color::from_rgb8(222, 165, 132));

        let js_color = FileNode::color_from_extension("js");
        assert_eq!(js_color, Color::from_rgb8(247, 223, 30));

        let py_color = FileNode::color_from_extension("py");
        assert_eq!(py_color, Color::from_rgb8(53, 114, 165));

        // Test case insensitivity
        let ts_lower = FileNode::color_from_extension("ts");
        let ts_upper = FileNode::color_from_extension("TS");
        assert_eq!(ts_lower, ts_upper);
    }

    #[test]
    fn test_file_node_color_unknown_extension() {
        // Unknown extensions should get a deterministic color from hash
        let color1 = FileNode::color_from_extension("xyz123");
        let color2 = FileNode::color_from_extension("xyz123");
        assert_eq!(color1, color2);

        // Different extensions should (usually) get different colors
        let color3 = FileNode::color_from_extension("abc456");
        assert_ne!(color1, color3);
    }

    #[test]
    fn test_file_node_touch() {
        let id = FileId::from_index(0);
        let dir_id = DirId::from_index(0);
        let mut file = FileNode::new(id, "test.rs", dir_id);

        let touch_color = Color::from_rgb8(0, 255, 0);
        file.touch(touch_color);

        assert_eq!(file.touch_time(), TOUCH_DURATION);
        assert_eq!(file.idle_time(), 0.0);
        assert_eq!(file.current_color(), touch_color);
    }

    #[test]
    fn test_file_node_update_fade_in() {
        let id = FileId::from_index(0);
        let dir_id = DirId::from_index(0);
        let mut file = FileNode::new(id, "test.rs", dir_id);

        assert_eq!(file.alpha(), 0.0);

        // Update should fade in
        file.update(0.5);
        assert!(file.alpha() > 0.0);

        // Keep updating until fully visible
        for _ in 0..10 {
            file.update(0.5);
        }
        assert_eq!(file.alpha(), 1.0);
    }

    #[test]
    fn test_file_node_update_fade_out() {
        let id = FileId::from_index(0);
        let dir_id = DirId::from_index(0);
        let mut file = FileNode::new(id, "test.rs", dir_id);

        // First, fully fade in
        for _ in 0..10 {
            file.update(0.5);
        }
        assert_eq!(file.alpha(), 1.0);

        // Mark for removal
        file.mark_for_removal();
        assert!(file.is_removing());

        // Update should fade out
        file.update(0.5);
        assert!(file.alpha() < 1.0);

        // Keep updating until invisible
        for _ in 0..10 {
            file.update(0.5);
        }
        assert_eq!(file.alpha(), 0.0);
        assert!(file.should_remove());
    }

    #[test]
    fn test_file_node_update_touch_fade() {
        let id = FileId::from_index(0);
        let dir_id = DirId::from_index(0);
        let mut file = FileNode::new(id, "test.rs", dir_id);

        let touch_color = Color::from_rgb8(0, 255, 0);
        file.touch(touch_color);

        // Touch color should fade
        file.update(0.5);
        assert!(file.touch_time() < TOUCH_DURATION);

        // Eventually touch color should be gone
        for _ in 0..10 {
            file.update(0.5);
        }
        assert_eq!(file.touch_time(), 0.0);
        assert_eq!(file.current_color(), file.color());
    }

    #[test]
    fn test_file_node_update_position() {
        let id = FileId::from_index(0);
        let dir_id = DirId::from_index(0);
        let mut file = FileNode::new(id, "test.rs", dir_id);

        file.set_target(Vec2::new(100.0, 100.0));
        assert_eq!(file.position(), Vec2::ZERO);

        // Update should move towards target
        file.update(1.0);
        assert!(file.position().x > 0.0);
        assert!(file.position().y > 0.0);

        // Keep updating until at target
        for _ in 0..20 {
            file.update(0.5);
        }
        let diff = file.position() - file.target();
        assert!(diff.length() < 0.5);
    }

    #[test]
    fn test_file_node_idle_time() {
        let id = FileId::from_index(0);
        let dir_id = DirId::from_index(0);
        let mut file = FileNode::new(id, "test.rs", dir_id);

        file.update(1.0);
        assert_eq!(file.idle_time(), 1.0);

        file.update(0.5);
        assert_eq!(file.idle_time(), 1.5);

        // Touch resets idle time
        file.touch(Color::GREEN);
        assert_eq!(file.idle_time(), 0.0);
    }

    #[test]
    fn test_file_node_radius() {
        let id = FileId::from_index(0);
        let dir_id = DirId::from_index(0);
        let mut file = FileNode::new(id, "test.rs", dir_id);

        assert_eq!(file.radius(), DEFAULT_FILE_RADIUS);

        file.set_radius(10.0);
        assert_eq!(file.radius(), 10.0);

        // Minimum radius is 1.0
        file.set_radius(0.0);
        assert_eq!(file.radius(), 1.0);
    }
}
