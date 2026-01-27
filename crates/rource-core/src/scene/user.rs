// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! User/contributor entity for the visualization.
//!
//! Users represent contributors who have made commits to the repository.
//! They move around the scene and perform actions on files.

use rource_math::{Color, Hsl, Vec2};

use crate::entity::{ActionId, UserId};

/// Movement speed for users (units per second).
pub const USER_SPEED: f32 = 200.0;

/// Threshold for idle fade (seconds without action).
pub const IDLE_THRESHOLD: f32 = 30.0;

/// How fast users fade in/out (per second).
pub const FADE_RATE: f32 = 2.0;

/// Minimum alpha for idle users (so they remain visible).
pub const MIN_IDLE_ALPHA: f32 = 0.3;

/// Default visual radius for users.
pub const DEFAULT_USER_RADIUS: f32 = 15.0;

/// A user/contributor entity in the scene.
///
/// Users represent people who have committed to the repository.
/// They move around the scene and interact with files through actions.
#[derive(Debug, Clone)]
pub struct User {
    /// The user ID.
    id: UserId,

    /// Display name.
    name: String,

    /// Position in 2D space.
    position: Vec2,

    /// Target position (for smooth movement).
    target: Option<Vec2>,

    /// Velocity.
    velocity: Vec2,

    /// User color (derived from name hash).
    color: Color,

    /// Active actions this user is performing.
    active_actions: Vec<ActionId>,

    /// Time since last action.
    idle_time: f32,

    /// Visibility/fade state (0.0 = invisible, 1.0 = fully visible).
    alpha: f32,

    /// Is highlighted (mouse over or selected).
    highlighted: bool,

    /// Visual radius.
    radius: f32,
}

impl User {
    /// Creates a new user with the given name.
    ///
    /// The user's color is derived deterministically from their name.
    #[must_use]
    pub fn new(id: UserId, name: impl Into<String>) -> Self {
        let name = name.into();
        let color = Self::color_from_name(&name);

        Self {
            id,
            name,
            position: Vec2::ZERO,
            target: None,
            velocity: Vec2::ZERO,
            color,
            active_actions: Vec::new(),
            idle_time: 0.0,
            alpha: 0.0, // Fade in
            highlighted: false,
            radius: DEFAULT_USER_RADIUS,
        }
    }

    /// Returns the user ID.
    #[inline]
    #[must_use]
    pub const fn id(&self) -> UserId {
        self.id
    }

    /// Returns the user's name.
    #[inline]
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
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

    /// Returns the target position, if any.
    #[inline]
    #[must_use]
    pub const fn target(&self) -> Option<Vec2> {
        self.target
    }

    /// Sets the target position to move towards.
    #[inline]
    pub fn set_target(&mut self, target: Vec2) {
        self.target = Some(target);
    }

    /// Clears the target position.
    #[inline]
    pub fn clear_target(&mut self) {
        self.target = None;
    }

    /// Returns the current velocity.
    #[inline]
    #[must_use]
    pub const fn velocity(&self) -> Vec2 {
        self.velocity
    }

    /// Returns the user's color.
    #[inline]
    #[must_use]
    pub const fn color(&self) -> Color {
        self.color
    }

    /// Returns the active action IDs.
    #[inline]
    #[must_use]
    pub fn active_actions(&self) -> &[ActionId] {
        &self.active_actions
    }

    /// Returns the idle time.
    #[inline]
    #[must_use]
    pub const fn idle_time(&self) -> f32 {
        self.idle_time
    }

    /// Returns the alpha (visibility).
    #[inline]
    #[must_use]
    pub const fn alpha(&self) -> f32 {
        self.alpha
    }

    /// Returns whether the user is highlighted.
    #[inline]
    #[must_use]
    pub const fn is_highlighted(&self) -> bool {
        self.highlighted
    }

    /// Sets the highlighted state.
    #[inline]
    pub fn set_highlighted(&mut self, highlighted: bool) {
        self.highlighted = highlighted;
    }

    /// Returns the visual radius.
    #[inline]
    #[must_use]
    pub const fn radius(&self) -> f32 {
        self.radius
    }

    /// Generates a consistent color from the username.
    ///
    /// This uses a simple hash-based color generation to ensure
    /// the same user always gets the same color.
    #[must_use]
    pub fn color_from_name(name: &str) -> Color {
        let hash = name.bytes().fold(0u32, |acc, b| {
            acc.wrapping_mul(31).wrapping_add(u32::from(b))
        });

        // Use hash to generate HSL values for a pleasing color
        let hue = (hash % 360) as f32;
        let saturation = 0.6 + (((hash >> 8) % 40) as f32 / 100.0);
        let lightness = 0.5 + (((hash >> 16) % 20) as f32 / 100.0);

        Color::from_hsl(Hsl::new(hue, saturation, lightness))
    }

    /// Adds an action to the user's active actions.
    pub fn add_action(&mut self, action_id: ActionId) {
        if !self.active_actions.contains(&action_id) {
            self.active_actions.push(action_id);
        }
        self.idle_time = 0.0;
    }

    /// Removes a completed action from the user's active actions.
    pub fn remove_action(&mut self, action_id: ActionId) {
        self.active_actions.retain(|&id| id != action_id);
    }

    /// Returns true if the user has any active actions.
    #[must_use]
    pub fn is_active(&self) -> bool {
        !self.active_actions.is_empty()
    }

    /// Updates the user state.
    ///
    /// This handles:
    /// - Movement towards target
    /// - Idle time tracking
    /// - Fade in/out based on activity
    pub fn update(&mut self, dt: f32) {
        // Move towards target
        if let Some(target) = self.target {
            let direction = target - self.position;
            // Use length_squared() for threshold check to avoid sqrt when unnecessary
            let distance_sq = direction.length_squared();

            if distance_sq > 1.0 {
                // Only compute sqrt when we actually need the distance value
                let distance = distance_sq.sqrt();
                // Move towards target, speed capped by USER_SPEED
                let speed = USER_SPEED.min(distance * 2.0);
                // Normalize using precomputed distance to avoid second sqrt
                self.velocity = direction * (speed / distance);
            } else {
                // Close enough, clear target
                self.target = None;
                self.velocity = Vec2::ZERO;
            }
        } else {
            // No target, slow down
            self.velocity *= 0.9;
            // Use length_squared() to avoid sqrt (0.1² = 0.01)
            if self.velocity.length_squared() < 0.01 {
                self.velocity = Vec2::ZERO;
            }
        }

        // Integrate position
        self.position += self.velocity * dt;

        // Track idle time
        self.idle_time += dt;

        // Fade in/out based on activity
        if self.idle_time > IDLE_THRESHOLD && !self.is_active() {
            // Fade out when idle, but keep a minimum visibility
            self.alpha = (self.alpha - FADE_RATE * dt).max(MIN_IDLE_ALPHA);
        } else {
            // Fade in when active
            self.alpha = (self.alpha + FADE_RATE * dt).min(1.0);
        }
    }

    /// Resets the idle timer (called when user performs an action).
    pub fn reset_idle(&mut self) {
        self.idle_time = 0.0;
    }

    /// Returns the display color, accounting for alpha and highlight.
    #[must_use]
    pub fn display_color(&self) -> Color {
        let mut color = self.color;
        if self.highlighted {
            // Brighten when highlighted
            color = color.with_alpha(1.0);
            let hsl = color.to_hsl();
            color = Color::from_hsl(Hsl::new(hsl.h, hsl.s, (hsl.l + 0.2).min(1.0)));
        }
        color.with_alpha(self.alpha)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_user_new() {
        let id = UserId::from_index(0);
        let user = User::new(id, "John Doe");

        assert_eq!(user.id(), id);
        assert_eq!(user.name(), "John Doe");
        assert_eq!(user.position(), Vec2::ZERO);
        assert_eq!(user.target(), None);
        assert_eq!(user.alpha(), 0.0); // Starts invisible
    }

    #[test]
    fn test_user_color_from_name() {
        // Same name should produce same color
        let color1 = User::color_from_name("Alice");
        let color2 = User::color_from_name("Alice");
        assert_eq!(color1, color2);

        // Different names should (usually) produce different colors
        let color3 = User::color_from_name("Bob");
        assert_ne!(color1, color3);

        // Color should be valid HSL range
        let color = User::color_from_name("Test User");
        let hsl = color.to_hsl();
        assert!(hsl.h >= 0.0 && hsl.h < 360.0);
        assert!(hsl.s >= 0.6 && hsl.s <= 1.0);
        assert!(hsl.l >= 0.5 && hsl.l <= 0.7);
    }

    #[test]
    fn test_user_movement() {
        let id = UserId::from_index(0);
        let mut user = User::new(id, "Test");

        user.set_target(Vec2::new(100.0, 0.0));
        user.update(0.1);

        // Should be moving towards target
        assert!(user.position().x > 0.0);
        assert!(user.velocity().x > 0.0);

        // Keep moving
        for _ in 0..100 {
            user.update(0.1);
        }

        // Should be at or near target
        assert!(user.target().is_none());
        assert!((user.position().x - 100.0).abs() < 10.0);
    }

    #[test]
    fn test_user_actions() {
        let id = UserId::from_index(0);
        let mut user = User::new(id, "Test");

        let action1 = ActionId::from_index(0);
        let action2 = ActionId::from_index(1);

        user.add_action(action1);
        user.add_action(action2);
        user.add_action(action1); // Duplicate should be ignored

        assert_eq!(user.active_actions().len(), 2);
        assert!(user.is_active());

        user.remove_action(action1);
        assert_eq!(user.active_actions().len(), 1);

        user.remove_action(action2);
        assert!(!user.is_active());
    }

    #[test]
    fn test_user_idle_fade() {
        let id = UserId::from_index(0);
        let mut user = User::new(id, "Test");

        // First, fade in
        user.add_action(ActionId::from_index(0));
        for _ in 0..10 {
            user.update(0.5);
        }
        assert_eq!(user.alpha(), 1.0);

        // Remove action and wait
        user.remove_action(ActionId::from_index(0));

        // Wait past idle threshold (IDLE_THRESHOLD is 30 seconds)
        for _ in 0..70 {
            user.update(0.5);
        }

        // Should be fading out but not below MIN_IDLE_ALPHA
        assert!(user.alpha() < 1.0);
        assert!(user.alpha() >= MIN_IDLE_ALPHA);
    }

    #[test]
    fn test_user_reset_idle() {
        let id = UserId::from_index(0);
        let mut user = User::new(id, "Test");

        user.update(5.0);
        assert_eq!(user.idle_time(), 5.0);

        user.reset_idle();
        assert_eq!(user.idle_time(), 0.0);
    }

    #[test]
    fn test_user_highlight() {
        let id = UserId::from_index(0);
        let mut user = User::new(id, "Test");

        assert!(!user.is_highlighted());

        user.set_highlighted(true);
        assert!(user.is_highlighted());

        // Highlighted color should be brighter
        user.alpha = 1.0;
        let normal_color = user.color();
        user.set_highlighted(true);
        let highlighted_color = user.display_color();

        let l_normal = normal_color.to_hsl().l;
        let l_highlighted = highlighted_color.to_hsl().l;
        assert!(l_highlighted > l_normal);
    }

    #[test]
    fn test_user_display_color() {
        let id = UserId::from_index(0);
        let mut user = User::new(id, "Test");

        // Alpha should affect display color
        user.alpha = 0.5;
        let display = user.display_color();
        assert!((display.a - 0.5).abs() < 0.001);
    }

    // ===================================================================
    // Hash Distribution Tests (Phase 74 - Floyd's Algorithm Application)
    // ===================================================================

    #[test]
    fn test_color_hash_no_short_cycle() {
        const MAX_CHECK: u32 = 1_000_000;

        // Test that the hash function doesn't have short cycles when
        // iteratively applied (simulating single-byte input progression)
        //
        // f(h) = h * 31 + 0x61 ('a')
        // This tests the hash's multiplicative structure
        let f = |h: u32| h.wrapping_mul(31).wrapping_add(0x61);

        // Floyd's Tortoise and Hare for cycle detection
        let x0 = 0u32;
        let mut tortoise = f(x0);
        let mut hare = f(f(x0));
        let mut iterations = 0u32;

        while tortoise != hare && iterations < MAX_CHECK {
            tortoise = f(tortoise);
            hare = f(f(hare));
            iterations += 1;
        }

        // If we hit MAX_CHECK, no short cycle exists
        // If cycle found, calculate its length
        if tortoise == hare && iterations < MAX_CHECK {
            // Find cycle length
            let mut lambda = 1u32;
            hare = f(tortoise);
            while tortoise != hare {
                hare = f(hare);
                lambda += 1;
            }

            // Hash should have cycle > 100,000 for reasonable distribution
            assert!(
                lambda > 100_000,
                "Hash function has short cycle: {} iterations",
                lambda
            );
        }
        // No short cycle found - this is good!
    }

    #[test]
    fn test_color_hash_distribution_quality() {
        // Test that color_from_name produces well-distributed colors
        // by checking hue distribution across common names
        use std::collections::HashMap;

        let test_names = [
            "Alice",
            "Bob",
            "Charlie",
            "David",
            "Eve",
            "Frank",
            "Grace",
            "Henry",
            "Ivy",
            "Jack",
            "Kate",
            "Liam",
            "Mia",
            "Noah",
            "Olivia",
            "Paul",
            "Quinn",
            "Rose",
            "Sam",
            "Tina",
            "Uma",
            "Victor",
            "Wendy",
            "Xavier",
            "Yuki",
            "Zoe",
            "admin",
            "root",
            "user",
            "developer",
            "test",
            "bot",
            "system",
            "github-actions",
            "dependabot",
        ];

        let mut hue_buckets: HashMap<u32, u32> = HashMap::new();

        for name in &test_names {
            let color = User::color_from_name(name);
            let hsl = color.to_hsl();
            // Bucket hues into 36 buckets (10 degrees each)
            let bucket = (hsl.h / 10.0) as u32;
            *hue_buckets.entry(bucket).or_insert(0) += 1;
        }

        // Check distribution: no bucket should have more than 30% of names
        let max_per_bucket = (test_names.len() as f32 * 0.3).ceil() as u32;
        for (bucket, count) in &hue_buckets {
            assert!(
                *count <= max_per_bucket,
                "Bucket {} has {} names, exceeds 30% threshold ({})",
                bucket,
                count,
                max_per_bucket
            );
        }

        // At least 6 different buckets should be used (spread across color wheel)
        assert!(
            hue_buckets.len() >= 6,
            "Colors too concentrated: only {} hue buckets used",
            hue_buckets.len()
        );
    }

    #[test]
    fn test_color_hash_collision_resistance() {
        // Test that similar names produce different colors
        let pairs = [
            ("user1", "user2"),
            ("test", "Test"),
            ("alice", "Alice"),
            ("Bob", "bob"),
            ("a", "b"),
            ("file.rs", "file.ts"),
        ];

        for (name1, name2) in pairs {
            let color1 = User::color_from_name(name1);
            let color2 = User::color_from_name(name2);

            // Colors should be different
            assert_ne!(
                color1, color2,
                "Names '{}' and '{}' should produce different colors",
                name1, name2
            );
        }
    }

    #[test]
    fn test_color_hash_empty_and_special() {
        // Test edge cases
        let empty = User::color_from_name("");
        let space = User::color_from_name(" ");
        let unicode = User::color_from_name("🦀");
        let long_name = User::color_from_name(&"a".repeat(1000));

        // All should produce valid colors (no panic)
        assert!(empty.to_hsl().h >= 0.0);
        assert!(space.to_hsl().h >= 0.0);
        assert!(unicode.to_hsl().h >= 0.0);
        assert!(long_name.to_hsl().h >= 0.0);

        // Empty and single space should be different
        assert_ne!(empty, space);
    }
}
