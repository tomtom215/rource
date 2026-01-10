//! Action entity for the visualization.
//!
//! Actions represent the visual "beams" that connect users to files
//! when they perform operations (create, modify, delete).

use rource_math::{Color, Vec2};

use crate::entity::{ActionId, FileId, UserId};

/// Speed at which actions progress (per second).
pub const ACTION_SPEED: f32 = 2.0;

/// The type of action being performed on a file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ActionType {
    /// File is being created (new file).
    Create,
    /// File is being modified (content changed).
    Modify,
    /// File is being deleted (removed).
    Delete,
}

impl ActionType {
    /// Returns the color associated with this action type.
    #[must_use]
    pub const fn color(self) -> Color {
        match self {
            Self::Create => Color::from_rgb8_const(0, 255, 0), // Green
            Self::Modify => Color::from_rgb8_const(255, 165, 0), // Orange
            Self::Delete => Color::from_rgb8_const(255, 0, 0), // Red
        }
    }

    /// Returns a human-readable name for the action type.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Create => "create",
            Self::Modify => "modify",
            Self::Delete => "delete",
        }
    }
}

impl std::fmt::Display for ActionType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// An action connecting a user to a file.
///
/// Actions are visual elements that show a "beam" from the user
/// to the file they are modifying. The beam animates from the user
/// to the file as the action progresses.
#[derive(Debug, Clone)]
#[allow(clippy::struct_field_names)]
pub struct Action {
    /// The action ID.
    id: ActionId,

    /// Source user performing the action.
    user: UserId,

    /// Target file being acted upon.
    file: FileId,

    /// The type of action.
    action_type: ActionType,

    /// Progress (0.0 = start at user, 1.0 = reached file).
    progress: f32,

    /// The color of the action beam.
    color: Color,
}

impl Action {
    /// Creates a new action.
    #[must_use]
    pub fn new(id: ActionId, user: UserId, file: FileId, action_type: ActionType) -> Self {
        Self {
            id,
            user,
            file,
            action_type,
            progress: 0.0,
            color: action_type.color(),
        }
    }

    /// Returns the action ID.
    #[inline]
    #[must_use]
    pub const fn id(&self) -> ActionId {
        self.id
    }

    /// Returns the user performing the action.
    #[inline]
    #[must_use]
    pub const fn user(&self) -> UserId {
        self.user
    }

    /// Returns the file being acted upon.
    #[inline]
    #[must_use]
    pub const fn file(&self) -> FileId {
        self.file
    }

    /// Returns the action type.
    #[inline]
    #[must_use]
    pub const fn action_type(&self) -> ActionType {
        self.action_type
    }

    /// Returns the current progress (0.0 to 1.0).
    #[inline]
    #[must_use]
    pub const fn progress(&self) -> f32 {
        self.progress
    }

    /// Returns the action color.
    #[inline]
    #[must_use]
    pub const fn color(&self) -> Color {
        self.color
    }

    /// Sets a custom color for the action.
    #[inline]
    pub fn set_color(&mut self, color: Color) {
        self.color = color;
    }

    /// Updates the action progress.
    ///
    /// Returns true if the action is still in progress.
    pub fn update(&mut self, dt: f32) -> bool {
        self.progress = (self.progress + dt * ACTION_SPEED).min(1.0);
        !self.is_complete()
    }

    /// Returns true if the action has completed.
    #[inline]
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.progress >= 1.0
    }

    /// Gets the interpolated position along the beam.
    ///
    /// This is used for rendering the beam "head" that travels
    /// from the user to the file.
    #[must_use]
    pub fn beam_position(&self, user_pos: Vec2, file_pos: Vec2) -> Vec2 {
        user_pos.lerp(file_pos, self.progress)
    }

    /// Gets the beam start position (always the user position).
    #[must_use]
    pub const fn beam_start(&self, user_pos: Vec2) -> Vec2 {
        user_pos
    }

    /// Gets the beam end position (the current progress point).
    #[must_use]
    pub fn beam_end(&self, user_pos: Vec2, file_pos: Vec2) -> Vec2 {
        self.beam_position(user_pos, file_pos)
    }

    /// Gets the current beam length as a fraction (0.0 to 1.0).
    #[must_use]
    pub const fn beam_length(&self) -> f32 {
        self.progress
    }

    /// Gets the beam color with appropriate alpha based on progress.
    ///
    /// The beam fades slightly as it nears completion.
    #[must_use]
    pub fn beam_color(&self) -> Color {
        // Fade out slightly near the end
        let alpha = if self.progress > 0.8 {
            1.0 - (self.progress - 0.8) * 5.0 // Fade from 0.8 to 1.0
        } else {
            1.0
        };
        self.color.with_alpha(alpha.max(0.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_action_type_color() {
        assert_eq!(ActionType::Create.color(), Color::from_rgb8(0, 255, 0));
        assert_eq!(ActionType::Modify.color(), Color::from_rgb8(255, 165, 0));
        assert_eq!(ActionType::Delete.color(), Color::from_rgb8(255, 0, 0));
    }

    #[test]
    fn test_action_type_name() {
        assert_eq!(ActionType::Create.name(), "create");
        assert_eq!(ActionType::Modify.name(), "modify");
        assert_eq!(ActionType::Delete.name(), "delete");
    }

    #[test]
    fn test_action_type_display() {
        assert_eq!(format!("{}", ActionType::Create), "create");
        assert_eq!(format!("{}", ActionType::Modify), "modify");
        assert_eq!(format!("{}", ActionType::Delete), "delete");
    }

    #[test]
    fn test_action_new() {
        let id = ActionId::from_index(0);
        let user = UserId::from_index(0);
        let file = FileId::from_index(0);

        let action = Action::new(id, user, file, ActionType::Create);

        assert_eq!(action.id(), id);
        assert_eq!(action.user(), user);
        assert_eq!(action.file(), file);
        assert_eq!(action.action_type(), ActionType::Create);
        assert_eq!(action.progress(), 0.0);
        assert_eq!(action.color(), ActionType::Create.color());
        assert!(!action.is_complete());
    }

    #[test]
    fn test_action_update() {
        let id = ActionId::from_index(0);
        let user = UserId::from_index(0);
        let file = FileId::from_index(0);

        let mut action = Action::new(id, user, file, ActionType::Modify);

        assert!(action.update(0.25)); // Still in progress (progress = 0.5)
        assert!((action.progress() - 0.5).abs() < 0.01); // 0.25 * ACTION_SPEED (2.0) = 0.5

        // Second update brings progress to 1.0, action completes
        assert!(!action.update(0.25)); // Now complete (progress = 1.0)
        assert!(action.is_complete());
        assert_eq!(action.progress(), 1.0);
    }

    #[test]
    fn test_action_beam_position() {
        let id = ActionId::from_index(0);
        let user = UserId::from_index(0);
        let file = FileId::from_index(0);

        let mut action = Action::new(id, user, file, ActionType::Create);

        let user_pos = Vec2::new(0.0, 0.0);
        let file_pos = Vec2::new(100.0, 0.0);

        // At start, beam is at user position
        assert_eq!(action.beam_position(user_pos, file_pos), user_pos);
        assert_eq!(action.beam_start(user_pos), user_pos);

        // Update to 50%
        action.update(0.25); // 50% progress
        let mid_pos = action.beam_position(user_pos, file_pos);
        assert!((mid_pos.x - 50.0).abs() < 0.01);

        // Update to 100%
        action.update(0.25);
        assert_eq!(action.beam_position(user_pos, file_pos), file_pos);
    }

    #[test]
    fn test_action_beam_color() {
        let id = ActionId::from_index(0);
        let user = UserId::from_index(0);
        let file = FileId::from_index(0);

        let mut action = Action::new(id, user, file, ActionType::Delete);

        // At start, full alpha
        assert_eq!(action.beam_color().a, 1.0);

        // At 80%, starts fading
        action.progress = 0.8;
        assert_eq!(action.beam_color().a, 1.0);

        // At 90%, half faded
        action.progress = 0.9;
        assert!((action.beam_color().a - 0.5).abs() < 0.01);

        // At 100%, fully faded (use tolerance for floating point)
        action.progress = 1.0;
        assert!(action.beam_color().a.abs() < 0.0001);
    }

    #[test]
    fn test_action_custom_color() {
        let id = ActionId::from_index(0);
        let user = UserId::from_index(0);
        let file = FileId::from_index(0);

        let mut action = Action::new(id, user, file, ActionType::Create);

        let custom_color = Color::from_rgb8(128, 64, 255);
        action.set_color(custom_color);

        assert_eq!(action.color(), custom_color);
    }

    #[test]
    fn test_action_beam_length() {
        let id = ActionId::from_index(0);
        let user = UserId::from_index(0);
        let file = FileId::from_index(0);

        let mut action = Action::new(id, user, file, ActionType::Modify);

        assert_eq!(action.beam_length(), 0.0);

        action.update(0.25); // 50%
        assert!((action.beam_length() - 0.5).abs() < 0.01);

        action.update(0.25); // 100%
        assert_eq!(action.beam_length(), 1.0);
    }
}
