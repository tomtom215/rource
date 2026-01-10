//! Core commit data structures.
//!
//! These types represent VCS commits and file changes in a
//! VCS-agnostic format that can be produced by any parser.

use std::fmt;
use std::path::PathBuf;

/// The action performed on a file in a commit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FileAction {
    /// File was created (new file added to repository).
    Create,
    /// File was modified (content changed).
    Modify,
    /// File was deleted (removed from repository).
    Delete,
}

impl FileAction {
    /// Returns the standard color for this action type.
    ///
    /// These colors match the original Gource conventions:
    /// - Create: Green (#00FF00)
    /// - Modify: Orange (#FF8000)
    /// - Delete: Red (#FF0000)
    #[must_use]
    pub const fn color_rgb(self) -> (u8, u8, u8) {
        match self {
            Self::Create => (0, 255, 0),   // Green
            Self::Modify => (255, 128, 0), // Orange
            Self::Delete => (255, 0, 0),   // Red
        }
    }

    /// Returns a single-character code for this action.
    ///
    /// Used in the custom log format.
    #[must_use]
    pub const fn as_char(self) -> char {
        match self {
            Self::Create => 'A',
            Self::Modify => 'M',
            Self::Delete => 'D',
        }
    }

    /// Parses an action from a single character.
    ///
    /// # Returns
    ///
    /// - `Some(FileAction)` if the character is recognized
    /// - `None` for unknown characters
    #[must_use]
    pub const fn from_char(c: char) -> Option<Self> {
        match c {
            'A' | 'a' => Some(Self::Create),
            'M' | 'm' => Some(Self::Modify),
            'D' | 'd' => Some(Self::Delete),
            'C' | 'c' => Some(Self::Create), // Copy is treated as create
            'R' | 'r' => Some(Self::Modify), // Rename is treated as modify
            _ => None,
        }
    }
}

impl fmt::Display for FileAction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Create => write!(f, "create"),
            Self::Modify => write!(f, "modify"),
            Self::Delete => write!(f, "delete"),
        }
    }
}

/// A file change within a commit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileChange {
    /// The file path relative to the repository root.
    pub path: PathBuf,
    /// The action performed on the file.
    pub action: FileAction,
}

impl FileChange {
    /// Creates a new file change.
    #[must_use]
    pub fn new(path: impl Into<PathBuf>, action: FileAction) -> Self {
        Self {
            path: path.into(),
            action,
        }
    }

    /// Creates a new "create" file change.
    #[must_use]
    pub fn create(path: impl Into<PathBuf>) -> Self {
        Self::new(path, FileAction::Create)
    }

    /// Creates a new "modify" file change.
    #[must_use]
    pub fn modify(path: impl Into<PathBuf>) -> Self {
        Self::new(path, FileAction::Modify)
    }

    /// Creates a new "delete" file change.
    #[must_use]
    pub fn delete(path: impl Into<PathBuf>) -> Self {
        Self::new(path, FileAction::Delete)
    }

    /// Returns the file extension, if any.
    #[must_use]
    pub fn extension(&self) -> Option<&str> {
        self.path.extension().and_then(|e| e.to_str())
    }

    /// Returns the file name without the path.
    #[must_use]
    pub fn file_name(&self) -> Option<&str> {
        self.path.file_name().and_then(|n| n.to_str())
    }

    /// Returns the parent directory path.
    #[must_use]
    pub fn parent(&self) -> Option<&std::path::Path> {
        self.path.parent()
    }
}

impl fmt::Display for FileChange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.action.as_char(), self.path.display())
    }
}

/// A version control commit.
///
/// This is the VCS-agnostic representation of a commit that
/// can be produced by any parser.
#[derive(Debug, Clone, PartialEq)]
pub struct Commit {
    /// The commit hash or revision identifier.
    ///
    /// For Git, this is the full SHA-1 hash.
    /// For SVN, this is the revision number as a string.
    pub hash: String,

    /// The commit timestamp in seconds since Unix epoch.
    pub timestamp: i64,

    /// The commit author's name.
    pub author: String,

    /// The commit author's email (if available).
    pub email: Option<String>,

    /// The list of file changes in this commit.
    pub files: Vec<FileChange>,
}

impl Commit {
    /// Creates a new commit.
    #[must_use]
    pub fn new(hash: impl Into<String>, timestamp: i64, author: impl Into<String>) -> Self {
        Self {
            hash: hash.into(),
            timestamp,
            author: author.into(),
            email: None,
            files: Vec::new(),
        }
    }

    /// Sets the author email.
    #[must_use]
    pub fn with_email(mut self, email: impl Into<String>) -> Self {
        self.email = Some(email.into());
        self
    }

    /// Adds a file change to the commit.
    #[must_use]
    pub fn with_file(mut self, change: FileChange) -> Self {
        self.files.push(change);
        self
    }

    /// Adds multiple file changes to the commit.
    #[must_use]
    pub fn with_files(mut self, changes: impl IntoIterator<Item = FileChange>) -> Self {
        self.files.extend(changes);
        self
    }

    /// Returns the number of file changes.
    #[must_use]
    pub fn file_count(&self) -> usize {
        self.files.len()
    }

    /// Returns true if this commit has no file changes.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }

    /// Returns an iterator over file creations.
    pub fn creations(&self) -> impl Iterator<Item = &FileChange> {
        self.files.iter().filter(|f| f.action == FileAction::Create)
    }

    /// Returns an iterator over file modifications.
    pub fn modifications(&self) -> impl Iterator<Item = &FileChange> {
        self.files.iter().filter(|f| f.action == FileAction::Modify)
    }

    /// Returns an iterator over file deletions.
    pub fn deletions(&self) -> impl Iterator<Item = &FileChange> {
        self.files.iter().filter(|f| f.action == FileAction::Delete)
    }

    /// Returns the short hash (first 7 characters for Git-style hashes).
    #[must_use]
    pub fn short_hash(&self) -> &str {
        if self.hash.len() > 7 {
            &self.hash[..7]
        } else {
            &self.hash
        }
    }

    /// Returns the author's display name (name with optional email).
    #[must_use]
    pub fn author_display(&self) -> String {
        match &self.email {
            Some(email) => format!("{} <{}>", self.author, email),
            None => self.author.clone(),
        }
    }
}

impl fmt::Display for Commit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} by {} ({} files)",
            self.short_hash(),
            self.author,
            self.files.len()
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_file_action_from_char() {
        assert_eq!(FileAction::from_char('A'), Some(FileAction::Create));
        assert_eq!(FileAction::from_char('a'), Some(FileAction::Create));
        assert_eq!(FileAction::from_char('M'), Some(FileAction::Modify));
        assert_eq!(FileAction::from_char('D'), Some(FileAction::Delete));
        assert_eq!(FileAction::from_char('C'), Some(FileAction::Create));
        assert_eq!(FileAction::from_char('R'), Some(FileAction::Modify));
        assert_eq!(FileAction::from_char('X'), None);
    }

    #[test]
    fn test_file_action_as_char() {
        assert_eq!(FileAction::Create.as_char(), 'A');
        assert_eq!(FileAction::Modify.as_char(), 'M');
        assert_eq!(FileAction::Delete.as_char(), 'D');
    }

    #[test]
    fn test_file_action_color() {
        assert_eq!(FileAction::Create.color_rgb(), (0, 255, 0));
        assert_eq!(FileAction::Modify.color_rgb(), (255, 128, 0));
        assert_eq!(FileAction::Delete.color_rgb(), (255, 0, 0));
    }

    #[test]
    fn test_file_change() {
        let change = FileChange::new("src/main.rs", FileAction::Modify);
        assert_eq!(change.extension(), Some("rs"));
        assert_eq!(change.file_name(), Some("main.rs"));
        assert_eq!(change.parent(), Some(std::path::Path::new("src")));
    }

    #[test]
    fn test_file_change_constructors() {
        let create = FileChange::create("new.txt");
        assert_eq!(create.action, FileAction::Create);

        let modify = FileChange::modify("changed.txt");
        assert_eq!(modify.action, FileAction::Modify);

        let delete = FileChange::delete("removed.txt");
        assert_eq!(delete.action, FileAction::Delete);
    }

    #[test]
    fn test_commit() {
        let commit = Commit::new("abc123def456", 1234567890, "John Doe")
            .with_email("john@example.com")
            .with_file(FileChange::create("new.rs"))
            .with_file(FileChange::modify("existing.rs"))
            .with_file(FileChange::delete("old.rs"));

        assert_eq!(commit.hash, "abc123def456");
        assert_eq!(commit.short_hash(), "abc123d");
        assert_eq!(commit.timestamp, 1234567890);
        assert_eq!(commit.author, "John Doe");
        assert_eq!(commit.email, Some("john@example.com".to_string()));
        assert_eq!(commit.file_count(), 3);
        assert!(!commit.is_empty());

        assert_eq!(commit.creations().count(), 1);
        assert_eq!(commit.modifications().count(), 1);
        assert_eq!(commit.deletions().count(), 1);
    }

    #[test]
    fn test_commit_author_display() {
        let with_email = Commit::new("abc", 0, "John").with_email("john@test.com");
        assert_eq!(with_email.author_display(), "John <john@test.com>");

        let without_email = Commit::new("abc", 0, "John");
        assert_eq!(without_email.author_display(), "John");
    }

    #[test]
    fn test_commit_short_hash() {
        let long = Commit::new("abc123def456789", 0, "Test");
        assert_eq!(long.short_hash(), "abc123d");

        let short = Commit::new("abc", 0, "Test");
        assert_eq!(short.short_hash(), "abc");
    }

    #[test]
    fn test_commit_with_files() {
        let files = vec![FileChange::create("a.txt"), FileChange::create("b.txt")];
        let commit = Commit::new("abc", 0, "Test").with_files(files);
        assert_eq!(commit.file_count(), 2);
    }

    #[test]
    fn test_display() {
        let action = FileAction::Create;
        assert_eq!(format!("{action}"), "create");

        let change = FileChange::new("src/lib.rs", FileAction::Modify);
        assert_eq!(format!("{change}"), "M src/lib.rs");

        let commit = Commit::new("abc123def", 0, "John").with_file(FileChange::create("test.rs"));
        assert!(format!("{commit}").contains("abc123d"));
        assert!(format!("{commit}").contains("John"));
        assert!(format!("{commit}").contains("1 files"));
    }
}
