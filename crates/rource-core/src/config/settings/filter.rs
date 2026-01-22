//! Filter settings for users and files.

use regex_lite::Regex;
use std::path::Path;

/// Filter settings for users and files.
///
/// Allows filtering entities by regex patterns. The "show" patterns include
/// matching entities, while "hide" patterns exclude them. If both are specified,
/// "hide" takes precedence over "show".
#[derive(Debug, Clone, Default)]
pub struct FilterSettings {
    /// Regex pattern to match users that should be shown.
    /// If set, only users matching this pattern are displayed.
    show_users: Option<String>,

    /// Regex pattern to match users that should be hidden.
    /// Takes precedence over `show_users`.
    hide_users: Option<String>,

    /// Regex pattern to match file paths that should be shown.
    /// If set, only files matching this pattern are displayed.
    show_files: Option<String>,

    /// Regex pattern to match file paths that should be hidden.
    /// Takes precedence over `show_files`.
    hide_files: Option<String>,

    /// Regex pattern to match directory paths to exclude.
    /// Entire directory trees matching this pattern are excluded.
    hide_dirs: Option<String>,

    /// Compiled regex for `show_users` (lazily compiled).
    #[allow(clippy::type_complexity)]
    show_users_regex: Option<Result<Regex, String>>,

    /// Compiled regex for `hide_users` (lazily compiled).
    #[allow(clippy::type_complexity)]
    hide_users_regex: Option<Result<Regex, String>>,

    /// Compiled regex for `show_files` (lazily compiled).
    #[allow(clippy::type_complexity)]
    show_files_regex: Option<Result<Regex, String>>,

    /// Compiled regex for `hide_files` (lazily compiled).
    #[allow(clippy::type_complexity)]
    hide_files_regex: Option<Result<Regex, String>>,

    /// Compiled regex for `hide_dirs` (lazily compiled).
    #[allow(clippy::type_complexity)]
    hide_dirs_regex: Option<Result<Regex, String>>,
}

impl FilterSettings {
    /// Creates new filter settings with no filters.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets the user show filter.
    #[must_use]
    pub fn with_show_users(mut self, pattern: impl Into<String>) -> Self {
        let pattern = pattern.into();
        if !pattern.is_empty() {
            self.show_users = Some(pattern);
            self.show_users_regex = None; // Clear cached regex
        }
        self
    }

    /// Sets the user hide filter.
    #[must_use]
    pub fn with_hide_users(mut self, pattern: impl Into<String>) -> Self {
        let pattern = pattern.into();
        if !pattern.is_empty() {
            self.hide_users = Some(pattern);
            self.hide_users_regex = None;
        }
        self
    }

    /// Sets the file show filter.
    #[must_use]
    pub fn with_show_files(mut self, pattern: impl Into<String>) -> Self {
        let pattern = pattern.into();
        if !pattern.is_empty() {
            self.show_files = Some(pattern);
            self.show_files_regex = None;
        }
        self
    }

    /// Sets the file hide filter.
    #[must_use]
    pub fn with_hide_files(mut self, pattern: impl Into<String>) -> Self {
        let pattern = pattern.into();
        if !pattern.is_empty() {
            self.hide_files = Some(pattern);
            self.hide_files_regex = None;
        }
        self
    }

    /// Sets the directory hide filter.
    #[must_use]
    pub fn with_hide_dirs(mut self, pattern: impl Into<String>) -> Self {
        let pattern = pattern.into();
        if !pattern.is_empty() {
            self.hide_dirs = Some(pattern);
            self.hide_dirs_regex = None;
        }
        self
    }

    /// Sets the user show filter (mutable).
    pub fn set_show_users(&mut self, pattern: Option<String>) {
        self.show_users = pattern.filter(|s| !s.is_empty());
        self.show_users_regex = None;
    }

    /// Sets the user hide filter (mutable).
    pub fn set_hide_users(&mut self, pattern: Option<String>) {
        self.hide_users = pattern.filter(|s| !s.is_empty());
        self.hide_users_regex = None;
    }

    /// Sets the file show filter (mutable).
    pub fn set_show_files(&mut self, pattern: Option<String>) {
        self.show_files = pattern.filter(|s| !s.is_empty());
        self.show_files_regex = None;
    }

    /// Sets the file hide filter (mutable).
    pub fn set_hide_files(&mut self, pattern: Option<String>) {
        self.hide_files = pattern.filter(|s| !s.is_empty());
        self.hide_files_regex = None;
    }

    /// Sets the directory hide filter (mutable).
    pub fn set_hide_dirs(&mut self, pattern: Option<String>) {
        self.hide_dirs = pattern.filter(|s| !s.is_empty());
        self.hide_dirs_regex = None;
    }

    /// Returns the `show_users` pattern.
    #[must_use]
    pub fn show_users_pattern(&self) -> Option<&str> {
        self.show_users.as_deref()
    }

    /// Returns the `hide_users` pattern.
    #[must_use]
    pub fn hide_users_pattern(&self) -> Option<&str> {
        self.hide_users.as_deref()
    }

    /// Returns the `show_files` pattern.
    #[must_use]
    pub fn show_files_pattern(&self) -> Option<&str> {
        self.show_files.as_deref()
    }

    /// Returns the `hide_files` pattern.
    #[must_use]
    pub fn hide_files_pattern(&self) -> Option<&str> {
        self.hide_files.as_deref()
    }

    /// Returns the `hide_dirs` pattern.
    #[must_use]
    pub fn hide_dirs_pattern(&self) -> Option<&str> {
        self.hide_dirs.as_deref()
    }

    /// Compiles a regex pattern, caching the result.
    #[allow(clippy::ref_option)] // Using &Option here for ergonomic self.field references
    fn compile_regex<'a>(
        pattern: &Option<String>,
        cached: &'a mut Option<Result<Regex, String>>,
    ) -> Option<Result<&'a Regex, &'a str>> {
        if pattern.is_none() {
            return None;
        }

        if cached.is_none() {
            let result = pattern
                .as_ref()
                .map(|p| Regex::new(p).map_err(|e| e.to_string()))
                .unwrap();
            *cached = Some(result);
        }

        cached.as_ref().map(|r| r.as_ref().map_err(String::as_str))
    }

    /// Checks if a user should be included based on filter settings.
    ///
    /// Returns `true` if the user should be shown, `false` if filtered out.
    pub fn should_include_user(&mut self, name: &str) -> bool {
        // Check hide filter first (takes precedence)
        if let Some(Ok(regex)) = Self::compile_regex(&self.hide_users, &mut self.hide_users_regex) {
            if regex.is_match(name) {
                return false;
            }
        }

        // Check show filter
        if let Some(Ok(regex)) = Self::compile_regex(&self.show_users, &mut self.show_users_regex) {
            return regex.is_match(name);
        }

        true // No filters or invalid regex = show all
    }

    /// Checks if a file should be included based on filter settings.
    ///
    /// Returns `true` if the file should be shown, `false` if filtered out.
    pub fn should_include_file(&mut self, path: &Path) -> bool {
        let path_str = path.to_string_lossy();

        // Check directory hide filter first
        if let Some(Ok(regex)) = Self::compile_regex(&self.hide_dirs, &mut self.hide_dirs_regex) {
            // Check if any component of the path matches the directory filter
            for ancestor in path.ancestors() {
                if ancestor.as_os_str().is_empty() {
                    continue;
                }
                let ancestor_str = ancestor.to_string_lossy();
                if regex.is_match(&ancestor_str) {
                    return false;
                }
            }
        }

        // Check file hide filter
        if let Some(Ok(regex)) = Self::compile_regex(&self.hide_files, &mut self.hide_files_regex) {
            if regex.is_match(&path_str) {
                return false;
            }
        }

        // Check file show filter
        if let Some(Ok(regex)) = Self::compile_regex(&self.show_files, &mut self.show_files_regex) {
            return regex.is_match(&path_str);
        }

        true // No filters or invalid regex = show all
    }

    /// Validates filter patterns and returns errors for invalid regexes.
    #[must_use]
    pub fn validate(&mut self) -> Vec<String> {
        let mut errors = Vec::new();

        // Validate each filter pattern
        if let Some(pattern) = &self.show_users {
            if Regex::new(pattern).is_err() {
                errors.push(format!("Invalid regex for show-users: {pattern}"));
            }
        }
        if let Some(pattern) = &self.hide_users {
            if Regex::new(pattern).is_err() {
                errors.push(format!("Invalid regex for hide-users: {pattern}"));
            }
        }
        if let Some(pattern) = &self.show_files {
            if Regex::new(pattern).is_err() {
                errors.push(format!("Invalid regex for show-files: {pattern}"));
            }
        }
        if let Some(pattern) = &self.hide_files {
            if Regex::new(pattern).is_err() {
                errors.push(format!("Invalid regex for hide-files: {pattern}"));
            }
        }
        if let Some(pattern) = &self.hide_dirs {
            if Regex::new(pattern).is_err() {
                errors.push(format!("Invalid regex for hide-dirs: {pattern}"));
            }
        }

        errors
    }

    /// Returns true if any filters are configured.
    #[must_use]
    pub fn has_filters(&self) -> bool {
        self.show_users.is_some()
            || self.hide_users.is_some()
            || self.show_files.is_some()
            || self.hide_files.is_some()
            || self.hide_dirs.is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_filter_settings_default() {
        let filter = FilterSettings::default();
        assert!(!filter.has_filters());
        assert!(filter.show_users_pattern().is_none());
        assert!(filter.hide_users_pattern().is_none());
    }

    #[test]
    fn test_filter_settings_builder() {
        let filter = FilterSettings::new()
            .with_hide_users("bot.*")
            .with_show_files(r"\.rs$");

        assert!(filter.has_filters());
        assert_eq!(filter.hide_users_pattern(), Some("bot.*"));
        assert_eq!(filter.show_files_pattern(), Some(r"\.rs$"));
    }

    #[test]
    fn test_filter_user_inclusion() {
        let mut filter = FilterSettings::new().with_hide_users("bot.*");

        assert!(filter.should_include_user("alice"));
        assert!(filter.should_include_user("Bob"));
        assert!(!filter.should_include_user("bot123"));
        assert!(!filter.should_include_user("bot-ci"));
    }

    #[test]
    fn test_filter_user_show_only() {
        let mut filter = FilterSettings::new().with_show_users("^(alice|bob)$");

        assert!(filter.should_include_user("alice"));
        assert!(filter.should_include_user("bob"));
        assert!(!filter.should_include_user("charlie"));
        assert!(!filter.should_include_user("alice_smith")); // Exact match only
    }

    #[test]
    fn test_filter_user_hide_precedence() {
        // Hide takes precedence over show
        let mut filter = FilterSettings::new()
            .with_show_users(".*")
            .with_hide_users("^bot$");

        assert!(filter.should_include_user("alice"));
        assert!(!filter.should_include_user("bot"));
    }

    #[test]
    fn test_filter_file_inclusion() {
        let mut filter = FilterSettings::new().with_hide_files(r"\.log$");

        assert!(filter.should_include_file(&PathBuf::from("src/main.rs")));
        assert!(filter.should_include_file(&PathBuf::from("README.md")));
        assert!(!filter.should_include_file(&PathBuf::from("debug.log")));
        assert!(!filter.should_include_file(&PathBuf::from("logs/app.log")));
    }

    #[test]
    fn test_filter_file_show_only() {
        let mut filter = FilterSettings::new().with_show_files(r"\.rs$");

        assert!(filter.should_include_file(&PathBuf::from("src/main.rs")));
        assert!(filter.should_include_file(&PathBuf::from("lib.rs")));
        assert!(!filter.should_include_file(&PathBuf::from("README.md")));
        assert!(!filter.should_include_file(&PathBuf::from("Cargo.toml")));
    }

    #[test]
    fn test_filter_dir_exclusion() {
        let mut filter = FilterSettings::new().with_hide_dirs("node_modules|target");

        assert!(filter.should_include_file(&PathBuf::from("src/main.rs")));
        assert!(!filter.should_include_file(&PathBuf::from("node_modules/pkg/index.js")));
        assert!(!filter.should_include_file(&PathBuf::from("target/debug/app")));
    }

    #[test]
    fn test_filter_validation() {
        let mut valid = FilterSettings::new().with_hide_users(".*");
        assert!(valid.validate().is_empty());

        let mut invalid = FilterSettings::new().with_hide_users("[invalid");
        let errors = invalid.validate();
        assert!(!errors.is_empty());
        assert!(errors[0].contains("hide-users"));
    }
}
