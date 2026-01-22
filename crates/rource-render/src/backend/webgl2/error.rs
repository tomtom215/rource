//! Error types for the WebGL2 renderer.
//!
//! This module contains error types for WebGL2 renderer initialization and operations.

/// Error type for WebGL2 renderer initialization.
#[derive(Debug, Clone)]
pub enum WebGl2Error {
    /// WebGL2 context not available.
    ContextNotAvailable,
    /// Shader compilation failed.
    ShaderCompilation(String),
    /// Program linking failed.
    ProgramLinking(String),
}

impl std::fmt::Display for WebGl2Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ContextNotAvailable => write!(f, "WebGL2 context not available"),
            Self::ShaderCompilation(msg) => write!(f, "Shader compilation failed: {msg}"),
            Self::ProgramLinking(msg) => write!(f, "Program linking failed: {msg}"),
        }
    }
}

impl std::error::Error for WebGl2Error {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_webgl2_error_display() {
        let err = WebGl2Error::ContextNotAvailable;
        assert_eq!(format!("{err}"), "WebGL2 context not available");

        let err = WebGl2Error::ShaderCompilation("test error".into());
        assert!(format!("{err}").contains("test error"));

        let err = WebGl2Error::ProgramLinking("link error".into());
        assert!(format!("{err}").contains("link error"));
    }

    #[test]
    fn test_webgl2_error_debug() {
        let err = WebGl2Error::ContextNotAvailable;
        assert!(format!("{err:?}").contains("ContextNotAvailable"));

        let err = WebGl2Error::ShaderCompilation("vertex shader failed".into());
        assert!(format!("{err:?}").contains("ShaderCompilation"));
    }
}
