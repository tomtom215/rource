//! Error types for the wgpu rendering backend.

/// Error type for wgpu renderer operations.
#[derive(Debug, Clone)]
pub enum WgpuError {
    /// Failed to create wgpu adapter.
    AdapterNotFound,
    /// Failed to create wgpu device.
    DeviceCreationFailed(String),
    /// Failed to create surface.
    SurfaceCreationFailed(String),
    /// Shader compilation failed.
    ShaderCompilationFailed(String),
    /// Pipeline creation failed.
    PipelineCreationFailed(String),
    /// Context lost.
    ContextLost,
}

impl std::fmt::Display for WgpuError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AdapterNotFound => write!(f, "wgpu adapter not found"),
            Self::DeviceCreationFailed(msg) => write!(f, "wgpu device creation failed: {msg}"),
            Self::SurfaceCreationFailed(msg) => write!(f, "wgpu surface creation failed: {msg}"),
            Self::ShaderCompilationFailed(msg) => write!(f, "Shader compilation failed: {msg}"),
            Self::PipelineCreationFailed(msg) => write!(f, "Pipeline creation failed: {msg}"),
            Self::ContextLost => write!(f, "GPU context lost"),
        }
    }
}

impl std::error::Error for WgpuError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wgpu_error_display() {
        let err = WgpuError::AdapterNotFound;
        assert!(format!("{err}").contains("adapter"));

        let err = WgpuError::DeviceCreationFailed("test".into());
        assert!(format!("{err}").contains("device"));
        assert!(format!("{err}").contains("test"));
    }

    #[test]
    fn test_wgpu_error_surface() {
        let err = WgpuError::SurfaceCreationFailed("surface error".into());
        assert!(format!("{err}").contains("surface"));
    }

    #[test]
    fn test_wgpu_error_shader() {
        let err = WgpuError::ShaderCompilationFailed("shader error".into());
        assert!(format!("{err}").contains("Shader"));
    }

    #[test]
    fn test_wgpu_error_pipeline() {
        let err = WgpuError::PipelineCreationFailed("pipeline error".into());
        assert!(format!("{err}").contains("Pipeline"));
    }

    #[test]
    fn test_wgpu_error_context_lost() {
        let err = WgpuError::ContextLost;
        assert!(format!("{err}").contains("context"));
    }
}
