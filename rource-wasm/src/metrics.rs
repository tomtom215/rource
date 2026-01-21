//! Performance metrics and render statistics for Rource WASM.
//!
//! This module provides types for tracking frame timing, FPS calculation,
//! and per-frame render statistics.

// ============================================================================
// Constants
// ============================================================================

/// Number of frame samples for FPS averaging.
///
/// A larger value provides smoother FPS readings but responds slower to changes.
/// 60 samples at 60fps = 1 second averaging window.
pub const FRAME_SAMPLE_COUNT: usize = 60;

// ============================================================================
// Performance Metrics
// ============================================================================

/// Performance metrics for FPS tracking and profiling.
///
/// Tracks frame timing using a rolling average for smooth FPS display.
/// Also maintains cumulative statistics like total frames and uptime.
///
/// # Example
///
/// ```ignore
/// let mut metrics = PerformanceMetrics::new();
///
/// // In your frame loop:
/// let dt = calculate_delta_time();
/// metrics.record_frame(dt);
///
/// println!("FPS: {:.1}", metrics.fps());
/// ```
#[derive(Debug, Clone)]
pub struct PerformanceMetrics {
    /// Rolling buffer of frame times (in seconds).
    frame_times: [f32; FRAME_SAMPLE_COUNT],
    /// Index into `frame_times` for ring buffer.
    frame_time_index: usize,
    /// Number of valid frame time samples.
    frame_time_count: usize,
    /// Last calculated FPS value.
    fps: f32,
    /// Last frame duration in milliseconds.
    frame_time_ms: f32,
    /// Total frames rendered.
    total_frames: u64,
    /// Time of initialization (for uptime tracking).
    start_time: f64,
}

impl Default for PerformanceMetrics {
    fn default() -> Self {
        Self::new()
    }
}

impl PerformanceMetrics {
    /// Creates a new performance metrics tracker.
    ///
    /// All values are initialized to zero. Call `record_frame()` to start
    /// collecting data.
    #[inline]
    pub fn new() -> Self {
        Self {
            frame_times: [0.0; FRAME_SAMPLE_COUNT],
            frame_time_index: 0,
            frame_time_count: 0,
            fps: 0.0,
            frame_time_ms: 0.0,
            total_frames: 0,
            start_time: 0.0,
        }
    }

    /// Records a frame time sample and updates FPS calculation.
    ///
    /// # Arguments
    ///
    /// * `dt` - Frame delta time in seconds
    ///
    /// # FPS Calculation
    ///
    /// FPS is calculated as a rolling average over the last [`FRAME_SAMPLE_COUNT`]
    /// frames. This provides stable readings without rapid fluctuation.
    pub fn record_frame(&mut self, dt: f32) {
        self.frame_times[self.frame_time_index] = dt;
        self.frame_time_index = (self.frame_time_index + 1) % FRAME_SAMPLE_COUNT;
        self.frame_time_count = (self.frame_time_count + 1).min(FRAME_SAMPLE_COUNT);
        self.total_frames += 1;
        self.frame_time_ms = dt * 1000.0;

        // Calculate rolling average FPS
        if self.frame_time_count > 0 {
            let sum: f32 = self.frame_times[..self.frame_time_count].iter().sum();
            let avg_dt = sum / self.frame_time_count as f32;
            self.fps = if avg_dt > 0.0 { 1.0 / avg_dt } else { 0.0 };
        }
    }

    /// Returns the current frames per second (rolling average).
    #[inline]
    pub fn fps(&self) -> f32 {
        self.fps
    }

    /// Returns the last frame time in milliseconds.
    #[inline]
    pub fn frame_time_ms(&self) -> f32 {
        self.frame_time_ms
    }

    /// Returns the total number of frames rendered since initialization.
    #[inline]
    pub fn total_frames(&self) -> u64 {
        self.total_frames
    }

    /// Returns the start time (milliseconds since page load).
    #[inline]
    pub fn start_time(&self) -> f64 {
        self.start_time
    }

    /// Sets the start time (should be called on first frame).
    #[inline]
    pub fn set_start_time(&mut self, time: f64) {
        self.start_time = time;
    }

    /// Returns the uptime in seconds given the current timestamp.
    ///
    /// # Arguments
    ///
    /// * `current_time` - Current timestamp in milliseconds
    #[inline]
    pub fn uptime(&self, current_time: f64) -> f64 {
        if self.start_time > 0.0 {
            (current_time - self.start_time) / 1000.0
        } else {
            0.0
        }
    }
}

// ============================================================================
// Render Statistics
// ============================================================================

/// Render statistics for the current frame.
///
/// These statistics are updated each frame during the render pass and can be
/// used for debugging, profiling, or displaying scene information to users.
#[derive(Debug, Clone, Default)]
pub struct RenderStats {
    /// Number of visible files being rendered.
    pub visible_files: usize,
    /// Number of visible users being rendered.
    pub visible_users: usize,
    /// Number of visible directories being rendered.
    pub visible_directories: usize,
    /// Number of active action beams.
    pub active_actions: usize,
    /// Total entities in the scene (files + users + directories + actions).
    pub total_entities: usize,
    /// Estimated draw call count.
    ///
    /// For WebGL2, this is typically 6 (one per primitive type with instancing).
    /// For Software, this is proportional to visible entities.
    pub draw_calls: usize,
}

impl RenderStats {
    /// Creates new render statistics with all values at zero.
    #[inline]
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self::default()
    }

    /// Updates all statistics at once.
    ///
    /// This is more efficient than setting individual fields when you have
    /// all values available.
    #[inline]
    pub fn update(
        &mut self,
        visible_files: usize,
        visible_users: usize,
        visible_directories: usize,
        active_actions: usize,
        total_entities: usize,
        draw_calls: usize,
    ) {
        self.visible_files = visible_files;
        self.visible_users = visible_users;
        self.visible_directories = visible_directories;
        self.active_actions = active_actions;
        self.total_entities = total_entities;
        self.draw_calls = draw_calls;
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // Performance Metrics Tests

    #[test]
    fn test_performance_metrics_new() {
        let metrics = PerformanceMetrics::new();
        assert_eq!(metrics.fps(), 0.0);
        assert_eq!(metrics.total_frames(), 0);
        assert_eq!(metrics.frame_time_ms(), 0.0);
    }

    #[test]
    fn test_performance_metrics_default() {
        let metrics = PerformanceMetrics::default();
        assert_eq!(metrics.fps(), 0.0);
        assert_eq!(metrics.total_frames(), 0);
    }

    #[test]
    fn test_performance_metrics_record_frame() {
        let mut metrics = PerformanceMetrics::new();

        // Record a frame at 60fps (16.67ms)
        metrics.record_frame(1.0 / 60.0);

        assert_eq!(metrics.total_frames(), 1);
        assert!(metrics.fps() > 59.0 && metrics.fps() < 61.0);
    }

    #[test]
    fn test_performance_metrics_rolling_average() {
        let mut metrics = PerformanceMetrics::new();

        // Record 60 frames at consistent 60fps
        for _ in 0..60 {
            metrics.record_frame(1.0 / 60.0);
        }

        assert_eq!(metrics.total_frames(), 60);
        // Should show approximately 60 FPS
        assert!(metrics.fps() > 59.0 && metrics.fps() < 61.0);
    }

    #[test]
    fn test_performance_metrics_varying_framerate() {
        let mut metrics = PerformanceMetrics::new();

        // Mix of fast and slow frames
        for _ in 0..30 {
            metrics.record_frame(1.0 / 30.0); // 30fps
        }
        for _ in 0..30 {
            metrics.record_frame(1.0 / 60.0); // 60fps
        }

        // Average should be between 30 and 60
        assert!(metrics.fps() > 30.0 && metrics.fps() < 60.0);
    }

    #[test]
    fn test_performance_metrics_zero_dt() {
        let mut metrics = PerformanceMetrics::new();
        // Recording a zero-duration frame should not crash
        metrics.record_frame(0.0);
        assert_eq!(metrics.total_frames(), 1);
    }

    #[test]
    fn test_performance_metrics_very_slow_frame() {
        let mut metrics = PerformanceMetrics::new();
        // Very slow frame (1 second = 1 FPS)
        metrics.record_frame(1.0);
        assert!(metrics.fps() > 0.9 && metrics.fps() < 1.1);
    }

    #[test]
    fn test_performance_metrics_uptime() {
        let mut metrics = PerformanceMetrics::new();
        metrics.set_start_time(1000.0);
        assert_eq!(metrics.uptime(2000.0), 1.0); // 1 second
        assert_eq!(metrics.uptime(3500.0), 2.5); // 2.5 seconds
    }

    #[test]
    fn test_performance_metrics_uptime_not_started() {
        let metrics = PerformanceMetrics::new();
        assert_eq!(metrics.uptime(1000.0), 0.0);
    }

    // Render Stats Tests

    #[test]
    fn test_render_stats_default() {
        let stats = RenderStats::default();
        assert_eq!(stats.visible_files, 0);
        assert_eq!(stats.visible_users, 0);
        assert_eq!(stats.visible_directories, 0);
        assert_eq!(stats.active_actions, 0);
        assert_eq!(stats.total_entities, 0);
        assert_eq!(stats.draw_calls, 0);
    }

    #[test]
    fn test_render_stats_new() {
        let stats = RenderStats::new();
        assert_eq!(stats.visible_files, 0);
    }

    #[test]
    fn test_render_stats_with_values() {
        let stats = RenderStats {
            visible_files: 100,
            visible_users: 5,
            visible_directories: 20,
            active_actions: 10,
            total_entities: 125,
            draw_calls: 50,
        };
        assert_eq!(stats.visible_files, 100);
        assert_eq!(stats.visible_users, 5);
        assert_eq!(stats.visible_directories, 20);
        assert_eq!(stats.active_actions, 10);
        assert_eq!(stats.total_entities, 125);
        assert_eq!(stats.draw_calls, 50);
    }

    #[test]
    fn test_render_stats_update() {
        let mut stats = RenderStats::new();
        stats.update(50, 3, 10, 5, 68, 25);

        assert_eq!(stats.visible_files, 50);
        assert_eq!(stats.visible_users, 3);
        assert_eq!(stats.visible_directories, 10);
        assert_eq!(stats.active_actions, 5);
        assert_eq!(stats.total_entities, 68);
        assert_eq!(stats.draw_calls, 25);
    }

    #[test]
    fn test_render_stats_clone() {
        let stats1 = RenderStats {
            visible_files: 42,
            visible_users: 7,
            visible_directories: 15,
            active_actions: 3,
            total_entities: 67,
            draw_calls: 30,
        };
        let stats2 = stats1.clone();
        assert_eq!(stats1.visible_files, stats2.visible_files);
        assert_eq!(stats1.visible_users, stats2.visible_users);
    }

    #[test]
    fn test_render_stats_debug() {
        let stats = RenderStats::new();
        let debug_str = format!("{stats:?}");
        assert!(debug_str.contains("visible_files"));
    }
}
