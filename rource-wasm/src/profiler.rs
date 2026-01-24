// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! WASM-specific profiling infrastructure.
//!
//! This module provides browser-native profiling capabilities that integrate with
//! Chrome DevTools and other browser developer tools.
//!
//! ## Features
//!
//! ### Always Available (no feature flag)
//! - `FrameProfiler`: Phase timing with Performance API marks/measures
//! - `WasmMemoryStats`: WASM heap memory tracking
//! - `getDetailedFrameStats()`: JavaScript API for profiling data
//!
//! ### With `--features profiling`
//! - Performance marks visible in Chrome DevTools Performance tab
//! - Detailed phase breakdown (scene_update, render, gpu_wait, etc.)
//!
//! ### With `--features tracing`
//! - Rust tracing spans routed to browser console
//! - Function-level timing with call hierarchy
//!
//! ## Usage in Chrome DevTools
//!
//! 1. Open DevTools (F12)
//! 2. Go to Performance tab
//! 3. Click Record, interact with visualization, click Stop
//! 4. Look for "rource:*" markers in the timeline
//!
//! ## JavaScript API
//!
//! ```javascript
//! // Get detailed per-frame profiling data
//! const stats = JSON.parse(rource.getDetailedFrameStats());
//! console.log(`Scene update: ${stats.scene_update_ms.toFixed(2)}ms`);
//! console.log(`Render: ${stats.render_ms.toFixed(2)}ms`);
//! console.log(`WASM heap: ${(stats.wasm_heap_bytes / 1024 / 1024).toFixed(1)}MB`);
//! ```

use wasm_bindgen::JsCast;
use web_sys::Performance;

// ============================================================================
// Constants
// ============================================================================

/// Number of frame timing samples for averaging.
pub const PHASE_SAMPLE_COUNT: usize = 60;

// ============================================================================
// Performance API Helpers
// ============================================================================

/// Gets the browser Performance object.
#[inline]
fn get_performance() -> Option<Performance> {
    web_sys::window()?.performance()
}

/// High-precision timestamp in milliseconds.
#[inline]
pub fn now_ms() -> f64 {
    get_performance().map(|p| p.now()).unwrap_or(0.0)
}

/// Creates a Performance mark (shows up in DevTools Performance timeline).
///
/// Only active when `profiling` feature is enabled.
#[inline]
pub fn mark(name: &str) {
    #[cfg(feature = "profiling")]
    if let Some(perf) = get_performance() {
        let _ = perf.mark(name);
    }
    #[cfg(not(feature = "profiling"))]
    let _ = name;
}

/// Creates a Performance measure between two marks.
///
/// Only active when `profiling` feature is enabled.
#[inline]
pub fn measure(name: &str, start_mark: &str, end_mark: &str) {
    #[cfg(feature = "profiling")]
    if let Some(perf) = get_performance() {
        let _ = perf.measure_with_start_mark_and_end_mark(name, start_mark, end_mark);
    }
    #[cfg(not(feature = "profiling"))]
    {
        let _ = (name, start_mark, end_mark);
    }
}

/// Clears all Performance marks and measures (prevents memory leak in long sessions).
#[inline]
pub fn clear_marks() {
    #[cfg(feature = "profiling")]
    if let Some(perf) = get_performance() {
        let _ = perf.clear_marks();
        let _ = perf.clear_measures();
    }
}

// ============================================================================
// Frame Profiler
// ============================================================================

/// Phase timings for a single frame.
#[derive(Debug, Clone, Default)]
pub struct FrameTimings {
    /// Time spent applying commits and updating scene state (ms).
    pub scene_update_ms: f32,
    /// Time spent in render passes (ms).
    pub render_ms: f32,
    /// Time spent waiting for GPU (ms) - WebGPU only.
    pub gpu_wait_ms: f32,
    /// Time spent in post-processing effects (ms).
    pub effects_ms: f32,
    /// Total frame time (ms).
    pub total_ms: f32,
}

/// Per-frame profiler that tracks phase timings.
///
/// Use this to identify bottlenecks in the frame loop:
/// - Scene update: CPU-bound commit processing and physics
/// - Render: Draw call submission
/// - GPU wait: Time waiting for GPU to finish (WebGPU)
/// - Effects: Post-processing (bloom, shadows)
#[derive(Debug, Clone)]
pub struct FrameProfiler {
    /// Current frame's phase timings.
    current: FrameTimings,
    /// Rolling average of phase timings.
    averages: FrameTimings,
    /// Frame counter for clearing marks periodically.
    frame_count: u64,
    /// Phase start timestamps.
    phase_start: f64,
    /// Frame start timestamp.
    frame_start: f64,
    /// Rolling buffer for scene update times.
    scene_times: [f32; PHASE_SAMPLE_COUNT],
    /// Rolling buffer for render times.
    render_times: [f32; PHASE_SAMPLE_COUNT],
    /// Rolling buffer for gpu wait times.
    gpu_times: [f32; PHASE_SAMPLE_COUNT],
    /// Rolling buffer for effects times.
    effects_times: [f32; PHASE_SAMPLE_COUNT],
    /// Rolling buffer for total frame times.
    total_times: [f32; PHASE_SAMPLE_COUNT],
    /// Current index in rolling buffers.
    buffer_index: usize,
    /// Number of valid samples.
    sample_count: usize,
}

impl Default for FrameProfiler {
    fn default() -> Self {
        Self::new()
    }
}

impl FrameProfiler {
    /// Creates a new frame profiler.
    #[inline]
    pub fn new() -> Self {
        Self {
            current: FrameTimings::default(),
            averages: FrameTimings::default(),
            frame_count: 0,
            phase_start: 0.0,
            frame_start: 0.0,
            scene_times: [0.0; PHASE_SAMPLE_COUNT],
            render_times: [0.0; PHASE_SAMPLE_COUNT],
            gpu_times: [0.0; PHASE_SAMPLE_COUNT],
            effects_times: [0.0; PHASE_SAMPLE_COUNT],
            total_times: [0.0; PHASE_SAMPLE_COUNT],
            buffer_index: 0,
            sample_count: 0,
        }
    }

    /// Marks the start of a new frame.
    #[inline]
    pub fn begin_frame(&mut self) {
        self.frame_start = now_ms();
        self.current = FrameTimings::default();
        mark("rource:frame_start");
    }

    /// Marks the start of a phase.
    #[inline]
    pub fn begin_phase(&mut self, name: &str) {
        self.phase_start = now_ms();
        mark(&format!("rource:{name}_start"));
    }

    /// Marks the end of a phase and records its duration.
    #[inline]
    pub fn end_phase(&mut self, name: &str) {
        let end_time = now_ms();
        let duration = (end_time - self.phase_start) as f32;

        mark(&format!("rource:{name}_end"));
        measure(
            &format!("rource:{name}"),
            &format!("rource:{name}_start"),
            &format!("rource:{name}_end"),
        );

        match name {
            "scene_update" => self.current.scene_update_ms = duration,
            "render" => self.current.render_ms = duration,
            "gpu_wait" => self.current.gpu_wait_ms = duration,
            "effects" => self.current.effects_ms = duration,
            _ => {}
        }
    }

    /// Marks the end of the frame and updates rolling averages.
    #[inline]
    pub fn end_frame(&mut self) {
        let end_time = now_ms();
        self.current.total_ms = (end_time - self.frame_start) as f32;

        mark("rource:frame_end");
        measure("rource:frame", "rource:frame_start", "rource:frame_end");

        // Update rolling buffers
        self.scene_times[self.buffer_index] = self.current.scene_update_ms;
        self.render_times[self.buffer_index] = self.current.render_ms;
        self.gpu_times[self.buffer_index] = self.current.gpu_wait_ms;
        self.effects_times[self.buffer_index] = self.current.effects_ms;
        self.total_times[self.buffer_index] = self.current.total_ms;

        self.buffer_index = (self.buffer_index + 1) % PHASE_SAMPLE_COUNT;
        self.sample_count = (self.sample_count + 1).min(PHASE_SAMPLE_COUNT);

        // Calculate rolling averages
        if self.sample_count > 0 {
            let count = self.sample_count as f32;
            self.averages.scene_update_ms =
                self.scene_times[..self.sample_count].iter().sum::<f32>() / count;
            self.averages.render_ms =
                self.render_times[..self.sample_count].iter().sum::<f32>() / count;
            self.averages.gpu_wait_ms =
                self.gpu_times[..self.sample_count].iter().sum::<f32>() / count;
            self.averages.effects_ms =
                self.effects_times[..self.sample_count].iter().sum::<f32>() / count;
            self.averages.total_ms =
                self.total_times[..self.sample_count].iter().sum::<f32>() / count;
        }

        self.frame_count += 1;

        // Clear marks periodically to prevent memory leak (every 600 frames = ~10 seconds)
        if self.frame_count % 600 == 0 {
            clear_marks();
        }
    }

    /// Returns the current frame's timings.
    #[inline]
    pub fn current(&self) -> &FrameTimings {
        &self.current
    }

    /// Returns the rolling average timings.
    #[inline]
    pub fn averages(&self) -> &FrameTimings {
        &self.averages
    }

    /// Returns total frames profiled.
    #[inline]
    pub fn frame_count(&self) -> u64 {
        self.frame_count
    }
}

// ============================================================================
// WASM Memory Stats
// ============================================================================

/// WASM heap memory statistics.
#[derive(Debug, Clone, Default)]
pub struct WasmMemoryStats {
    /// Total WASM heap size in bytes.
    pub heap_bytes: usize,
    /// Estimated used heap in bytes (if available).
    pub used_bytes: usize,
}

impl WasmMemoryStats {
    /// Captures current WASM memory statistics.
    #[inline]
    pub fn capture() -> Self {
        let heap_bytes = wasm_bindgen::memory()
            .dyn_into::<js_sys::WebAssembly::Memory>()
            .ok()
            .and_then(|m| {
                m.buffer()
                    .dyn_into::<js_sys::ArrayBuffer>()
                    .ok()
                    .map(|buf| buf.byte_length() as usize)
            })
            .unwrap_or(0);

        Self {
            heap_bytes,
            used_bytes: 0, // Rust allocator doesn't expose this directly
        }
    }
}

// ============================================================================
// Detailed Frame Stats (for JavaScript API)
// ============================================================================

/// Detailed profiling statistics for export to JavaScript.
#[derive(Debug, Clone, Default)]
pub struct DetailedFrameStats {
    // Phase timings (current frame)
    pub scene_update_ms: f32,
    pub render_ms: f32,
    pub gpu_wait_ms: f32,
    pub effects_ms: f32,
    pub total_ms: f32,

    // Phase timings (rolling average)
    pub avg_scene_update_ms: f32,
    pub avg_render_ms: f32,
    pub avg_gpu_wait_ms: f32,
    pub avg_effects_ms: f32,
    pub avg_total_ms: f32,

    // Memory
    pub wasm_heap_bytes: usize,

    // Counters
    pub frame_count: u64,
}

impl DetailedFrameStats {
    /// Formats the stats as a JSON string for JavaScript consumption.
    pub fn to_json(&self) -> String {
        format!(
            r#"{{"sceneUpdateMs":{:.4},"renderMs":{:.4},"gpuWaitMs":{:.4},"effectsMs":{:.4},"totalMs":{:.4},"avgSceneUpdateMs":{:.4},"avgRenderMs":{:.4},"avgGpuWaitMs":{:.4},"avgEffectsMs":{:.4},"avgTotalMs":{:.4},"wasmHeapBytes":{},"frameCount":{}}}"#,
            self.scene_update_ms,
            self.render_ms,
            self.gpu_wait_ms,
            self.effects_ms,
            self.total_ms,
            self.avg_scene_update_ms,
            self.avg_render_ms,
            self.avg_gpu_wait_ms,
            self.avg_effects_ms,
            self.avg_total_ms,
            self.wasm_heap_bytes,
            self.frame_count,
        )
    }
}

// ============================================================================
// Tracing Integration
// ============================================================================

/// Initializes the tracing-web subscriber for browser console output.
///
/// Only active when `tracing` feature is enabled.
/// Call this once during initialization.
#[cfg(feature = "tracing")]
pub fn init_tracing() {
    use tracing_subscriber::layer::SubscriberExt;
    use tracing_subscriber::util::SubscriberInitExt;

    // Use tracing-web's console writer for WASM
    // MakeWebConsoleWriter provides better formatting than MakeConsoleWriter
    let fmt_layer = tracing_subscriber::fmt::layer()
        .with_ansi(false)
        .without_time()
        .with_writer(tracing_web::MakeWebConsoleWriter::default());

    tracing_subscriber::registry().with(fmt_layer).init();

    web_sys::console::log_1(&"Rource: tracing initialized - spans will appear in console".into());
}

/// No-op when tracing feature is not enabled.
#[cfg(not(feature = "tracing"))]
pub fn init_tracing() {
    // No-op
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_frame_timings_default() {
        let timings = FrameTimings::default();
        assert_eq!(timings.scene_update_ms, 0.0);
        assert_eq!(timings.render_ms, 0.0);
        assert_eq!(timings.total_ms, 0.0);
    }

    #[test]
    fn test_frame_profiler_new() {
        let profiler = FrameProfiler::new();
        assert_eq!(profiler.frame_count(), 0);
        assert_eq!(profiler.current().total_ms, 0.0);
    }

    #[test]
    fn test_frame_profiler_default() {
        let profiler = FrameProfiler::default();
        assert_eq!(profiler.frame_count(), 0);
    }

    #[test]
    fn test_wasm_memory_stats_default() {
        let stats = WasmMemoryStats::default();
        assert_eq!(stats.heap_bytes, 0);
    }

    #[test]
    fn test_detailed_frame_stats_to_json() {
        let stats = DetailedFrameStats {
            scene_update_ms: 1.5,
            render_ms: 2.5,
            gpu_wait_ms: 0.5,
            effects_ms: 0.3,
            total_ms: 4.8,
            avg_scene_update_ms: 1.4,
            avg_render_ms: 2.4,
            avg_gpu_wait_ms: 0.4,
            avg_effects_ms: 0.2,
            avg_total_ms: 4.4,
            wasm_heap_bytes: 1024 * 1024,
            frame_count: 100,
        };

        let json = stats.to_json();
        assert!(json.contains("sceneUpdateMs"));
        assert!(json.contains("1.5"));
        assert!(json.contains("wasmHeapBytes"));
        assert!(json.contains("1048576"));
    }

    #[test]
    fn test_detailed_frame_stats_default() {
        let stats = DetailedFrameStats::default();
        assert_eq!(stats.frame_count, 0);
        assert_eq!(stats.wasm_heap_bytes, 0);
    }
}
