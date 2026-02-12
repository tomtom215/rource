// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Animation Module Facade
 *
 * This module re-exports all animation-related functionality from the
 * modularized core and UI modules. It maintains backward compatibility
 * with existing imports while providing a cleaner architecture.
 *
 * Architecture:
 * - core/frame-scheduler.js: High-performance frame scheduling (FrameScheduler class)
 * - core/animation-loop.js: Main animation loop and canvas management
 * - core/performance-metrics.js: FPS tracking and metrics display
 * - ui/playback-ui.js: Playback controls and timeline UI
 *
 * @module animation
 */

// =============================================================================
// Core Animation Exports
// =============================================================================

export {
    // Animation loop control
    animate,
    startAnimation,
    stopAnimation,
    restartAnimation,
    isAnimating,
    // Canvas management
    resizeCanvas,
    debouncedResize,
    // Callbacks
    setUIUpdateCallback,
    // Idle mode (Level 2 power management)
    wakeFromIdle,
    isIdleMode,
    // Initialization
    initAnimation,
} from './core/animation-loop.js';

// =============================================================================
// Frame Scheduler Exports
// =============================================================================

export {
    FrameScheduler,
    getFrameScheduler,
    isHighPerformanceSchedulerAvailable,
} from './core/frame-scheduler.js';

// =============================================================================
// Performance Metrics Exports
// =============================================================================

export {
    // FPS statistics
    updateFpsStats,
    resetUncappedFpsStats,
    getUncappedFpsStats,
    // Metrics display
    updatePerfMetrics,
    trackFramePerformance,
    // Throttling helpers
    incrementPerfCounter,
    shouldUpdatePerfMetrics,
    resetPerfCounter,
} from './core/performance-metrics.js';

// =============================================================================
// Playback UI Exports
// =============================================================================

export {
    updatePlaybackUI,
    resetTimelineDateLabels,
    isAtEnd,
    setPlaybackStateCallback,
} from './ui/playback-ui.js';
