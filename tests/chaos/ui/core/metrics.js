/**
 * Metrics Collector - Performance and resource tracking for chaos tests
 *
 * Collects heap usage, frame timing, error counts, and other metrics
 * during chaos test execution.
 */

export class MetricsCollector {
    constructor() {
        this.reset();
    }

    /**
     * Reset all metrics
     */
    reset() {
        this.frameTimings = [];
        this.errorCount = 0;
        this.wasmTrapCount = 0;
        this.memorySnapshots = [];
        this.domNodeCounts = [];
        this.customMetrics = {};
        this.startTime = performance.now();
    }

    // ========================================================================
    // Frame Timing
    // ========================================================================

    /**
     * Record a frame time
     */
    recordFrameTime(ms) {
        this.frameTimings.push({
            time: performance.now() - this.startTime,
            duration: ms,
        });

        // Keep only last 1000 frames
        if (this.frameTimings.length > 1000) {
            this.frameTimings.shift();
        }
    }

    /**
     * Get FPS statistics
     */
    getFpsStats() {
        if (this.frameTimings.length === 0) {
            return { min: 0, max: 0, avg: 0, p95: 0, p99: 0 };
        }

        const fps = this.frameTimings.map(f => 1000 / f.duration);
        const sorted = [...fps].sort((a, b) => a - b);

        return {
            min: sorted[0],
            max: sorted[sorted.length - 1],
            avg: fps.reduce((a, b) => a + b, 0) / fps.length,
            p95: this.percentile(sorted, 0.05),  // Lower is worse for FPS
            p99: this.percentile(sorted, 0.01),
        };
    }

    /**
     * Get frame time statistics
     */
    getFrameTimeStats() {
        if (this.frameTimings.length === 0) {
            return { min: 0, max: 0, avg: 0, p95: 0, p99: 0 };
        }

        const times = this.frameTimings.map(f => f.duration);
        const sorted = [...times].sort((a, b) => a - b);

        return {
            min: sorted[0],
            max: sorted[sorted.length - 1],
            avg: times.reduce((a, b) => a + b, 0) / times.length,
            p95: this.percentile(sorted, 0.95),
            p99: this.percentile(sorted, 0.99),
        };
    }

    // ========================================================================
    // Memory Tracking
    // ========================================================================

    /**
     * Take a memory snapshot
     */
    takeMemorySnapshot(label = '') {
        const snapshot = {
            time: performance.now() - this.startTime,
            label,
            heap: null,
            jsHeapSize: null,
        };

        // Use Performance Memory API if available (Chrome)
        if (performance.memory) {
            snapshot.heap = performance.memory.usedJSHeapSize;
            snapshot.jsHeapSize = performance.memory.totalJSHeapSize;
        }

        this.memorySnapshots.push(snapshot);
        return snapshot;
    }

    /**
     * Get memory statistics
     */
    getMemoryStats() {
        const heaps = this.memorySnapshots
            .filter(s => s.heap !== null)
            .map(s => s.heap);

        if (heaps.length === 0) {
            return { current: 0, peak: 0, avg: 0, growth: 0 };
        }

        return {
            current: heaps[heaps.length - 1],
            peak: Math.max(...heaps),
            avg: heaps.reduce((a, b) => a + b, 0) / heaps.length,
            growth: heaps[heaps.length - 1] - heaps[0],
        };
    }

    /**
     * Detect potential memory leaks
     */
    detectMemoryLeaks(thresholdGrowthMB = 50) {
        const stats = this.getMemoryStats();
        const growthMB = stats.growth / (1024 * 1024);

        return {
            detected: growthMB > thresholdGrowthMB,
            growthMB,
            threshold: thresholdGrowthMB,
        };
    }

    // ========================================================================
    // DOM Tracking
    // ========================================================================

    /**
     * Count DOM nodes
     */
    countDomNodes() {
        const count = document.getElementsByTagName('*').length;
        this.domNodeCounts.push({
            time: performance.now() - this.startTime,
            count,
        });
        return count;
    }

    /**
     * Get DOM node statistics
     */
    getDomNodeStats() {
        if (this.domNodeCounts.length === 0) {
            return { current: 0, peak: 0, avg: 0, growth: 0 };
        }

        const counts = this.domNodeCounts.map(d => d.count);

        return {
            current: counts[counts.length - 1],
            peak: Math.max(...counts),
            avg: counts.reduce((a, b) => a + b, 0) / counts.length,
            growth: counts[counts.length - 1] - counts[0],
        };
    }

    /**
     * Detect DOM node leaks
     */
    detectDomLeaks(thresholdGrowth = 100) {
        const stats = this.getDomNodeStats();

        return {
            detected: stats.growth > thresholdGrowth,
            growth: stats.growth,
            threshold: thresholdGrowth,
        };
    }

    // ========================================================================
    // Error Tracking
    // ========================================================================

    /**
     * Record an error
     */
    recordError(error) {
        this.errorCount++;
        return this.errorCount;
    }

    /**
     * Record a WASM trap
     */
    recordWasmTrap(trap) {
        this.wasmTrapCount++;
        return this.wasmTrapCount;
    }

    /**
     * Get error counts
     */
    getErrorCounts() {
        return {
            errors: this.errorCount,
            wasmTraps: this.wasmTrapCount,
            total: this.errorCount + this.wasmTrapCount,
        };
    }

    // ========================================================================
    // Custom Metrics
    // ========================================================================

    /**
     * Record a custom metric value
     */
    recordCustomMetric(name, value) {
        if (!this.customMetrics[name]) {
            this.customMetrics[name] = [];
        }
        this.customMetrics[name].push({
            time: performance.now() - this.startTime,
            value,
        });
    }

    /**
     * Get custom metric statistics
     */
    getCustomMetricStats(name) {
        const values = this.customMetrics[name];
        if (!values || values.length === 0) {
            return null;
        }

        const nums = values.map(v => v.value);
        const sorted = [...nums].sort((a, b) => a - b);

        return {
            count: nums.length,
            min: sorted[0],
            max: sorted[sorted.length - 1],
            avg: nums.reduce((a, b) => a + b, 0) / nums.length,
            p50: this.percentile(sorted, 0.50),
            p95: this.percentile(sorted, 0.95),
            p99: this.percentile(sorted, 0.99),
        };
    }

    // ========================================================================
    // Utility
    // ========================================================================

    /**
     * Calculate percentile
     */
    percentile(sortedArray, p) {
        if (sortedArray.length === 0) return 0;
        const index = Math.ceil(sortedArray.length * p) - 1;
        return sortedArray[Math.max(0, Math.min(index, sortedArray.length - 1))];
    }

    /**
     * Get snapshot of all metrics
     */
    getSnapshot() {
        return {
            fps: this.getFpsStats(),
            frameTime: this.getFrameTimeStats(),
            memory: this.getMemoryStats(),
            domNodes: this.getDomNodeStats(),
            errors: this.getErrorCounts(),
            duration: performance.now() - this.startTime,
            customMetrics: Object.fromEntries(
                Object.entries(this.customMetrics)
                    .map(([name, values]) => [name, this.getCustomMetricStats(name)])
            ),
        };
    }

    /**
     * Check if metrics pass thresholds
     */
    checkThresholds(thresholds = {}) {
        const defaults = {
            maxHeapMB: 512,
            maxFrameTimeP99Ms: 32,
            minFpsP95: 15,
            maxErrors: 0,
            maxWasmTraps: 0,
            maxDomNodeGrowth: 100,
        };

        const t = { ...defaults, ...thresholds };
        const snapshot = this.getSnapshot();
        const failures = [];

        // Heap check
        if (snapshot.memory.peak / (1024 * 1024) > t.maxHeapMB) {
            failures.push({
                metric: 'heapMB',
                threshold: t.maxHeapMB,
                actual: snapshot.memory.peak / (1024 * 1024),
            });
        }

        // Frame time check
        if (snapshot.frameTime.p99 > t.maxFrameTimeP99Ms) {
            failures.push({
                metric: 'frameTimeP99Ms',
                threshold: t.maxFrameTimeP99Ms,
                actual: snapshot.frameTime.p99,
            });
        }

        // FPS check
        if (snapshot.fps.p95 < t.minFpsP95 && snapshot.fps.p95 > 0) {
            failures.push({
                metric: 'fpsP95',
                threshold: t.minFpsP95,
                actual: snapshot.fps.p95,
            });
        }

        // Error check
        if (snapshot.errors.errors > t.maxErrors) {
            failures.push({
                metric: 'errors',
                threshold: t.maxErrors,
                actual: snapshot.errors.errors,
            });
        }

        // WASM trap check
        if (snapshot.errors.wasmTraps > t.maxWasmTraps) {
            failures.push({
                metric: 'wasmTraps',
                threshold: t.maxWasmTraps,
                actual: snapshot.errors.wasmTraps,
            });
        }

        // DOM node check
        if (snapshot.domNodes.growth > t.maxDomNodeGrowth) {
            failures.push({
                metric: 'domNodeGrowth',
                threshold: t.maxDomNodeGrowth,
                actual: snapshot.domNodes.growth,
            });
        }

        return {
            passed: failures.length === 0,
            failures,
            snapshot,
        };
    }
}

/**
 * Performance timeline for tracking operations
 */
export class PerformanceTimeline {
    constructor() {
        this.entries = [];
    }

    /**
     * Mark the start of an operation
     */
    start(name) {
        this.entries.push({
            name,
            type: 'start',
            time: performance.now(),
        });
    }

    /**
     * Mark the end of an operation
     */
    end(name) {
        this.entries.push({
            name,
            type: 'end',
            time: performance.now(),
        });
    }

    /**
     * Get duration of an operation
     */
    getDuration(name) {
        const start = this.entries.find(e => e.name === name && e.type === 'start');
        const end = this.entries.find(e => e.name === name && e.type === 'end');

        if (start && end) {
            return end.time - start.time;
        }
        return null;
    }

    /**
     * Get all durations
     */
    getAllDurations() {
        const durations = {};
        const starts = {};

        for (const entry of this.entries) {
            if (entry.type === 'start') {
                starts[entry.name] = entry.time;
            } else if (entry.type === 'end' && starts[entry.name]) {
                durations[entry.name] = entry.time - starts[entry.name];
            }
        }

        return durations;
    }

    /**
     * Clear the timeline
     */
    clear() {
        this.entries = [];
    }
}
