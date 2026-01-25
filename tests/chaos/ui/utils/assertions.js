/**
 * Custom Assertions for Chaos Testing
 *
 * Provides additional assertion helpers for chaos tests.
 */

/**
 * Assert that a value is within tolerance of expected
 */
export function assertApprox(actual, expected, tolerance = 0.001, message) {
    const diff = Math.abs(actual - expected);
    if (diff > tolerance) {
        throw new Error(message || `Expected ${actual} to be within ${tolerance} of ${expected}`);
    }
}

/**
 * Assert that a value is a valid number (not NaN, not Infinity)
 */
export function assertValidNumber(value, message) {
    if (!Number.isFinite(value)) {
        throw new Error(message || `Expected ${value} to be a valid finite number`);
    }
}

/**
 * Assert that an array has no duplicates
 */
export function assertNoDuplicates(array, message) {
    const set = new Set(array);
    if (set.size !== array.length) {
        throw new Error(message || `Expected array to have no duplicates`);
    }
}

/**
 * Assert that a function completes within a time limit
 */
export async function assertCompletesBefore(fn, timeoutMs, message) {
    const start = performance.now();
    await fn();
    const elapsed = performance.now() - start;
    if (elapsed > timeoutMs) {
        throw new Error(message || `Expected to complete in ${timeoutMs}ms, took ${elapsed.toFixed(0)}ms`);
    }
}

/**
 * Assert that memory usage stays below threshold
 */
export function assertMemoryBelow(thresholdMB, message) {
    if (performance.memory) {
        const usedMB = performance.memory.usedJSHeapSize / (1024 * 1024);
        if (usedMB > thresholdMB) {
            throw new Error(message || `Memory usage ${usedMB.toFixed(1)}MB exceeds ${thresholdMB}MB`);
        }
    }
}

/**
 * Assert that a string is valid UTF-8
 */
export function assertValidUtf8(str, message) {
    try {
        const encoded = new TextEncoder().encode(str);
        const decoded = new TextDecoder().decode(encoded);
        if (decoded !== str) {
            throw new Error('Round-trip failed');
        }
    } catch (e) {
        throw new Error(message || `String is not valid UTF-8: ${e.message}`);
    }
}

/**
 * Assert that an object matches a shape
 */
export function assertShape(obj, shape, message) {
    for (const [key, expectedType] of Object.entries(shape)) {
        const actualType = typeof obj[key];
        if (actualType !== expectedType) {
            throw new Error(
                message || `Expected ${key} to be ${expectedType}, got ${actualType}`
            );
        }
    }
}

/**
 * Assert that no console errors occurred during a function
 */
export async function assertNoConsoleErrors(fn) {
    const errors = [];
    const originalError = console.error;
    console.error = (...args) => {
        errors.push(args);
        originalError.apply(console, args);
    };

    try {
        await fn();
    } finally {
        console.error = originalError;
    }

    if (errors.length > 0) {
        throw new Error(`Console errors occurred: ${errors.length}`);
    }
}
