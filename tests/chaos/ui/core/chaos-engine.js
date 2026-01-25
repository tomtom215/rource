/**
 * Chaos Engine - Core utilities for chaos testing
 *
 * Provides chaos injection utilities, random generators,
 * and simulation helpers for UI/UX chaos tests.
 */

export class ChaosEngine {
    constructor() {
        this.seed = Date.now();
        this.state = this.seed;
        this.injectedChaos = [];
        this.metrics = {
            chaosEventsInjected: 0,
            errorsTriggered: 0,
            recoveriesSuccessful: 0,
        };
    }

    /**
     * Seeded random number generator (LCG)
     */
    random() {
        this.state = (this.state * 1664525 + 1013904223) >>> 0;
        return this.state / 4294967296;
    }

    /**
     * Random integer in range [min, max)
     */
    randomInt(min, max) {
        return Math.floor(this.random() * (max - min)) + min;
    }

    /**
     * Random float in range [min, max)
     */
    randomFloat(min, max) {
        return this.random() * (max - min) + min;
    }

    /**
     * Random delay promise
     */
    randomDelay(minMs, maxMs) {
        const delay = this.randomInt(minMs, maxMs);
        return new Promise(resolve => setTimeout(resolve, delay));
    }

    /**
     * Random boolean with probability
     */
    chance(probability = 0.5) {
        return this.random() < probability;
    }

    /**
     * Pick random element from array
     */
    pick(array) {
        return array[this.randomInt(0, array.length)];
    }

    /**
     * Shuffle array (Fisher-Yates)
     */
    shuffle(array) {
        const result = [...array];
        for (let i = result.length - 1; i > 0; i--) {
            const j = this.randomInt(0, i + 1);
            [result[i], result[j]] = [result[j], result[i]];
        }
        return result;
    }

    // ========================================================================
    // Chaos Injection Utilities
    // ========================================================================

    /**
     * Generate chaotic string with edge cases
     */
    chaosString(length = 50) {
        const chaosChars = [
            // Normal
            'a', 'b', 'c', '1', '2', '3', ' ',
            // Whitespace
            '\t', '\n', '\r',
            // Unicode
            '\u0000', '\uFEFF', '\u200B', '\u200C', '\u200D',
            // Emoji
            '\u{1F980}', '\u{1F4A9}', '\u{1F525}',
            // RTL
            '\u202E', '\u202D', '\u202C',
            // Combining
            '\u0300', '\u0301', '\u0302',
            // Replacement
            '\uFFFD',
        ];

        let result = '';
        for (let i = 0; i < length; i++) {
            result += this.pick(chaosChars);
        }
        return result;
    }

    /**
     * Generate injection attempt string
     */
    injectionString() {
        const injections = [
            '<script>alert("xss")</script>',
            '"; DROP TABLE users; --',
            '../../../etc/passwd',
            '{{constructor.constructor("return this")()}}',
            '${7*7}',
            '%00',
            '\x00',
            'javascript:alert(1)',
            'data:text/html,<script>alert(1)</script>',
            '<img src=x onerror=alert(1)>',
            '"><script>alert(1)</script>',
            "'; exec xp_cmdshell('dir'); --",
        ];
        return this.pick(injections);
    }

    /**
     * Generate chaotic number
     */
    chaosNumber() {
        const values = [
            0, -0, 1, -1,
            0.1, -0.1, 0.0001, -0.0001,
            Number.MAX_VALUE, Number.MIN_VALUE,
            Number.MAX_SAFE_INTEGER, Number.MIN_SAFE_INTEGER,
            Number.POSITIVE_INFINITY, Number.NEGATIVE_INFINITY,
            Number.NaN,
            Number.EPSILON,
            1e100, 1e-100,
            -1e100, -1e-100,
        ];
        return this.pick(values);
    }

    /**
     * Generate chaotic coordinate
     */
    chaosCoord() {
        if (this.chance(0.1)) {
            return this.chaosNumber();
        }
        return this.randomFloat(-10000, 10000);
    }

    /**
     * Simulate network latency
     */
    async simulateLatency(minMs = 0, maxMs = 5000) {
        await this.randomDelay(minMs, maxMs);
        this.metrics.chaosEventsInjected++;
    }

    /**
     * Simulate network failure
     */
    async simulateNetworkFailure(failureRate = 0.3) {
        if (this.chance(failureRate)) {
            this.metrics.chaosEventsInjected++;
            throw new Error('Simulated network failure');
        }
    }

    /**
     * Simulate memory pressure
     */
    simulateMemoryPressure(sizeMB = 100) {
        const arrays = [];
        try {
            for (let i = 0; i < sizeMB; i++) {
                arrays.push(new Uint8Array(1024 * 1024));
            }
            this.metrics.chaosEventsInjected++;
        } finally {
            // Allow GC
            arrays.length = 0;
        }
    }

    /**
     * Simulate slow device
     */
    async simulateSlowDevice(operation, slowdownFactor = 10) {
        const start = performance.now();
        const result = await operation();
        const elapsed = performance.now() - start;
        await this.randomDelay(0, elapsed * slowdownFactor);
        this.metrics.chaosEventsInjected++;
        return result;
    }

    // ========================================================================
    // Event Simulation
    // ========================================================================

    /**
     * Create synthetic mouse event
     */
    createMouseEvent(type, x, y, options = {}) {
        return new MouseEvent(type, {
            bubbles: true,
            cancelable: true,
            clientX: x,
            clientY: y,
            button: options.button || 0,
            buttons: options.buttons || 1,
            shiftKey: options.shiftKey || false,
            ctrlKey: options.ctrlKey || false,
            altKey: options.altKey || false,
            metaKey: options.metaKey || false,
            ...options,
        });
    }

    /**
     * Create synthetic touch event
     */
    createTouchEvent(type, touches) {
        const touchList = touches.map((t, i) => ({
            identifier: i,
            clientX: t.x,
            clientY: t.y,
            target: t.target || document.body,
        }));

        return new TouchEvent(type, {
            bubbles: true,
            cancelable: true,
            touches: touchList,
            targetTouches: touchList,
            changedTouches: touchList,
        });
    }

    /**
     * Create synthetic wheel event
     */
    createWheelEvent(deltaX, deltaY, x, y, options = {}) {
        return new WheelEvent('wheel', {
            bubbles: true,
            cancelable: true,
            deltaX,
            deltaY,
            deltaMode: options.deltaMode || 0,
            clientX: x,
            clientY: y,
            ...options,
        });
    }

    /**
     * Create synthetic keyboard event
     */
    createKeyboardEvent(type, key, options = {}) {
        return new KeyboardEvent(type, {
            bubbles: true,
            cancelable: true,
            key,
            code: options.code || key,
            keyCode: options.keyCode || key.charCodeAt(0),
            shiftKey: options.shiftKey || false,
            ctrlKey: options.ctrlKey || false,
            altKey: options.altKey || false,
            metaKey: options.metaKey || false,
            ...options,
        });
    }

    /**
     * Dispatch rapid events
     */
    async dispatchRapidEvents(element, eventFactory, count, delayMs = 0) {
        for (let i = 0; i < count; i++) {
            const event = eventFactory(i);
            element.dispatchEvent(event);
            if (delayMs > 0) {
                await this.randomDelay(0, delayMs);
            }
        }
        this.metrics.chaosEventsInjected += count;
    }

    // ========================================================================
    // Screen Simulation
    // ========================================================================

    /**
     * Device profiles for simulation
     */
    static DEVICE_PROFILES = {
        'iphone-se': { width: 320, height: 568, pixelRatio: 2, touch: true },
        'iphone-12': { width: 390, height: 844, pixelRatio: 3, touch: true },
        'iphone-12-pro-max': { width: 428, height: 926, pixelRatio: 3, touch: true },
        'ipad': { width: 768, height: 1024, pixelRatio: 2, touch: true },
        'ipad-pro': { width: 1024, height: 1366, pixelRatio: 2, touch: true },
        'android-small': { width: 360, height: 640, pixelRatio: 2, touch: true },
        'android-large': { width: 412, height: 915, pixelRatio: 2.6, touch: true },
        'laptop': { width: 1366, height: 768, pixelRatio: 1, touch: false },
        'desktop': { width: 1920, height: 1080, pixelRatio: 1, touch: false },
        '4k': { width: 3840, height: 2160, pixelRatio: 1, touch: false },
        'ultrawide': { width: 3440, height: 1440, pixelRatio: 1, touch: false },
    };

    /**
     * Get random device profile
     */
    randomDeviceProfile() {
        const profiles = Object.keys(ChaosEngine.DEVICE_PROFILES);
        const name = this.pick(profiles);
        return { name, ...ChaosEngine.DEVICE_PROFILES[name] };
    }

    /**
     * Simulate viewport resize
     */
    simulateViewportResize(width, height) {
        window.dispatchEvent(new Event('resize'));
        this.metrics.chaosEventsInjected++;
        return { width, height };
    }

    /**
     * Simulate orientation change
     */
    simulateOrientationChange(isLandscape) {
        window.dispatchEvent(new Event('orientationchange'));
        this.metrics.chaosEventsInjected++;
        return isLandscape;
    }

    // ========================================================================
    // DOM Chaos
    // ========================================================================

    /**
     * Temporarily remove element
     */
    async temporarilyRemoveElement(element, durationMs = 100) {
        const parent = element.parentNode;
        const nextSibling = element.nextSibling;

        if (parent) {
            parent.removeChild(element);
            this.metrics.chaosEventsInjected++;

            await this.randomDelay(durationMs, durationMs * 2);

            if (nextSibling) {
                parent.insertBefore(element, nextSibling);
            } else {
                parent.appendChild(element);
            }
            this.metrics.recoveriesSuccessful++;
        }
    }

    /**
     * Inject random style changes
     */
    injectStyleChaos(element) {
        const originalStyle = element.style.cssText;

        const chaosStyles = [
            { transform: 'rotate(180deg)' },
            { opacity: '0' },
            { visibility: 'hidden' },
            { display: 'none' },
            { position: 'fixed', top: '-9999px' },
            { width: '0', height: '0' },
            { pointerEvents: 'none' },
        ];

        const chaos = this.pick(chaosStyles);
        Object.assign(element.style, chaos);
        this.metrics.chaosEventsInjected++;

        // Return restore function
        return () => {
            element.style.cssText = originalStyle;
            this.metrics.recoveriesSuccessful++;
        };
    }

    // ========================================================================
    // Timing Chaos
    // ========================================================================

    /**
     * Inject timing jitter
     */
    async injectTimingJitter(operation, maxJitterMs = 100) {
        await this.randomDelay(0, maxJitterMs);
        const result = await operation();
        await this.randomDelay(0, maxJitterMs);
        this.metrics.chaosEventsInjected++;
        return result;
    }

    /**
     * Run with timeout chaos
     */
    async runWithTimeoutChaos(operation, timeoutMs = 5000, failureRate = 0.1) {
        if (this.chance(failureRate)) {
            this.metrics.errorsTriggered++;
            throw new Error('Simulated timeout');
        }

        return new Promise((resolve, reject) => {
            const timer = setTimeout(() => {
                this.metrics.errorsTriggered++;
                reject(new Error('Operation timed out'));
            }, timeoutMs);

            Promise.resolve(operation())
                .then(result => {
                    clearTimeout(timer);
                    resolve(result);
                })
                .catch(err => {
                    clearTimeout(timer);
                    reject(err);
                });
        });
    }

    // ========================================================================
    // State Chaos
    // ========================================================================

    /**
     * Create corrupted state object
     */
    createCorruptedState(template) {
        const corrupted = JSON.parse(JSON.stringify(template));

        const corruptValue = (obj, path = []) => {
            for (const key of Object.keys(obj)) {
                if (this.chance(0.3)) {
                    const type = typeof obj[key];
                    if (type === 'number') {
                        obj[key] = this.chaosNumber();
                    } else if (type === 'string') {
                        obj[key] = this.chaosString(20);
                    } else if (type === 'boolean') {
                        obj[key] = this.pick([true, false, null, undefined, 0, 1, '', 'true']);
                    } else if (Array.isArray(obj[key])) {
                        if (this.chance(0.5)) {
                            obj[key] = [];
                        } else {
                            obj[key].push(this.chaosNumber());
                        }
                    } else if (type === 'object' && obj[key] !== null) {
                        corruptValue(obj[key], [...path, key]);
                    }
                }
            }
        };

        corruptValue(corrupted);
        this.metrics.chaosEventsInjected++;
        return corrupted;
    }

    // ========================================================================
    // Metrics
    // ========================================================================

    /**
     * Get current metrics
     */
    getMetrics() {
        return { ...this.metrics };
    }

    /**
     * Reset metrics
     */
    resetMetrics() {
        this.metrics = {
            chaosEventsInjected: 0,
            errorsTriggered: 0,
            recoveriesSuccessful: 0,
        };
    }

    /**
     * Reset seed
     */
    resetSeed(seed = Date.now()) {
        this.seed = seed;
        this.state = seed;
    }
}

// Export singleton instance
export const chaos = new ChaosEngine();
