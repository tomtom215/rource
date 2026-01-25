/**
 * Chaos Test Runner - Orchestrates chaos test execution
 *
 * Manages test discovery, execution, timing, and result collection.
 */

import { ChaosEngine } from './chaos-engine.js';
import { MetricsCollector } from './metrics.js';
import { ChaosReporter } from './reporter.js';

export class ChaosTestRunner {
    constructor(options = {}) {
        this.options = {
            timeout: 30000,           // Default test timeout
            parallel: false,          // Run tests in parallel
            stopOnFail: false,        // Stop on first failure
            verbose: options.verbose || false,
            categories: options.categories || null, // Filter by category
            testFilter: options.testFilter || null, // Filter by test name
            seed: options.seed || Date.now(),
            ...options,
        };

        this.chaos = new ChaosEngine();
        this.chaos.resetSeed(this.options.seed);

        this.metrics = new MetricsCollector();
        this.reporter = new ChaosReporter();

        this.tests = [];
        this.results = [];
        this.startTime = null;
        this.endTime = null;

        // Test lifecycle hooks
        this.hooks = {
            beforeAll: [],
            afterAll: [],
            beforeEach: [],
            afterEach: [],
        };
    }

    /**
     * Register a test
     */
    test(testDef) {
        this.tests.push({
            name: testDef.name,
            category: testDef.category || 'general',
            severity: testDef.severity || 'medium',
            timeout: testDef.timeout || this.options.timeout,
            run: testDef.run,
            skip: testDef.skip || false,
            only: testDef.only || false,
        });
    }

    /**
     * Register multiple tests
     */
    tests(testDefs) {
        for (const def of testDefs) {
            this.test(def);
        }
    }

    /**
     * Register lifecycle hook
     */
    hook(type, fn) {
        if (this.hooks[type]) {
            this.hooks[type].push(fn);
        }
    }

    /**
     * Get tests to run (after filtering)
     */
    getTestsToRun() {
        let filtered = [...this.tests];

        // Check for .only tests
        const onlyTests = filtered.filter(t => t.only);
        if (onlyTests.length > 0) {
            filtered = onlyTests;
        }

        // Filter by category
        if (this.options.categories) {
            const cats = this.options.categories.split(',').map(c => c.trim());
            filtered = filtered.filter(t => cats.includes(t.category));
        }

        // Filter by test name
        if (this.options.testFilter) {
            const pattern = new RegExp(this.options.testFilter, 'i');
            filtered = filtered.filter(t => pattern.test(t.name));
        }

        // Remove skipped tests
        filtered = filtered.filter(t => !t.skip);

        return filtered;
    }

    /**
     * Run all registered tests
     */
    async run() {
        this.startTime = Date.now();
        this.results = [];

        const testsToRun = this.getTestsToRun();
        const skippedCount = this.tests.length - testsToRun.length;

        if (this.options.verbose) {
            console.log(`\nChaos Test Suite`);
            console.log(`================`);
            console.log(`Seed: ${this.options.seed}`);
            console.log(`Total tests: ${this.tests.length}`);
            console.log(`Running: ${testsToRun.length}`);
            console.log(`Skipped: ${skippedCount}\n`);
        }

        // Run beforeAll hooks
        for (const hook of this.hooks.beforeAll) {
            await hook(this.createContext());
        }

        // Run tests
        if (this.options.parallel) {
            await this.runParallel(testsToRun);
        } else {
            await this.runSequential(testsToRun);
        }

        // Run afterAll hooks
        for (const hook of this.hooks.afterAll) {
            await hook(this.createContext());
        }

        this.endTime = Date.now();

        return this.generateReport();
    }

    /**
     * Run tests sequentially
     */
    async runSequential(tests) {
        for (const test of tests) {
            const result = await this.runTest(test);
            this.results.push(result);

            if (!result.passed && this.options.stopOnFail) {
                break;
            }
        }
    }

    /**
     * Run tests in parallel
     */
    async runParallel(tests) {
        const promises = tests.map(test => this.runTest(test));
        this.results = await Promise.all(promises);
    }

    /**
     * Run a single test
     */
    async runTest(test) {
        const result = {
            name: test.name,
            category: test.category,
            severity: test.severity,
            passed: false,
            skipped: false,
            duration: 0,
            error: null,
            metrics: null,
            assertions: [],
        };

        if (this.options.verbose) {
            process.stdout.write(`  ${test.category}/${test.name}... `);
        }

        const startTime = performance.now();

        try {
            // Create test context
            const ctx = this.createContext(test);

            // Run beforeEach hooks
            for (const hook of this.hooks.beforeEach) {
                await hook(ctx);
            }

            // Run test with timeout
            await this.runWithTimeout(
                () => test.run(ctx),
                test.timeout
            );

            result.passed = true;
            result.assertions = ctx.assertions;

        } catch (error) {
            result.passed = false;
            result.error = {
                message: error.message,
                stack: error.stack,
            };
        }

        result.duration = performance.now() - startTime;
        result.metrics = this.metrics.getSnapshot();

        // Run afterEach hooks
        try {
            for (const hook of this.hooks.afterEach) {
                await hook(this.createContext(test));
            }
        } catch (hookError) {
            // Log but don't fail test
            console.warn(`afterEach hook failed: ${hookError.message}`);
        }

        if (this.options.verbose) {
            if (result.passed) {
                console.log(`PASS (${result.duration.toFixed(0)}ms)`);
            } else {
                console.log(`FAIL`);
                console.log(`    Error: ${result.error.message}`);
            }
        }

        return result;
    }

    /**
     * Create test context
     */
    createContext(test = null) {
        const ctx = {
            test,
            chaos: this.chaos,
            metrics: this.metrics,
            assertions: [],

            // Assertion helpers
            assert(condition, message = 'Assertion failed') {
                ctx.assertions.push({ condition, message });
                if (!condition) {
                    throw new Error(message);
                }
            },

            assertEqual(actual, expected, message) {
                const msg = message || `Expected ${expected}, got ${actual}`;
                ctx.assert(actual === expected, msg);
            },

            assertNotEqual(actual, expected, message) {
                const msg = message || `Expected not ${expected}`;
                ctx.assert(actual !== expected, msg);
            },

            assertThrows(fn, message = 'Expected function to throw') {
                let threw = false;
                try {
                    fn();
                } catch (e) {
                    threw = true;
                }
                ctx.assert(threw, message);
            },

            async assertThrowsAsync(fn, message = 'Expected async function to throw') {
                let threw = false;
                try {
                    await fn();
                } catch (e) {
                    threw = true;
                }
                ctx.assert(threw, message);
            },

            assertInRange(value, min, max, message) {
                const msg = message || `Expected ${value} to be in range [${min}, ${max}]`;
                ctx.assert(value >= min && value <= max, msg);
            },

            assertFinite(value, message) {
                const msg = message || `Expected ${value} to be finite`;
                ctx.assert(Number.isFinite(value), msg);
            },

            assertNoErrors(errorList, message) {
                const msg = message || `Expected no errors, got ${errorList.length}`;
                ctx.assert(errorList.length === 0, msg);
            },

            // Timing helpers
            async wait(ms) {
                return new Promise(resolve => setTimeout(resolve, ms));
            },

            async waitForCondition(condition, timeoutMs = 5000, intervalMs = 100) {
                const start = Date.now();
                while (Date.now() - start < timeoutMs) {
                    if (await condition()) {
                        return true;
                    }
                    await ctx.wait(intervalMs);
                }
                throw new Error('Condition not met within timeout');
            },
        };

        return ctx;
    }

    /**
     * Run function with timeout
     */
    async runWithTimeout(fn, timeoutMs) {
        return new Promise((resolve, reject) => {
            const timer = setTimeout(() => {
                reject(new Error(`Test timed out after ${timeoutMs}ms`));
            }, timeoutMs);

            Promise.resolve(fn())
                .then(result => {
                    clearTimeout(timer);
                    resolve(result);
                })
                .catch(error => {
                    clearTimeout(timer);
                    reject(error);
                });
        });
    }

    /**
     * Generate test report
     */
    generateReport() {
        const passed = this.results.filter(r => r.passed).length;
        const failed = this.results.filter(r => !r.passed && !r.skipped).length;
        const skipped = this.results.filter(r => r.skipped).length;

        const report = {
            timestamp: new Date().toISOString(),
            duration: this.endTime - this.startTime,
            seed: this.options.seed,
            summary: {
                total: this.results.length,
                passed,
                failed,
                skipped,
                passRate: this.results.length > 0
                    ? (passed / this.results.length) * 100
                    : 0,
            },
            categories: this.aggregateByCategory(),
            failures: this.results.filter(r => !r.passed && !r.skipped),
            results: this.results,
            chaosMetrics: this.chaos.getMetrics(),
        };

        return report;
    }

    /**
     * Aggregate results by category
     */
    aggregateByCategory() {
        const categories = {};

        for (const result of this.results) {
            if (!categories[result.category]) {
                categories[result.category] = {
                    total: 0,
                    passed: 0,
                    failed: 0,
                    skipped: 0,
                    duration: 0,
                };
            }

            categories[result.category].total++;
            categories[result.category].duration += result.duration;

            if (result.skipped) {
                categories[result.category].skipped++;
            } else if (result.passed) {
                categories[result.category].passed++;
            } else {
                categories[result.category].failed++;
            }
        }

        return categories;
    }
}

/**
 * Create a test suite
 */
export function createChaosTestSuite(name, options = {}) {
    const runner = new ChaosTestRunner({ ...options, suiteName: name });
    return runner;
}
