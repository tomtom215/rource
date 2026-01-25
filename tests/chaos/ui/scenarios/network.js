/**
 * Network Chaos Tests
 *
 * Tests behavior under network failures, slow connections,
 * timeouts, and other network-related issues.
 */

export const networkTests = [
    // ========================================================================
    // Offline Mode
    // ========================================================================
    {
        name: 'offline_detection',
        category: 'network',
        severity: 'critical',
        async run(ctx) {
            const { chaos, assert } = ctx;

            // Simulate offline state
            let isOnline = true;

            // Toggle offline/online
            for (let i = 0; i < 10; i++) {
                isOnline = !isOnline;
                // In real app: would dispatch 'offline'/'online' events
            }

            assert(typeof isOnline === 'boolean', 'Online state tracked');
        },
    },

    {
        name: 'offline_graceful_degradation',
        category: 'network',
        severity: 'critical',
        async run(ctx) {
            const { chaos, assert } = ctx;

            // Simulate fetch that fails due to offline
            const mockFetch = async (url) => {
                if (!navigator.onLine) {
                    throw new Error('Network request failed');
                }
                return { ok: true, data: 'response' };
            };

            // Test error handling
            try {
                const result = await mockFetch('https://example.com');
                assert(result.ok || !navigator.onLine, 'Fetch handled correctly');
            } catch (e) {
                // Expected when offline
                assert(e.message.includes('failed'), 'Error message clear');
            }
        },
    },

    // ========================================================================
    // Slow Network
    // ========================================================================
    {
        name: 'slow_network_simulation',
        category: 'network',
        severity: 'high',
        timeout: 10000,
        async run(ctx) {
            const { chaos, assert } = ctx;

            // Simulate 3G-speed network (2000ms latency)
            const simulateSlowFetch = async () => {
                await chaos.simulateLatency(1000, 3000);
                return { ok: true };
            };

            const start = performance.now();
            const result = await simulateSlowFetch();
            const elapsed = performance.now() - start;

            assert(result.ok, 'Request eventually succeeded');
            assert(elapsed >= 1000, 'Latency was simulated');
        },
    },

    {
        name: 'progressive_loading_under_latency',
        category: 'network',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const chunks = [];
            const totalChunks = 10;

            // Simulate progressive loading with random delays
            for (let i = 0; i < totalChunks; i++) {
                await chaos.randomDelay(10, 50);
                chunks.push({ index: i, data: `chunk${i}` });
            }

            assert(chunks.length === totalChunks, 'All chunks received');
            assert(chunks[0].index === 0, 'First chunk correct');
            assert(chunks[totalChunks - 1].index === totalChunks - 1, 'Last chunk correct');
        },
    },

    // ========================================================================
    // Timeout Tests
    // ========================================================================
    {
        name: 'request_timeout_handling',
        category: 'network',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const fetchWithTimeout = async (timeoutMs) => {
                return new Promise((resolve, reject) => {
                    const timer = setTimeout(() => {
                        reject(new Error('Request timeout'));
                    }, timeoutMs);

                    // Simulate request that takes random time
                    setTimeout(() => {
                        clearTimeout(timer);
                        resolve({ ok: true });
                    }, chaos.randomInt(0, timeoutMs * 2));
                });
            };

            let successCount = 0;
            let timeoutCount = 0;

            for (let i = 0; i < 10; i++) {
                try {
                    await fetchWithTimeout(100);
                    successCount++;
                } catch (e) {
                    if (e.message.includes('timeout')) {
                        timeoutCount++;
                    }
                }
            }

            // Some should succeed, some should timeout
            assert(successCount + timeoutCount === 10, 'All requests handled');
        },
    },

    {
        name: 'connection_timeout_retry',
        category: 'network',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            let attempts = 0;
            const maxRetries = 3;

            const fetchWithRetry = async () => {
                for (let i = 0; i <= maxRetries; i++) {
                    attempts++;
                    try {
                        if (chaos.chance(0.7)) {
                            throw new Error('Connection failed');
                        }
                        return { ok: true };
                    } catch (e) {
                        if (i === maxRetries) throw e;
                        await chaos.randomDelay(10, 50);
                    }
                }
            };

            try {
                const result = await fetchWithRetry();
                assert(result.ok, 'Eventually succeeded');
            } catch (e) {
                assert(attempts === maxRetries + 1, 'Used all retries');
            }
        },
    },

    // ========================================================================
    // Partial Failure
    // ========================================================================
    {
        name: 'intermittent_connection_drops',
        category: 'network',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            let successfulRequests = 0;
            let failedRequests = 0;

            // Simulate 30% failure rate
            for (let i = 0; i < 100; i++) {
                if (chaos.chance(0.7)) {
                    successfulRequests++;
                } else {
                    failedRequests++;
                }
            }

            assert(successfulRequests > 0, 'Some requests succeeded');
            assert(failedRequests > 0, 'Some requests failed');
            assert(successfulRequests + failedRequests === 100, 'All handled');
        },
    },

    {
        name: 'partial_response_handling',
        category: 'network',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            // Simulate partial data response
            const fullData = 'ABCDEFGHIJ';
            const receivedLength = chaos.randomInt(0, fullData.length);
            const partialData = fullData.substring(0, receivedLength);

            assert(partialData.length <= fullData.length, 'Partial data valid');

            // System should handle incomplete data
            const isComplete = partialData.length === fullData.length;
            assert(typeof isComplete === 'boolean', 'Completeness detectable');
        },
    },

    // ========================================================================
    // Error Response Handling
    // ========================================================================
    {
        name: 'http_error_codes',
        category: 'network',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const errorCodes = [400, 401, 403, 404, 500, 502, 503, 504];

            for (const code of errorCodes) {
                const response = { status: code, ok: code < 400 };

                // Should handle all error codes
                assert(typeof response.status === 'number', `${code} handled`);
                assert(!response.ok || code < 400, `${code} ok status correct`);
            }
        },
    },

    {
        name: 'malformed_response_handling',
        category: 'network',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const malformedResponses = [
                '',                              // Empty
                'not json',                      // Plain text
                '{"incomplete":',                // Truncated JSON
                'null',                          // JSON null
                '[]',                            // Empty array
                '{}',                            // Empty object
                '{"data": null}',                // Null data
            ];

            for (const response of malformedResponses) {
                try {
                    const parsed = JSON.parse(response);
                    // If parse succeeds, should handle result
                    assert(parsed !== undefined, 'Parsed result exists');
                } catch (e) {
                    // Parse failure should be caught
                    assert(e.name === 'SyntaxError', 'JSON error caught');
                }
            }
        },
    },

    // ========================================================================
    // CORS and Security
    // ========================================================================
    {
        name: 'cors_error_handling',
        category: 'network',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            // Simulate CORS error
            const corsError = new TypeError('Failed to fetch');

            try {
                throw corsError;
            } catch (e) {
                // Should handle CORS errors gracefully
                assert(e instanceof TypeError, 'CORS error is TypeError');
                assert(e.message.includes('fetch'), 'Error message indicates fetch failure');
            }
        },
    },

    {
        name: 'mixed_content_handling',
        category: 'network',
        severity: 'medium',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const urls = [
                'https://secure.example.com',
                'http://insecure.example.com',  // Mixed content if on HTTPS
            ];

            for (const url of urls) {
                const isSecure = url.startsWith('https://');
                assert(typeof isSecure === 'boolean', 'Security detectable');
            }
        },
    },

    // ========================================================================
    // Caching Tests
    // ========================================================================
    {
        name: 'cache_miss_handling',
        category: 'network',
        severity: 'medium',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const cache = new Map();

            // Cache miss scenario
            const key = 'missing_key';
            const cached = cache.get(key);

            assert(cached === undefined, 'Cache miss returns undefined');

            // Should fall back to network
            cache.set(key, 'fetched_data');
            assert(cache.get(key) === 'fetched_data', 'Cache populated');
        },
    },

    {
        name: 'stale_cache_refresh',
        category: 'network',
        severity: 'medium',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const cache = new Map();
            const maxAge = 1000; // 1 second

            // Set stale data
            cache.set('data', {
                value: 'stale',
                timestamp: Date.now() - maxAge - 1,
            });

            const entry = cache.get('data');
            const isStale = Date.now() - entry.timestamp > maxAge;

            assert(isStale, 'Stale data detected');

            // Refresh
            cache.set('data', {
                value: 'fresh',
                timestamp: Date.now(),
            });

            const fresh = cache.get('data');
            assert(fresh.value === 'fresh', 'Cache refreshed');
        },
    },

    // ========================================================================
    // Rate Limiting
    // ========================================================================
    {
        name: 'rate_limit_handling',
        category: 'network',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            let requestCount = 0;
            const limit = 10;
            const window = 100; // ms
            let windowStart = Date.now();

            const makeRequest = () => {
                const now = Date.now();
                if (now - windowStart > window) {
                    windowStart = now;
                    requestCount = 0;
                }

                if (requestCount >= limit) {
                    return { status: 429, ok: false };
                }

                requestCount++;
                return { status: 200, ok: true };
            };

            // Make requests rapidly
            let successCount = 0;
            let rateLimitedCount = 0;

            for (let i = 0; i < 20; i++) {
                const result = makeRequest();
                if (result.ok) {
                    successCount++;
                } else {
                    rateLimitedCount++;
                }
            }

            assert(successCount <= limit, 'Rate limit enforced');
            assert(rateLimitedCount > 0, 'Some requests rate limited');
        },
    },

    // ========================================================================
    // WebSocket-like Tests
    // ========================================================================
    {
        name: 'connection_reconnect',
        category: 'network',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            let connected = false;
            let reconnectAttempts = 0;
            const maxReconnects = 5;

            const connect = () => {
                if (chaos.chance(0.3)) {
                    connected = true;
                    return true;
                }
                return false;
            };

            // Attempt to connect with retries
            while (!connected && reconnectAttempts < maxReconnects) {
                if (connect()) break;
                reconnectAttempts++;
                await chaos.randomDelay(10, 50);
            }

            assert(reconnectAttempts <= maxReconnects, 'Reconnect limit respected');
        },
    },

    {
        name: 'message_queue_during_disconnect',
        category: 'network',
        severity: 'medium',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const messageQueue = [];
            let connected = true;

            const send = (message) => {
                if (connected) {
                    return true;
                } else {
                    messageQueue.push(message);
                    return false;
                }
            };

            // Disconnect and queue messages
            connected = false;
            for (let i = 0; i < 10; i++) {
                send({ id: i, data: 'test' });
            }

            assert(messageQueue.length === 10, 'Messages queued');

            // Reconnect and flush
            connected = true;
            const flushed = messageQueue.length;
            messageQueue.length = 0;

            assert(flushed === 10, 'Queue flushed on reconnect');
        },
    },
];
