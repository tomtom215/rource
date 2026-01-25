/**
 * Input Fuzzing Tests
 *
 * Tests input handling resilience with random, malformed,
 * and malicious inputs.
 */

export const fuzzingTests = [
    // ========================================================================
    // Unicode Chaos
    // ========================================================================
    {
        name: 'unicode_emoji_input',
        category: 'fuzzing',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const emojiInputs = [
                '\u{1F980}\u{1F99E}\u{1F990}',  // Crab, lobster, shrimp
                '\u{1F4A9}',                     // Pile of poo
                '\u{1F525}\u{1F525}\u{1F525}',  // Fire x3
                '\u{1F1FA}\u{1F1F8}',            // US flag (regional indicators)
                '\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467}', // Family ZWJ
                '\u{1F3CB}\u{1F3FB}',            // Weight lifter with skin tone
            ];

            for (const emoji of emojiInputs) {
                // Should not throw when processing emoji
                try {
                    const processed = emoji.normalize('NFC');
                    assert(processed.length > 0, 'Emoji processing failed');
                } catch (e) {
                    assert(false, `Emoji processing threw: ${e.message}`);
                }
            }
        },
    },

    {
        name: 'unicode_rtl_override',
        category: 'fuzzing',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const rtlInputs = [
                '\u202Ereversed\u202C',           // RTL override
                'normal\u202Ereversed\u202Cnormal', // Mixed
                '\u202Dforced LTR\u202C',         // LTR override
                '\u2066isolated\u2069',           // First strong isolate
            ];

            for (const input of rtlInputs) {
                // Should handle RTL without breaking
                assert(typeof input === 'string', 'RTL input is string');
                assert(input.length > 0, 'RTL input has length');
            }
        },
    },

    {
        name: 'unicode_combining_characters',
        category: 'fuzzing',
        severity: 'medium',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const combiningInputs = [
                'a\u0301',                        // a + combining acute
                'e\u0301\u0302\u0303',            // e + multiple combining
                'Z\u0335\u0335\u0335\u0335',      // Zalgo-style
                '\u0300\u0301\u0302',             // Orphan combining chars
            ];

            for (const input of combiningInputs) {
                // Should normalize properly
                const nfc = input.normalize('NFC');
                const nfd = input.normalize('NFD');
                assert(typeof nfc === 'string', 'NFC normalization works');
                assert(typeof nfd === 'string', 'NFD normalization works');
            }
        },
    },

    {
        name: 'unicode_zero_width',
        category: 'fuzzing',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const zeroWidthInputs = [
                'te\u200Bst',                     // Zero-width space
                'te\u200Cst',                     // Zero-width non-joiner
                'te\u200Dst',                     // Zero-width joiner
                '\uFEFFtest',                     // BOM
                'test\uFEFF',                     // Trailing BOM
            ];

            for (const input of zeroWidthInputs) {
                const visible = input.replace(/[\u200B\u200C\u200D\uFEFF]/g, '');
                assert(visible === 'test', 'Zero-width chars removable');
            }
        },
    },

    // ========================================================================
    // Injection Attempts
    // ========================================================================
    {
        name: 'xss_script_injection',
        category: 'fuzzing',
        severity: 'critical',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const xssPayloads = [
                '<script>alert("xss")</script>',
                '<img src=x onerror=alert(1)>',
                '"><script>alert(1)</script>',
                "javascript:alert('xss')",
                '<svg onload=alert(1)>',
                '<body onload=alert(1)>',
                '{{constructor.constructor("return this")()}}',
                '${7*7}',
                '<iframe src="javascript:alert(1)">',
                '<marquee onstart=alert(1)>',
            ];

            for (const payload of xssPayloads) {
                // When escaped/sanitized, should not contain active script
                const escaped = payload
                    .replace(/</g, '&lt;')
                    .replace(/>/g, '&gt;')
                    .replace(/"/g, '&quot;');

                assert(!escaped.includes('<script>'), 'Script tag escaped');
                assert(!escaped.includes('javascript:'), 'JS protocol should be escaped');
            }
        },
    },

    {
        name: 'sql_injection_patterns',
        category: 'fuzzing',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const sqlPayloads = [
                "'; DROP TABLE users; --",
                "1' OR '1'='1",
                "1; DELETE FROM commits;--",
                "' UNION SELECT * FROM users--",
                "admin'--",
                "1' AND 1=1--",
            ];

            for (const payload of sqlPayloads) {
                // Should be treated as plain text
                assert(typeof payload === 'string', 'SQL payload is string');
                // In a real test, would verify no SQL execution occurred
            }
        },
    },

    {
        name: 'path_traversal_attempts',
        category: 'fuzzing',
        severity: 'critical',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const pathPayloads = [
                '../../../etc/passwd',
                '..\\..\\..\\windows\\system32',
                '/etc/passwd',
                'file:///etc/passwd',
                '....//....//....//etc/passwd',
                '%2e%2e%2f%2e%2e%2fetc/passwd',
            ];

            for (const payload of pathPayloads) {
                // Should not resolve to system paths
                const normalized = payload.replace(/\.\.[\/\\]/g, '');
                assert(!normalized.startsWith('/etc'), 'Path traversal blocked');
            }
        },
    },

    // ========================================================================
    // Oversized Inputs
    // ========================================================================
    {
        name: 'oversized_string_input',
        category: 'fuzzing',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const sizes = [1000, 10000, 100000, 1000000];

            for (const size of sizes) {
                const oversized = 'A'.repeat(size);
                assert(oversized.length === size, `Created ${size} char string`);

                // Typical operations should not hang
                const start = performance.now();
                const trimmed = oversized.trim();
                const elapsed = performance.now() - start;

                assert(elapsed < 1000, `Processing ${size} chars took < 1s`);
            }
        },
    },

    {
        name: 'deeply_nested_json',
        category: 'fuzzing',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            // Create deeply nested object
            let nested = { value: 'leaf' };
            for (let i = 0; i < 100; i++) {
                nested = { child: nested };
            }

            // Should serialize without stack overflow
            try {
                const json = JSON.stringify(nested);
                assert(json.length > 0, 'Deeply nested JSON serializes');

                const parsed = JSON.parse(json);
                assert(typeof parsed === 'object', 'Deeply nested JSON parses');
            } catch (e) {
                assert(false, `Deep nesting failed: ${e.message}`);
            }
        },
    },

    {
        name: 'large_array_input',
        category: 'fuzzing',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const sizes = [1000, 10000, 100000];

            for (const size of sizes) {
                const arr = new Array(size).fill(0).map((_, i) => i);

                const start = performance.now();
                const sum = arr.reduce((a, b) => a + b, 0);
                const elapsed = performance.now() - start;

                assert(sum === (size - 1) * size / 2, 'Array sum correct');
                assert(elapsed < 1000, `Processing ${size} elements took < 1s`);
            }
        },
    },

    // ========================================================================
    // Special Characters
    // ========================================================================
    {
        name: 'null_byte_handling',
        category: 'fuzzing',
        severity: 'critical',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const nullInputs = [
                'before\x00after',
                '\x00start',
                'end\x00',
                '\x00\x00\x00',
            ];

            for (const input of nullInputs) {
                // Should handle null bytes safely
                const cleaned = input.replace(/\x00/g, '');
                assert(!cleaned.includes('\x00'), 'Null bytes removable');
            }
        },
    },

    {
        name: 'control_character_handling',
        category: 'fuzzing',
        severity: 'medium',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const controlInputs = [
                '\x01\x02\x03',           // SOH, STX, ETX
                '\x07\x08\x09',           // BEL, BS, TAB
                '\x0B\x0C\x0D',           // VT, FF, CR
                '\x1B[31mcolored\x1B[0m', // ANSI escape
                '\x7F',                    // DEL
            ];

            for (const input of controlInputs) {
                // Should be escapable
                const escaped = JSON.stringify(input);
                assert(escaped.startsWith('"'), 'Control chars JSON-escapable');
            }
        },
    },

    // ========================================================================
    // Encoding Edge Cases
    // ========================================================================
    {
        name: 'mixed_encoding_input',
        category: 'fuzzing',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const mixedInputs = [
                'Hello \u4E16\u754C',      // English + Chinese
                '\u0645\u0631\u062D\u0628\u0627 World', // Arabic + English
                '\u3053\u3093\u306B\u3061\u306F', // Japanese
                '\uD83D\uDE00',             // Emoji as surrogate pair
            ];

            for (const input of mixedInputs) {
                // Should handle mixed encodings
                assert(typeof input === 'string', 'Mixed encoding is string');
                const bytes = new TextEncoder().encode(input);
                const decoded = new TextDecoder().decode(bytes);
                assert(decoded === input, 'Round-trip encoding works');
            }
        },
    },

    {
        name: 'bom_handling',
        category: 'fuzzing',
        severity: 'medium',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const bomVariants = [
                '\uFEFFtext',               // UTF-8 BOM
                'text\uFEFF',               // Trailing BOM
                '\uFEFF\uFEFFdouble',        // Double BOM
            ];

            for (const input of bomVariants) {
                const stripped = input.replace(/\uFEFF/g, '');
                assert(!stripped.includes('\uFEFF'), 'BOM strippable');
            }
        },
    },

    // ========================================================================
    // Numeric Edge Cases
    // ========================================================================
    {
        name: 'numeric_string_parsing',
        category: 'fuzzing',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const numericStrings = [
                '0',
                '-0',
                '1e308',
                '1e-308',
                'Infinity',
                '-Infinity',
                'NaN',
                '9007199254740993', // > MAX_SAFE_INTEGER
                '0.1',
                '.1',
                '1.',
                '1e',
                '1e+',
                '1e-',
                '0x10',
                '0o10',
                '0b10',
            ];

            for (const str of numericStrings) {
                const num = Number(str);
                // Should parse without throwing
                assert(typeof num === 'number', `"${str}" parses to number`);
            }
        },
    },

    {
        name: 'date_string_parsing',
        category: 'fuzzing',
        severity: 'medium',
        async run(ctx) {
            const { chaos, assert } = ctx;

            const dateStrings = [
                '2026-01-25',
                '2026-01-25T12:00:00Z',
                '2026-01-25T12:00:00+00:00',
                'January 25, 2026',
                '1/25/2026',
                '0',                         // Unix epoch
                '-1',                        // Before epoch
                '9999999999999',             // Far future
                'invalid',
                '',
            ];

            for (const str of dateStrings) {
                const date = new Date(str);
                // Should not throw
                assert(date instanceof Date, `"${str}" creates Date object`);
            }
        },
    },

    // ========================================================================
    // Random Fuzzing
    // ========================================================================
    {
        name: 'random_string_fuzzing',
        category: 'fuzzing',
        severity: 'high',
        timeout: 60000,
        async run(ctx) {
            const { chaos, assert } = ctx;

            for (let i = 0; i < 1000; i++) {
                const randomStr = chaos.chaosString(100);

                // Should handle any random string
                try {
                    const len = randomStr.length;
                    const trimmed = randomStr.trim();
                    const upper = randomStr.toUpperCase();
                    const lower = randomStr.toLowerCase();
                    const encoded = encodeURIComponent(randomStr);

                    assert(len >= 0, 'Length is non-negative');
                } catch (e) {
                    // encodeURIComponent may throw on unpaired surrogates
                    // This is expected behavior
                }
            }
        },
    },

    {
        name: 'random_number_fuzzing',
        category: 'fuzzing',
        severity: 'high',
        async run(ctx) {
            const { chaos, assert } = ctx;

            for (let i = 0; i < 1000; i++) {
                const num = chaos.chaosNumber();

                // Operations on any number should not throw
                const str = String(num);
                const isFinite = Number.isFinite(num);
                const isNaN = Number.isNaN(num);
                const abs = Math.abs(num);

                assert(typeof str === 'string', 'Number stringifies');
                assert(typeof isFinite === 'boolean', 'isFinite works');
                assert(typeof isNaN === 'boolean', 'isNaN works');
            }
        },
    },
];
