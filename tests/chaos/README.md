# Rource Chaos Testing Suite

A comprehensive chaos testing framework for ensuring the Rource WASM and UI/UX demo is production-ready for any device, any edge case, and any user behavior.

## Overview

This testing suite implements **chaos engineering principles** to validate system resilience:

| Category | Tests | Description |
|----------|-------|-------------|
| WASM Stability | 45+ | Memory pressure, API boundaries, invalid inputs |
| Input Fuzzing | 30+ | Random/malicious inputs, encoding edge cases |
| Rapid Interactions | 25+ | Spam clicks, rapid state changes, race conditions |
| Network Chaos | 15+ | Offline, slow networks, partial failures |
| Device Simulation | 20+ | Screen sizes, orientations, performance tiers |
| Edge Cases | 50+ | Empty repos, massive repos, unicode, dates |

**Total: 185+ chaos scenarios**

## Quick Start

```bash
# Run all chaos tests
./scripts/run-chaos-tests.sh

# Run specific category
./scripts/run-chaos-tests.sh --category wasm
./scripts/run-chaos-tests.sh --category ui
./scripts/run-chaos-tests.sh --category network

# Run with verbose output
./scripts/run-chaos-tests.sh --verbose

# Generate HTML report
./scripts/run-chaos-tests.sh --report
```

## Test Categories

### 1. WASM Stability Tests (`wasm/`)

Tests the Rust/WASM boundary for robustness:

| Test | Description | Severity |
|------|-------------|----------|
| `memory_pressure` | OOM conditions, large allocations | Critical |
| `api_boundaries` | All public API edge cases | Critical |
| `invalid_inputs` | Null, undefined, wrong types | High |
| `concurrent_calls` | Race conditions, async chaos | High |
| `state_corruption` | Invalid state transitions | Critical |
| `panic_recovery` | Graceful panic handling | Critical |

### 2. Input Fuzzing Tests (`ui/scenarios/fuzzing.js`)

Tests input handling resilience:

| Test | Description | Severity |
|------|-------------|----------|
| `unicode_injection` | Emoji, RTL, combining chars | High |
| `script_injection` | XSS attempts in inputs | Critical |
| `oversized_inputs` | Massive strings, deep objects | High |
| `special_characters` | Null bytes, control chars | Medium |
| `encoding_chaos` | Invalid UTF-8, mixed encodings | High |

### 3. Rapid Interaction Tests (`ui/scenarios/rapid.js`)

Tests UI under stress:

| Test | Description | Severity |
|------|-------------|----------|
| `button_spam` | 100+ clicks/second | High |
| `slider_chaos` | Rapid seek operations | High |
| `zoom_storm` | Continuous zoom in/out | Medium |
| `resize_flood` | Rapid window resizing | High |
| `toggle_storm` | Rapid setting changes | Medium |

### 4. Network Chaos Tests (`ui/scenarios/network.js`)

Tests offline and degraded network:

| Test | Description | Severity |
|------|-------------|----------|
| `offline_mode` | Complete network failure | Critical |
| `slow_network` | 3G-speed throttling | High |
| `partial_failure` | Intermittent drops | High |
| `timeout_chaos` | Random request timeouts | Medium |
| `cors_errors` | Cross-origin failures | High |

### 5. Device Simulation Tests (`ui/scenarios/devices.js`)

Tests cross-device compatibility:

| Test | Description | Severity |
|------|-------------|----------|
| `mobile_portrait` | iPhone SE (320x568) | Critical |
| `mobile_landscape` | iPhone landscape | High |
| `tablet_portrait` | iPad portrait | High |
| `4k_display` | 3840x2160 | Medium |
| `low_dpi` | 1x pixel ratio | Medium |
| `high_dpi` | 3x pixel ratio | High |
| `touch_only` | No mouse available | Critical |

### 6. Edge Case Tests (`ui/scenarios/edge-cases.js`)

Tests obscure but real scenarios:

| Test | Description | Severity |
|------|-------------|----------|
| `empty_repo` | Repository with 0 commits | Critical |
| `single_commit` | Only 1 commit | High |
| `massive_repo` | 100,000+ commits | Critical |
| `deep_paths` | 50+ directory depth | High |
| `binary_files` | Files with null bytes | Medium |
| `future_dates` | Commits in year 2099 | Medium |
| `epoch_dates` | Commits at Unix epoch | High |
| `negative_zoom` | Zoom < 0 attempts | High |
| `infinite_values` | NaN, Infinity inputs | Critical |

## Test Fixtures

Located in `fixtures/`:

| Fixture | Description | Size |
|---------|-------------|------|
| `empty.log` | Empty log file | 0 bytes |
| `single-commit.log` | Minimal valid log | 50 bytes |
| `unicode-hell.log` | All unicode edge cases | 5 KB |
| `massive.log` | 100K commits | 15 MB |
| `malformed.log` | Invalid format variations | 2 KB |
| `injection.log` | XSS/injection attempts | 1 KB |

## Architecture

```
tests/chaos/
├── README.md              # This file
├── wasm/
│   ├── mod.rs             # WASM chaos test module
│   ├── memory_tests.rs    # Memory pressure tests
│   ├── api_tests.rs       # API boundary tests
│   ├── state_tests.rs     # State corruption tests
│   └── panic_tests.rs     # Panic recovery tests
├── ui/
│   ├── core/
│   │   ├── test-runner.js      # Test orchestration
│   │   ├── chaos-engine.js     # Chaos injection utilities
│   │   ├── metrics.js          # Performance measurement
│   │   └── reporter.js         # Report generation
│   ├── scenarios/
│   │   ├── fuzzing.js          # Input fuzzing tests
│   │   ├── rapid.js            # Rapid interaction tests
│   │   ├── network.js          # Network chaos tests
│   │   ├── devices.js          # Device simulation tests
│   │   └── edge-cases.js       # Edge case tests
│   └── utils/
│       ├── mock-wasm.js        # WASM mock for isolation
│       ├── dom-simulator.js    # DOM event simulation
│       └── assertions.js       # Custom assertions
├── fixtures/
│   ├── empty.log
│   ├── single-commit.log
│   ├── unicode-hell.log
│   ├── massive.log
│   ├── malformed.log
│   └── injection.log
└── reports/
    └── .gitkeep
```

## Metrics Collected

Every test run collects:

| Metric | Description | Threshold |
|--------|-------------|-----------|
| `heap_usage_mb` | Peak heap memory | < 512 MB |
| `frame_time_p99` | 99th percentile frame | < 32 ms |
| `fps_min` | Minimum FPS during test | > 15 |
| `error_count` | Uncaught exceptions | 0 |
| `wasm_trap_count` | WASM traps/panics | 0 |
| `memory_leaks` | Unreleased allocations | 0 |
| `dom_nodes_leaked` | Orphaned DOM nodes | 0 |

## Report Format

Reports are generated in `reports/` with:

```
reports/
├── chaos-report-2026-01-25T12-00-00.json   # Machine-readable
├── chaos-report-2026-01-25T12-00-00.html   # Human-readable
└── chaos-report-latest.html                 # Symlink to latest
```

### JSON Report Schema

```json
{
  "timestamp": "2026-01-25T12:00:00.000Z",
  "duration_ms": 45000,
  "environment": {
    "browser": "Chrome 120",
    "os": "Linux",
    "wasm_backend": "wgpu"
  },
  "summary": {
    "total": 185,
    "passed": 183,
    "failed": 1,
    "skipped": 1,
    "pass_rate": 98.9
  },
  "categories": [...],
  "failures": [...],
  "metrics": {...}
}
```

## CI Integration

Add to `.github/workflows/chaos.yml`:

```yaml
name: Chaos Testing
on:
  push:
    branches: [main, develop]
  schedule:
    - cron: '0 2 * * *'  # Nightly at 2 AM

jobs:
  chaos:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: browser-actions/setup-chrome@latest
      - run: ./scripts/run-chaos-tests.sh --headless --report
      - uses: actions/upload-artifact@v4
        with:
          name: chaos-report
          path: tests/chaos/reports/
```

## Writing New Tests

### WASM Tests (Rust)

```rust
#[test]
fn chaos_test_name() {
    let chaos = ChaosContext::new();

    // Inject chaos condition
    chaos.inject_memory_pressure(256 * 1024 * 1024);

    // Run scenario
    let result = scene.update(0.016);

    // Validate resilience
    assert!(result.is_ok(), "Should handle memory pressure gracefully");
    chaos.verify_no_leaks();
}
```

### UI Tests (JavaScript)

```javascript
export const testRapidPlayPause = {
    name: 'rapid_play_pause',
    category: 'rapid',
    severity: 'high',
    timeout: 10000,

    async run(ctx) {
        const { wasm, metrics, chaos } = ctx;

        // Inject chaos
        for (let i = 0; i < 100; i++) {
            wasm.togglePlay();
            await chaos.randomDelay(0, 10);
        }

        // Validate stability
        ctx.assert(metrics.errorCount === 0, 'No errors during rapid toggle');
        ctx.assert(metrics.fps > 15, 'FPS remained acceptable');
    }
};
```

## Debugging Failed Tests

1. **View detailed logs**: `./scripts/run-chaos-tests.sh --verbose`
2. **Run single test**: `./scripts/run-chaos-tests.sh --test rapid_play_pause`
3. **Enable tracing**: `CHAOS_TRACE=1 ./scripts/run-chaos-tests.sh`
4. **Capture screenshots**: `./scripts/run-chaos-tests.sh --screenshots`

## Contributing

When adding new chaos tests:

1. Identify a real-world failure scenario
2. Create a reproducible test case
3. Set appropriate severity (Critical/High/Medium/Low)
4. Define pass/fail criteria with measurable thresholds
5. Document the expected behavior
6. Add to appropriate category file
