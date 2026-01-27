# Error Budget Policy

**Status**: Active
**Created**: 2026-01-27
**Purpose**: Define error rate targets, alerting thresholds, and incident response triggers

---

## Overview

Rource implements error rate tracking to ensure reliability and enable proactive incident detection. This document defines the error budget policy, including target rates, alerting thresholds, and remediation procedures.

---

## Error Categories

| Category | Description | Examples |
|----------|-------------|----------|
| **Parse** | VCS log parsing failures | Malformed git log, invalid timestamps, unknown file actions |
| **Render** | Frame rendering failures | Buffer allocation failure, texture upload error |
| **WebGL** | GPU context errors | Shader compilation, program linking, context lost |
| **Config** | Configuration validation | Invalid settings values, unsupported options |
| **Asset** | Resource loading failures | Font loading, image decode errors |
| **I/O** | File/network operations | File not found, network timeout |

---

## Error Budget Targets

### Overall SLO

| Metric | Target | Warning | Critical |
|--------|--------|---------|----------|
| **Total Error Rate** | <0.1% | >0.05% | >0.1% |

### Per-Category Targets

| Category | Target Rate | Rationale |
|----------|-------------|-----------|
| **Parse** | <0.5% | User-provided input, expect some malformed data |
| **Render** | <0.01% | Should never fail during normal operation |
| **WebGL** | <0.1% | Device/browser compatibility issues |
| **Config** | <1.0% | User configuration errors acceptable |
| **Asset** | <0.5% | Network/loading issues |
| **I/O** | <0.5% | Network/file system issues |

---

## Alerting Thresholds

### Severity Levels

| Severity | Threshold | Response Time | Notification |
|----------|-----------|---------------|--------------|
| **Info** | >0.01% total | None | Dashboard |
| **Warning** | >0.05% total | 24 hours | Console warning |
| **Critical** | >0.1% total | 4 hours | Error overlay |
| **Emergency** | >1.0% total | Immediate | Disable feature |

### Category-Specific Alerts

| Category | Warning | Critical | Auto-Mitigation |
|----------|---------|----------|-----------------|
| Parse | >0.1% | >0.5% | Enable lenient mode |
| Render | >0.005% | >0.01% | Fallback to software |
| WebGL | >0.05% | >0.1% | Fallback to software |
| Config | >0.5% | >1.0% | Reset to defaults |
| Asset | >0.1% | >0.5% | Use fallback assets |
| I/O | >0.1% | >0.5% | Retry with backoff |

---

## Measurement Methodology

### Data Collection

Error metrics are collected at the WASM boundary layer:

```javascript
// Get error metrics from WASM
const metrics = JSON.parse(rource.getErrorMetrics());
// {
//   "parse": 0,
//   "render": 0,
//   "webgl": 0,
//   "config": 0,
//   "asset": 0,
//   "io": 0,
//   "total": 0,
//   "rate": 0.0
// }

// Check against threshold
if (rource.errorRateExceedsThreshold(0.1)) {
    showErrorAlert('Error rate too high');
}
```

### Rate Calculation

```
Error Rate = Total Errors / Total Operations × 100%
```

Operations are counted for both successful and failed executions to ensure accurate rate calculation.

### Sampling Period

| Use Case | Period | Minimum Operations |
|----------|--------|-------------------|
| Real-time monitoring | Per-session | 100 |
| Alerting | Rolling 5 minutes | 1000 |
| Reporting | Daily | 10000 |

---

## JavaScript Integration

### Basic Monitoring

```javascript
// Check error rate after each load operation
async function loadRepository(log) {
    try {
        const commits = rource.loadGitLog(log);
        console.log(`Loaded ${commits} commits`);
    } catch (error) {
        console.error('Load failed:', error);
    }

    // Check error metrics
    const errorRate = rource.getErrorRate();
    if (errorRate > 0.1) {
        console.warn(`Error rate: ${errorRate.toFixed(3)}%`);
    }
}
```

### Detailed Monitoring

```javascript
// Get detailed metrics for dashboard
function updateErrorDashboard() {
    const metrics = JSON.parse(rource.getDetailedErrorMetrics());

    document.getElementById('parse-errors').textContent = metrics.errors.parse;
    document.getElementById('parse-ops').textContent = metrics.operations.parse;
    document.getElementById('total-rate').textContent =
        (metrics.totals.rate * 100).toFixed(4) + '%';
}
```

### Threshold Alerts

```javascript
// Alerting logic
function checkErrorBudget() {
    // Warning at 0.05%
    if (rource.errorRateExceedsThreshold(0.05)) {
        console.warn('Error budget warning: rate exceeds 0.05%');
    }

    // Critical at 0.1%
    if (rource.errorRateExceedsThreshold(0.1)) {
        console.error('Error budget critical: rate exceeds 0.1%');
        showErrorOverlay('High error rate detected');
    }
}
```

---

## Incident Response

### Parse Error Surge

**Trigger**: Parse error rate >0.5%

**Response**:
1. Check input data format
2. Verify git log command output
3. Enable lenient parsing mode (already default)
4. If persists, file bug report with sample input

### Render Error Occurrence

**Trigger**: Any render error

**Response**:
1. Check WebGL context status
2. Verify canvas dimensions
3. Fall back to software renderer
4. Report device/browser information

### WebGL Context Lost

**Trigger**: WebGL context lost event

**Response**:
1. Automatically handled by backend fallback
2. Log browser/device information
3. Consider memory pressure if frequent

---

## Budget Exhaustion Procedure

When error budget is exhausted (>0.1% sustained):

1. **Immediate**: Display user-friendly error message
2. **Short-term**: Fall back to more reliable mode (software renderer)
3. **Investigation**: Collect error samples for analysis
4. **Resolution**: Fix root cause before re-enabling affected features
5. **Verification**: Confirm error rate returns to normal

---

## API Reference

### WASM Methods

| Method | Returns | Description |
|--------|---------|-------------|
| `getTotalErrors()` | `u64` | Total error count |
| `getTotalOperations()` | `u64` | Total operation count |
| `getParseErrorCount()` | `u64` | Parse error count |
| `getRenderErrorCount()` | `u64` | Render error count |
| `getWebGlErrorCount()` | `u64` | WebGL error count |
| `getConfigErrorCount()` | `u64` | Config error count |
| `getAssetErrorCount()` | `u64` | Asset error count |
| `getIoErrorCount()` | `u64` | I/O error count |
| `getErrorRate()` | `f64` | Total error rate (%) |
| `getParseErrorRate()` | `f64` | Parse error rate (%) |
| `errorRateExceedsThreshold(%)` | `bool` | Check vs threshold |
| `resetErrorMetrics()` | `void` | Reset all counters |
| `getErrorMetrics()` | `String` | JSON summary |
| `getDetailedErrorMetrics()` | `String` | JSON with operations |

---

## Rust Implementation

### Recording Errors

```rust
// In WASM boundary layer
pub fn load_git_log(&mut self, log: &str) -> Result<usize, JsValue> {
    // Record operation
    self.error_metrics.record_operation(ErrorCategory::Parse);

    let parser = GitParser::with_options(ParseOptions::lenient());
    let commits = parser.parse_str(log).map_err(|e| {
        // Record error
        self.error_metrics.record_error(ErrorCategory::Parse);
        JsValue::from_str(&format!("Parse error: {e}"))
    })?;

    Ok(self.load_commits_internal(commits))
}
```

### Error Categories

```rust
pub enum ErrorCategory {
    Parse = 0,   // VCS log parsing
    Render = 1,  // Frame rendering
    WebGl = 2,   // GPU context
    Config = 3,  // Configuration
    Asset = 4,   // Resource loading
    Io = 5,      // File/network I/O
}
```

---

## Success Criteria

OP-5 task is complete when:

- [x] Error categorization enum implemented
- [x] Error counters implemented
- [x] Error budget documentation created
- [x] Alerting thresholds documented
- [x] WASM API methods exposed
- [x] Integration with load operations

---

## References

- [Google SRE Book: Service Level Objectives](https://sre.google/sre-book/service-level-objectives/)
- [The Art of SLOs](https://sre.google/workbook/implementing-slos/)
- [docs/operations/RUNBOOK.md](./RUNBOOK.md) - Error response playbooks

---

*Document created: 2026-01-27*
*Last updated: 2026-01-27*
