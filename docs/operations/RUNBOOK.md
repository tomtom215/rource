# Operational Runbook

**Status**: Active
**Task ID**: DOC-3
**Last Updated**: 2026-01-26

---

## Table of Contents

1. [Overview](#overview)
2. [Incident Response](#incident-response)
3. [Performance Issues](#performance-issues)
4. [Memory Issues](#memory-issues)
5. [Rendering Issues](#rendering-issues)
6. [Browser-Specific Issues](#browser-specific-issues)
7. [Deployment Issues](#deployment-issues)
8. [Error Rate Issues](#error-rate-issues)
9. [Monitoring and Alerting](#monitoring-and-alerting)

---

## Overview

This runbook provides operational procedures for diagnosing and resolving issues with Rource deployments.

### Quick Reference

| Issue | First Check | Escalation |
|-------|-------------|------------|
| Low FPS | Entity count, GPU physics | Performance tuning section |
| High memory | Entity count, label count | Memory issues section |
| Rendering artifacts | Browser console, WebGL errors | Rendering issues section |
| Crash | Browser console, WASM errors | Check fuzz/crash artifacts |

---

## Incident Response

### Severity Levels

| Level | Description | Response Time | Example |
|-------|-------------|---------------|---------|
| P0 | Complete outage | Immediate | Demo site down |
| P1 | Major degradation | 1 hour | <10 FPS on typical repo |
| P2 | Minor issue | 24 hours | UI element misaligned |
| P3 | Cosmetic | Next release | Typo in label |

### Incident Checklist

1. **Acknowledge**: Confirm the issue
2. **Assess**: Determine severity and scope
3. **Communicate**: Update status if public-facing
4. **Investigate**: Use relevant playbook below
5. **Resolve**: Implement fix or workaround
6. **Document**: Update this runbook if needed

---

## Performance Issues

### Playbook: Low Frame Rate (<30 FPS)

**Symptoms**:
- Stuttering animation
- Delayed response to input
- Browser "slow script" warnings

**Diagnosis Steps**:

```javascript
// 1. Check entity count
console.log('Entities:', rource.getTotalEntities());

// 2. Check renderer type
console.log('Renderer:', rource.getRendererType());

// 3. Check GPU acceleration status
console.log('GPU Accelerated:', rource.isGPUAccelerated());

// 4. Check frame time
console.log('Frame time:', rource.getFrameTimeMs(), 'ms');
```

**Resolution by Cause**:

| Cause | Solution |
|-------|----------|
| High entity count (>20k) | Enable GPU physics: `rource.setUseGPUCulling(true)` |
| GPU physics disabled | Lower threshold: `rource.setGPUCullingThreshold(5000)` |
| Software renderer | Refresh page, check WebGL support |
| Many visible labels | Zoom out or reduce label limit |

**Expected Outcomes**:
- Small repo (1k entities): 60+ FPS
- Medium repo (10k entities): 60+ FPS with GPU physics
- Large repo (50k entities): 30+ FPS with GPU physics

### Playbook: Frame Rate Drops During Playback

**Symptoms**:
- FPS drops when commits are being applied
- Spike in frame time during activity

**Diagnosis**:
```javascript
console.log('Current commit:', rource.currentCommit());
console.log('Playback speed:', rource.getSpeed());
```

**Resolution**:
1. Reduce playback speed: `rource.setSpeed(0.5)` (was 0.1)
2. Skip idle periods: Already automatic
3. Enable commit batching (if available)

---

## Memory Issues

### Playbook: High Memory Usage (>2GB)

**Symptoms**:
- Browser tab using excessive memory
- Page becomes unresponsive
- OOM crashes

**Diagnosis**:
```javascript
// Check entity counts
console.log('Files:', rource.getTotalFiles());
console.log('Directories:', rource.getTotalDirectories());
console.log('Users:', rource.getTotalUsers());

// Check visible entity counts
console.log('Visible files:', rource.getVisibleFiles());
console.log('Visible users:', rource.getVisibleUsers());
```

**Resolution by Cause**:

| Cause | Solution |
|-------|----------|
| Large repository | Reduce max commits: reload with smaller log |
| Memory leak | Refresh page; report to issue tracker |
| Label accumulation | Disable labels or reduce max_labels |

**Prevention**:
- For repos >100k commits, use `--max-commits 50000`
- Monitor memory growth over time

### Playbook: Memory Growth Over Time

**Symptoms**:
- Memory slowly increases during playback
- No immediate issue, but eventual OOM

**Diagnosis**:
```javascript
// Take snapshots every 5 minutes
setInterval(() => {
    console.log('Memory snapshot:', performance.memory?.usedJSHeapSize);
}, 300000);
```

**Resolution**:
1. Document growth rate
2. If >5% growth per 30 minutes, file bug report
3. Workaround: Periodic page refresh

---

## Rendering Issues

### Playbook: Black Screen

**Symptoms**:
- Canvas is entirely black
- No error in console

**Diagnosis**:
```javascript
// Check if scene is loaded
console.log('Scene loaded:', rource.isSceneLoaded());
console.log('Entity count:', rource.getEntityCount());

// Check camera position
console.log('Zoom:', rource.getZoom());
console.log('Center:', rource.getCenter());
```

**Resolution**:

| Cause | Solution |
|-------|----------|
| No data loaded | Check log parsing completed |
| Zoomed out too far | Reset zoom: `rource.resetCamera()` |
| Camera at wrong position | Call `rource.autoFitCamera()` |
| WebGL context lost | Refresh page |

### Playbook: WebGL Context Lost

**Symptoms**:
- "WebGL context lost" in console
- Rendering stops, black canvas

**Diagnosis**:
```javascript
console.log('Context lost:', rource.isContextLost());
```

**Resolution**:
1. Refresh the page
2. If recurring:
   - Close other WebGL-heavy tabs
   - Update GPU drivers
   - Try different browser

### Playbook: Visual Artifacts

**Symptoms**:
- Flickering
- Z-fighting (overlapping elements)
- Missing elements

**Diagnosis**:
```javascript
console.log('Renderer:', rource.getRendererType());
console.log('Bloom enabled:', rource.isBloomEnabled());
```

**Resolution**:

| Artifact | Solution |
|----------|----------|
| Flickering | Disable bloom: `rource.setBloomEnabled(false)` |
| Z-fighting | Zoom in; report as bug |
| Missing elements | Check visibility: `rource.setDebugMode(true)` |

---

## Browser-Specific Issues

### Firefox Performance Issues

**Known Issue**: GPU compute shaders are slow on Firefox.

**Workaround**: Already implemented - GPU physics disabled on Firefox.

**Verification**:
```javascript
console.log('GPU Physics:', rource.isGPUPhysicsActive());
// Should be false on Firefox
```

### Safari WebGPU Issues

**Known Issue**: WebGPU API differences on Safari.

**Workaround**: Falls back to WebGL2.

**Verification**:
```javascript
console.log('Renderer:', rource.getRendererType());
// May show 'webgl2' instead of 'webgpu'
```

### Mobile Browser Issues

**Common Issues**:
- Touch targets too small
- Reduced performance
- Memory constraints

**Mitigations**:
1. Enable mobile mode: `rource.setMobileMode(true)`
2. Reduce entity limits
3. Disable bloom effects

---

## Deployment Issues

### Playbook: GitHub Pages Deployment Failed

**Diagnosis**:
1. Check workflow run: Actions tab
2. Look for build errors in logs

**Common Causes**:

| Error | Solution |
|-------|----------|
| WASM build failed | Check Rust version, rebuild |
| Test failure | Fix failing test first |
| Asset too large | Check WASM size limit |

### Playbook: Demo Site 503 Error

**Symptoms**:
- Demo site returns 503
- Usually on fresh load

**Cause**: GitHub Pages CDN rate limiting during cold start.

**Resolution**:
1. Wait 30 seconds, retry
2. If persistent, check GitHub Status

---

## Error Rate Issues

### Playbook: High Error Rate (>0.1%)

**Symptoms**:
- Parse failures on valid-looking logs
- Multiple operations failing
- Console showing repeated error messages

**Diagnosis**:
```javascript
// 1. Check overall error rate
console.log('Error rate:', rource.getErrorRate().toFixed(4) + '%');

// 2. Get detailed error breakdown
const metrics = JSON.parse(rource.getDetailedErrorMetrics());
console.log('Parse errors:', metrics.errors.parse, '/', metrics.operations.parse);
console.log('Render errors:', metrics.errors.render, '/', metrics.operations.render);
console.log('WebGL errors:', metrics.errors.webgl, '/', metrics.operations.webgl);

// 3. Check if threshold exceeded
if (rource.errorRateExceedsThreshold(0.1)) {
    console.warn('Error budget exhausted!');
}
```

**Resolution by Category**:

| Category | Threshold | Resolution |
|----------|-----------|------------|
| Parse >0.5% | Check input format | Verify git log command, check encoding |
| Render >0.01% | Check WebGL status | Fall back to software renderer |
| WebGL >0.1% | Check browser support | Refresh page, try different browser |
| Config >1% | Check settings | Reset to defaults |
| Asset >0.5% | Check network | Retry asset loading |

### Playbook: Parse Error Surge

**Symptoms**:
- `loadGitLog()` returning errors
- High parse error count in metrics
- Truncated or garbled commit data

**Diagnosis**:
```javascript
// Check parse error rate specifically
console.log('Parse error rate:', rource.getParseErrorRate().toFixed(4) + '%');
console.log('Parse errors:', rource.getParseErrorCount());

// Get detailed breakdown
const metrics = JSON.parse(rource.getDetailedErrorMetrics());
console.log('Parse ops:', metrics.operations.parse);
```

**Resolution**:
1. Verify git log format:
   ```bash
   git log --pretty=format:'%at|%an|%s' --stat --no-merges
   ```
2. Check for encoding issues (UTF-8 BOM, non-UTF-8 characters)
3. Enable lenient parsing (default)
4. If persists, file bug with sample input (redacted)

### Playbook: WebGL Context Lost

**Symptoms**:
- Black screen after running for a while
- WebGL error count increasing
- "Context lost" errors in console

**Diagnosis**:
```javascript
console.log('WebGL errors:', rource.getWebGlErrorCount());
console.log('Renderer type:', rource.getRendererType());
```

**Resolution**:
1. Automatic fallback to software renderer should occur
2. Refresh page to reset WebGL context
3. Check system memory pressure
4. Try reducing entity count or disabling bloom

---

## Monitoring and Alerting

### Key Metrics to Monitor

| Metric | Target | Alert Threshold |
|--------|--------|-----------------|
| Frame time (P50) | <16.67ms | >20ms |
| Memory growth | <5%/30min | >10%/30min |
| Crash count | 0 | >0 |
| CI pass rate | 100% | <95% |
| **Error rate** | **<0.1%** | **>0.05%** |
| **Parse error rate** | **<0.5%** | **>0.1%** |

### Alerting Setup

**GitHub Actions**:
- Benchmark regression: Automatic comment
- Fuzzing crash: Issue created
- CI failure: Email notification

**Browser Console**:
```javascript
// Add performance warnings
if (rource.getLastFrameTime() > 20) {
    console.warn('Frame time exceeds target:', rource.getLastFrameTime());
}

// Add error rate warnings
if (rource.errorRateExceedsThreshold(0.05)) {
    console.warn('Error rate warning:', rource.getErrorRate().toFixed(4) + '%');
}
if (rource.errorRateExceedsThreshold(0.1)) {
    console.error('Error budget exhausted:', rource.getErrorRate().toFixed(4) + '%');
}
```

### Error Budget Monitoring

Monitor error rates to ensure SLO compliance:

```javascript
// Periodic error budget check
function checkErrorBudget() {
    const metrics = JSON.parse(rource.getErrorMetrics());

    // Log current state
    console.log(`Error budget: ${(0.1 - metrics.rate * 100).toFixed(4)}% remaining`);

    // Alert if approaching threshold
    if (metrics.rate > 0.0005) { // >0.05%
        console.warn('Error rate warning - approaching budget limit');
    }

    if (metrics.rate > 0.001) { // >0.1%
        console.error('Error budget EXHAUSTED');
        // Trigger mitigation
    }
}

// Run every 60 seconds
setInterval(checkErrorBudget, 60000);
```

See [ERROR_BUDGET.md](./ERROR_BUDGET.md) for detailed error budget policy.

---

## Escalation Contacts

| Issue Type | Primary Contact | Backup |
|------------|-----------------|--------|
| Performance | Performance team | Core maintainers |
| Security | security@example.com | Maintainers |
| General bugs | GitHub Issues | - |

---

## Revision History

| Date | Version | Changes |
|------|---------|---------|
| 2026-01-26 | 1.0 | Initial runbook |

---

*Last updated: 2026-01-26*
*Task: DOC-3 Runbook/Playbook Documentation*
