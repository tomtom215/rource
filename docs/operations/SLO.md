# Service Level Objectives (SLOs)

This document defines the formal Service Level Indicators (SLIs) and Service Level Objectives (SLOs) for Rource. These targets apply to both the native CLI and the WASM demo deployment.

---

## Table of Contents

1. [Overview](#1-overview)
2. [Performance SLOs](#2-performance-slos)
3. [Reliability SLOs](#3-reliability-slos)
4. [Build Quality SLOs](#4-build-quality-slos)
5. [User Experience SLOs](#5-user-experience-slos)
6. [Monitoring](#6-monitoring)
7. [Error Budget](#7-error-budget)

---

## 1. Overview

### 1.1 Purpose

SLOs ensure consistent quality for:
- Portfolio demonstration reliability
- Public WASM demo availability
- Development velocity protection
- Performance regression prevention

### 1.2 Scope

| Target | Platform | Applies To |
|--------|----------|------------|
| Native CLI | Linux, macOS, Windows | Release builds |
| WASM Demo | Modern browsers | Production deployment |
| CI Pipeline | GitHub Actions | All PRs and main |

---

## 2. Performance SLOs

### 2.1 Frame Time

| SLI | Target | Measurement |
|-----|--------|-------------|
| Frame time (software renderer) | <200ms p95 | Render phase timing |
| Frame time (WebGL2) | <20ms p95 | `requestAnimationFrame` delta |
| Frame time (wgpu) | <16.6ms p95 | GPU fence timing |

**Rationale**: Software renderer is CPU-bound and intended for offline export. GPU renderers target 60 FPS for interactive use.

### 2.2 Startup Time

| SLI | Target | Measurement |
|-----|--------|-------------|
| WASM initial load | <3s p95 | First meaningful paint |
| Native startup | <1s p95 | Time to first frame |
| Repository parse (10K commits) | <2s p95 | Parse completion |

**Measurement Method**: Lighthouse for WASM, `--timing` flag for native.

### 2.3 Memory Usage

| SLI | Target | Measurement |
|-----|--------|-------------|
| WASM heap usage | <512MB | `WebAssembly.Memory` pages |
| Native RSS | <1GB | `ps` or task manager |
| Per-entity memory | <1KB | Total / entity count |

**Enforcement**: Chaos tests verify memory bounds.

### 2.4 Throughput

| SLI | Target | Measurement |
|-----|--------|-------------|
| Entity update rate | >50K entities/frame | Scene::update() throughput |
| VCS parse rate | >100K lines/s | Benchmark suite |
| Pixel fill rate (software) | >10M pixels/s | Render benchmark |

---

## 3. Reliability SLOs

### 3.1 Crash Rate

| SLI | Target | Measurement |
|-----|--------|-------------|
| WASM trap rate | 0% | Exception monitoring |
| Native panic rate | 0% | Exit code monitoring |
| CI failure rate (non-flaky) | <1% | Workflow analytics |

**Enforcement**: Chaos tests with 185+ edge cases, panic = abort in release.

### 3.2 Demo Availability

| SLI | Target | Measurement |
|-----|--------|-------------|
| Demo site uptime | 99.9% | UptimeRobot/Pingdom |
| GitHub Pages latency | <500ms p95 | CDN edge response |
| Asset loading success | 99.9% | Browser error tracking |

**Error Budget**: 43.2 minutes/month downtime allowed.

### 3.3 Regression Prevention

| SLI | Target | Measurement |
|-----|--------|-------------|
| Benchmark regression detection | 100% for >10% | CI benchmark workflow |
| Test coverage | >80% | Codecov |
| All tests passing | 100% | CI gate |

---

## 4. Build Quality SLOs

### 4.1 Binary Size

| Artifact | Target | Warning | Error |
|----------|--------|---------|-------|
| Native binary | <5MB | >5MB | >6MB |
| WASM (gzipped) | <300KB | >300KB | >400KB |
| JS bindings | <50KB | >50KB | >100KB |

**Current Status**:
- Native: ~3.8MB (OK)
- WASM gzipped: ~250KB (OK)

### 4.2 Build Time

| SLI | Target | Measurement |
|-----|--------|-------------|
| Full debug build | <2min | `cargo build` |
| Incremental build | <30s | `cargo build` (after change) |
| Full release build | <5min | `cargo build --release` |
| WASM build | <3min | `wasm-pack build` |
| Full CI pipeline | <15min | Workflow duration |

### 4.3 Code Quality

| SLI | Target | Enforcement |
|-----|--------|-------------|
| Clippy warnings | 0 | `-D warnings` |
| Rustfmt compliance | 100% | `cargo fmt --check` |
| Unsafe code | 0 blocks | `#![deny(unsafe_code)]` |
| Doc coverage | >90% public items | `cargo doc` warnings |

---

## 5. User Experience SLOs

### 5.1 Input Responsiveness

| SLI | Target | Measurement |
|-----|--------|-------------|
| Mouse event latency | <50ms | Event to visual update |
| Keyboard shortcut response | <100ms | Key to action |
| Slider drag latency | <16ms | Touch to update |

### 5.2 Visual Quality

| SLI | Target | Measurement |
|-----|--------|-------------|
| Frame drops (60 FPS target) | <5% | DevTools performance |
| Visual glitches | 0 | Manual QA |
| Text readability | Clear at all zoom levels | Manual QA |

### 5.3 Error Handling

| SLI | Target | Measurement |
|-----|--------|-------------|
| User-visible errors | Graceful with message | Chaos test coverage |
| Recovery from errors | Automatic where possible | Test verification |
| Error message clarity | Actionable advice | UX review |

---

## 6. Monitoring

### 6.1 Automated Checks

| Check | Frequency | Tool |
|-------|-----------|------|
| Benchmark regression | Every PR | `bench.yml` workflow |
| Binary size | Every PR | `bench.yml` size-check job |
| Test suite | Every PR | `ci.yml` workflow |
| Security audit | Weekly | `security.yml` workflow |
| Demo uptime | Every minute | UptimeRobot |

### 6.2 Manual Checks

| Check | Frequency | Owner |
|-------|-----------|-------|
| Visual QA on demo | Every release | Maintainer |
| Browser compatibility | Every release | Maintainer |
| Performance profiling | Monthly | Maintainer |

### 6.3 Alerting

| Condition | Alert Method | Response Time |
|-----------|-------------|---------------|
| Demo site down | Email/Slack | <1 hour |
| >10% benchmark regression | PR comment | Before merge |
| Security vulnerability | GitHub advisory | <24 hours |
| Build failure on main | Email | <4 hours |

---

## 7. Error Budget

### 7.1 Calculation

For 99.9% availability over 30 days:
```
Total minutes: 30 × 24 × 60 = 43,200 minutes
Error budget: 0.1% × 43,200 = 43.2 minutes
```

### 7.2 Budget Consumption

Track error budget consumption monthly:

| Event | Duration | Budget Used |
|-------|----------|-------------|
| Planned maintenance | N/A | Excluded |
| Infrastructure issue | 5 min | 5 min |
| Bug causing crash | 10 min | 10 min |

**Remaining**: 43.2 - 15 = 28.2 minutes

### 7.3 Budget Exhaustion Policy

If error budget exhausted:

1. **Freeze new features** - Focus on reliability
2. **Root cause analysis** - Document all incidents
3. **Implement fixes** - Add monitoring, tests
4. **Post-mortem review** - Learn from failures

---

## Appendix A: SLI Definitions

| Term | Definition |
|------|------------|
| **SLI** | Service Level Indicator - a measurable metric |
| **SLO** | Service Level Objective - target for an SLI |
| **Error Budget** | Allowed failure rate (100% - SLO) |
| **p95** | 95th percentile (95% of measurements below) |
| **p99** | 99th percentile |

## Appendix B: Measurement Tools

| Metric | Native Tool | WASM Tool |
|--------|-------------|-----------|
| Frame time | `--timing` flag | Performance API |
| Memory | `ps`/`top` | `performance.memory` |
| Startup | `time` command | Lighthouse |
| Throughput | Criterion benchmark | Custom profiler |

## Appendix C: Historical Performance

| Date | WASM Size | Native Size | Test Count |
|------|-----------|-------------|------------|
| 2026-01 | 250KB | 3.8MB | 1,899 |

---

*Document Version: 1.0*
*Last Updated: 2026-01-26*
*Review Frequency: Quarterly*
