# Operations Documentation

This directory contains operational documentation for running and maintaining Rource.

## Documents

| Document | Description |
|----------|-------------|
| [ERROR_BUDGET.md](./ERROR_BUDGET.md) | Error budget policy and burn rate monitoring |
| [LOAD_TESTING.md](./LOAD_TESTING.md) | Load testing infrastructure and methodology |
| [RUNBOOK.md](./RUNBOOK.md) | Operational runbook for incident response |
| [SLO.md](./SLO.md) | Service Level Objectives and Indicators |
| [TELEMETRY.md](./TELEMETRY.md) | Telemetry and observability configuration |

## Quick Reference

### Key Metrics

| Metric | Target | Current |
|--------|--------|---------|
| Demo uptime | 99.9% | Monitored |
| WASM size (gzip) | <300KB | ~250KB |
| Native size | <5MB | ~3.8MB |
| Test count | - | 2,900+ |

### Monitoring

- **CI**: GitHub Actions workflows
- **Benchmarks**: `bench.yml` with regression detection
- **Size tracking**: `bench.yml` size-check job

### Incident Response

1. Check CI status at GitHub Actions
2. Review recent commits
3. Run local tests: `cargo test`
4. Check demo at deployment URL

---

*Last Updated: 2026-01-26*
