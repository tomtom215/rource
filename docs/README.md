# Rource Documentation

Complete technical documentation for the Rource project.

---

## Quick Links

| Document | Purpose |
|----------|---------|
| [../README.md](../README.md) | Project overview and usage |
| [../CLAUDE.md](../CLAUDE.md) | Development guidelines (Expert+ standards) |
| [../CONTRIBUTING.md](../CONTRIBUTING.md) | Contribution guide |
| [../STABILITY.md](../STABILITY.md) | API stability policy |
| [../SECURITY.md](../SECURITY.md) | Security policy |
| [performance/FUTURE_WORK.md](./performance/FUTURE_WORK.md) | Expert+ roadmap |

---

## Master Documentation Index

### Root Documents (6 files)

| Document | Description | Status |
|----------|-------------|--------|
| [README.md](../README.md) | Project overview, installation, usage | Current |
| [CLAUDE.md](../CLAUDE.md) | Development guidelines and Expert+ standards | Current |
| [CONTRIBUTING.md](../CONTRIBUTING.md) | Contribution guidelines and setup | Current |
| [STABILITY.md](../STABILITY.md) | API versioning and stability policy | Current |
| [SECURITY.md](../SECURITY.md) | Security policy and vulnerability reporting | Current |
| [CHANGELOG.md](../CHANGELOG.md) | Release history and optimization phases | Current |

---

### Architecture & Design (8 files)

| Document | Description |
|----------|-------------|
| [ARCHITECTURE.md](./ARCHITECTURE.md) | System architecture and crate structure |
| [RENDERING.md](./RENDERING.md) | Rendering backends and pipeline details |
| [GOURCE_COMPARISON.md](./GOURCE_COMPARISON.md) | Feature parity with original Gource |
| [TROUBLESHOOTING.md](./TROUBLESHOOTING.md) | Common issues and solutions |
| [REVIEW_STANDARDS.md](./REVIEW_STANDARDS.md) | Code review requirements |
| [RFC_UNLIMITED_REPO_VISUALIZATION.md](./RFC_UNLIMITED_REPO_VISUALIZATION.md) | RFC for unlimited repo viz |
| [RENDERING_BOTTLENECK_ANALYSIS.md](./RENDERING_BOTTLENECK_ANALYSIS.md) | Performance bottleneck analysis |

---

### Performance Documentation (20 files)

| Document | Description |
|----------|-------------|
| [performance/README.md](./performance/README.md) | Performance documentation index |
| [performance/OVERVIEW.md](./performance/OVERVIEW.md) | Executive summary and philosophy |
| [performance/CHRONOLOGY.md](./performance/CHRONOLOGY.md) | Timeline of all **83 optimization phases** |
| [performance/BENCHMARKS.md](./performance/BENCHMARKS.md) | Benchmark data with methodology |
| [performance/SUCCESSFUL_OPTIMIZATIONS.md](./performance/SUCCESSFUL_OPTIMIZATIONS.md) | Implemented optimizations |
| [performance/FUTURE_WORK.md](./performance/FUTURE_WORK.md) | **Expert+ roadmap** (active) |
| [performance/THEORETICAL_ALGORITHMS.md](./performance/THEORETICAL_ALGORITHMS.md) | Advanced algorithmic research |
| [performance/ALGORITHMIC_COMPLEXITY.md](./performance/ALGORITHMIC_COMPLEXITY.md) | Big-O analysis of all functions |
| [performance/FORMAL_PROOFS.md](./performance/FORMAL_PROOFS.md) | Mathematical proofs for core algorithms |
| [performance/COMPLEXITY_VERIFICATION.md](./performance/COMPLEXITY_VERIFICATION.md) | Empirical Big-O verification |
| [performance/FUNCTION_PROFILES.md](./performance/FUNCTION_PROFILES.md) | Per-function timing profiles |
| [performance/PERFORMANCE_BASELINE.md](./performance/PERFORMANCE_BASELINE.md) | WASM performance audit |
| [performance/PROFILING.md](./performance/PROFILING.md) | Profiling tools and techniques |
| [performance/GUIDE.md](./performance/GUIDE.md) | General performance tips |
| [performance/METHODOLOGY.md](./performance/METHODOLOGY.md) | Benchmark methodology |
| [performance/MEMORY_BUDGET.md](./performance/MEMORY_BUDGET.md) | Memory constraints |
| [performance/SLO.md](./performance/SLO.md) | Service level objectives |
| [performance/NOT_APPLICABLE.md](./performance/NOT_APPLICABLE.md) | Analyzed but not applicable |
| [performance/UNSUCCESSFUL.md](./performance/UNSUCCESSFUL.md) | Tested but performed worse |
| [performance/SHADERS.md](./performance/SHADERS.md) | GPU shader optimization |

---

### Operations Documentation (6 files)

| Document | Description |
|----------|-------------|
| [operations/README.md](./operations/README.md) | Operations documentation index |
| [operations/TELEMETRY.md](./operations/TELEMETRY.md) | Telemetry infrastructure |
| [operations/SLO.md](./operations/SLO.md) | Service level objectives |
| [operations/ERROR_BUDGET.md](./operations/ERROR_BUDGET.md) | Error budgeting policy |
| [operations/LOAD_TESTING.md](./operations/LOAD_TESTING.md) | Load testing documentation |
| [operations/RUNBOOK.md](./operations/RUNBOOK.md) | Operational runbooks |

---

### Testing Documentation (2 files)

| Document | Description |
|----------|-------------|
| [testing/MUTATION_TESTING.md](./testing/MUTATION_TESTING.md) | Mutation testing setup and results |
| [testing/VISUAL_REGRESSION.md](./testing/VISUAL_REGRESSION.md) | Visual regression testing infrastructure |

---

### Verification Documentation (7 files)

| Document | Description |
|----------|-------------|
| [verification/FORMAL_VERIFICATION.md](./verification/FORMAL_VERIFICATION.md) | Formal verification overview and index (2221 theorems/harnesses, 8 types) |
| [verification/VERUS_PROOFS.md](./verification/VERUS_PROOFS.md) | Verus theorem tables (475 proof functions, 7 types) |
| [verification/COQ_PROOFS.md](./verification/COQ_PROOFS.md) | Coq proofs (R-based + Z-based, 1393 theorems, development workflow) |
| [verification/VERIFICATION_COVERAGE.md](./verification/VERIFICATION_COVERAGE.md) | Coverage metrics, limitations, floating-point assessment |
| [verification/WASM_EXTRACTION_PIPELINE.md](./verification/WASM_EXTRACTION_PIPELINE.md) | Coq-to-WASM pipeline, tool ecosystem, Rocq migration |
| [verification/SETUP_GUIDE.md](./verification/SETUP_GUIDE.md) | Verus, Coq, MetaCoq, wasm_of_ocaml setup |
| [verification/CERTICOQ_WASM_ASSESSMENT.md](./verification/CERTICOQ_WASM_ASSESSMENT.md) | Coq-to-WASM pipeline (9 paths surveyed) |

---

### Security Documentation (3 files)

| Document | Description |
|----------|-------------|
| [../SECURITY.md](../SECURITY.md) | Security policy (root) |
| [security/FUZZING.md](./security/FUZZING.md) | Fuzzing coverage documentation |
| [security/SUPPLY_CHAIN.md](./security/SUPPLY_CHAIN.md) | Supply chain security (SLSA) |

---

### UX & Accessibility (2 files)

| Document | Description |
|----------|-------------|
| [ux/MOBILE_UX_ROADMAP.md](./ux/MOBILE_UX_ROADMAP.md) | Mobile UX roadmap (46 issues) |
| [accessibility/WCAG_COMPLIANCE.md](./accessibility/WCAG_COMPLIANCE.md) | WCAG 2.1 AA compliance |

---

### Architecture Decision Records (6 files)

| ADR | Decision |
|-----|----------|
| [adr/README.md](./adr/README.md) | ADR index and template |
| [adr/0001-use-barnes-hut-for-force-layout.md](./adr/0001-use-barnes-hut-for-force-layout.md) | Barnes-Hut algorithm for force layout |
| [adr/0002-software-renderer-as-primary-backend.md](./adr/0002-software-renderer-as-primary-backend.md) | Software renderer as primary |
| [adr/0003-wasm-first-architecture.md](./adr/0003-wasm-first-architecture.md) | WASM-first architecture |
| [adr/0004-generation-counter-for-spatial-reset.md](./adr/0004-generation-counter-for-spatial-reset.md) | Generation counter optimization |
| [adr/0005-texture-array-batching.md](./adr/0005-texture-array-batching.md) | Texture array batching |

---

### CI/CD Documentation (2 files)

| Document | Description |
|----------|-------------|
| [ci/BENCHMARK_GATES.md](./ci/BENCHMARK_GATES.md) | Performance regression gates |
| [ci/BENCHMARK_DASHBOARD.md](./ci/BENCHMARK_DASHBOARD.md) | Benchmark dashboard setup |

---

## Documentation by Topic

### Getting Started
1. [../README.md](../README.md) - Installation and basic usage
2. [ARCHITECTURE.md](./ARCHITECTURE.md) - Understand the codebase structure
3. [../CONTRIBUTING.md](../CONTRIBUTING.md) - Set up development environment

### Understanding the Code
1. [ARCHITECTURE.md](./ARCHITECTURE.md) - Crate structure and data flow
2. [RENDERING.md](./RENDERING.md) - How rendering works
3. [performance/ALGORITHMIC_COMPLEXITY.md](./performance/ALGORITHMIC_COMPLEXITY.md) - Performance characteristics

### Optimizing Performance
1. [performance/GUIDE.md](./performance/GUIDE.md) - General performance tips
2. [performance/PROFILING.md](./performance/PROFILING.md) - Finding bottlenecks
3. [performance/BENCHMARKS.md](./performance/BENCHMARKS.md) - Benchmark methodology
4. [performance/CHRONOLOGY.md](./performance/CHRONOLOGY.md) - 83 optimization phases

### Expert+ Development
1. [../CLAUDE.md](../CLAUDE.md) - Development standards
2. [performance/FUTURE_WORK.md](./performance/FUTURE_WORK.md) - Expert+ roadmap
3. [ux/MOBILE_UX_ROADMAP.md](./ux/MOBILE_UX_ROADMAP.md) - Mobile UX roadmap

### Operations & Monitoring
1. [operations/TELEMETRY.md](./operations/TELEMETRY.md) - Telemetry setup
2. [operations/SLO.md](./operations/SLO.md) - Service level objectives
3. [operations/RUNBOOK.md](./operations/RUNBOOK.md) - Operational playbooks

### Testing & Quality
1. [testing/MUTATION_TESTING.md](./testing/MUTATION_TESTING.md) - Mutation testing
2. [testing/VISUAL_REGRESSION.md](./testing/VISUAL_REGRESSION.md) - Visual regression
3. [REVIEW_STANDARDS.md](./REVIEW_STANDARDS.md) - Code review requirements

---

## Document Statistics

| Metric | Value |
|--------|-------|
| Total documentation files | **64** |
| Performance documents | 20 |
| Operations documents | 6 |
| Architecture/Design documents | 8 |
| ADR documents | 6 |
| Verification documents | 3 |
| Security documents | 3 |
| Testing documents | 2 |
| UX/Accessibility documents | 2 |
| CI/CD documents | 2 |
| Root documents | 6 |
| Other (examples, benchmarks) | 6 |

### Size Distribution

| Category | Files | Approximate Size |
|----------|-------|------------------|
| Performance | 19 | ~450 KB |
| Root/Core | 14 | ~160 KB |
| Verification | 3 | ~80 KB |
| Operations | 6 | ~45 KB |
| ADRs | 6 | ~25 KB |
| Security | 3 | ~30 KB |
| Testing | 2 | ~20 KB |
| UX | 2 | ~40 KB |
| **Total** | **65** | **~880 KB** |

---

## Maintenance

### Updating Documentation

When making changes that affect documentation:

1. Update the relevant document(s)
2. Update any cross-references
3. Update the "Last updated" date at bottom of each file
4. Verify links with: `grep -r "](./.*\.md)" docs/`
5. Update this index if adding new documents

### Documentation Standards

- Use consistent Markdown formatting
- Include tables of contents for long documents (>200 lines)
- Provide code examples where applicable
- Keep tables aligned for readability
- Date all documents with "Last updated: YYYY-MM-DD"
- Follow Expert+ standards from [CLAUDE.md](../CLAUDE.md)

### Link Verification

```bash
# Find all internal markdown links
grep -r "](\./" docs/ | grep "\.md"

# Check for broken links
for f in $(find docs -name "*.md"); do
  grep -oP '(?<=]\()[^)]+\.md(?=\))' "$f" | while read link; do
    dir=$(dirname "$f")
    if [ ! -f "$dir/$link" ]; then
      echo "BROKEN: $f -> $link"
    fi
  done
done
```

---

*Last updated: 2026-01-29*
