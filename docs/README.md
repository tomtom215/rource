# Rource Documentation

Complete technical documentation for the Rource project.

---

## Quick Links

| Document | Purpose |
|----------|---------|
| [../README.md](../README.md) | Project overview and usage |
| [../CLAUDE.md](../CLAUDE.md) | Development guidelines |
| [../CONTRIBUTING.md](../CONTRIBUTING.md) | Contribution guide |
| [../PERFORMANCE.md](../PERFORMANCE.md) | Performance summary |

---

## Documentation Index

### Architecture & Design

| Document | Description |
|----------|-------------|
| [ARCHITECTURE.md](./ARCHITECTURE.md) | System architecture and crate structure |
| [RENDERING.md](./RENDERING.md) | Rendering backends and pipeline details |

### Performance

| Document | Description |
|----------|-------------|
| [performance/README.md](./performance/README.md) | Performance documentation index |
| [performance/OVERVIEW.md](./performance/OVERVIEW.md) | Executive summary and philosophy |
| [performance/CHRONOLOGY.md](./performance/CHRONOLOGY.md) | Timeline of all 58 optimization phases |
| [performance/BENCHMARKS.md](./performance/BENCHMARKS.md) | All benchmark data with methodology |
| [performance/SUCCESSFUL_OPTIMIZATIONS.md](./performance/SUCCESSFUL_OPTIMIZATIONS.md) | Implemented optimizations |
| [performance/NOT_APPLICABLE.md](./performance/NOT_APPLICABLE.md) | Analyzed but not applicable |
| [performance/UNSUCCESSFUL.md](./performance/UNSUCCESSFUL.md) | Tested but performed worse |
| [performance/GUIDE.md](./performance/GUIDE.md) | General performance guide |

### Reference

| Document | Description |
|----------|-------------|
| [ALGORITHMIC_COMPLEXITY.md](./ALGORITHMIC_COMPLEXITY.md) | Big-O analysis of all functions |
| [PROFILING.md](./PROFILING.md) | Profiling tools and techniques |
| [THEORETICAL_ALGORITHMS.md](./THEORETICAL_ALGORITHMS.md) | Advanced algorithmic research |

### Archives

Historical documents preserved for reference:

| Document | Description |
|----------|-------------|
| [performance/archives/AUDIT_2026-01-23.md](./performance/archives/AUDIT_2026-01-23.md) | Closed performance audit |
| [performance/archives/FPS_2026-01-21.md](./performance/archives/FPS_2026-01-21.md) | Early FPS optimization report |

---

## Documentation by Topic

### Getting Started
1. [../README.md](../README.md) - Installation and basic usage
2. [ARCHITECTURE.md](./ARCHITECTURE.md) - Understand the codebase structure
3. [../CONTRIBUTING.md](../CONTRIBUTING.md) - Set up development environment

### Understanding the Code
1. [ARCHITECTURE.md](./ARCHITECTURE.md) - Crate structure and data flow
2. [RENDERING.md](./RENDERING.md) - How rendering works
3. [ALGORITHMIC_COMPLEXITY.md](./ALGORITHMIC_COMPLEXITY.md) - Performance characteristics

### Optimizing Performance
1. [performance/GUIDE.md](./performance/GUIDE.md) - General performance tips
2. [PROFILING.md](./PROFILING.md) - Finding bottlenecks
3. [performance/BENCHMARKS.md](./performance/BENCHMARKS.md) - Benchmark methodology

### Advanced Topics
1. [THEORETICAL_ALGORITHMS.md](./THEORETICAL_ALGORITHMS.md) - Cutting-edge algorithms
2. [performance/CHRONOLOGY.md](./performance/CHRONOLOGY.md) - Optimization history
3. [../CLAUDE.md](../CLAUDE.md) - Development standards

---

## Document Statistics

| Metric | Value |
|--------|-------|
| Total documentation files | 15 |
| Performance documents | 9 |
| Architecture documents | 2 |
| Reference documents | 3 |
| Archived documents | 2 |

---

## Maintenance

### Updating Documentation

When making changes that affect documentation:

1. Update the relevant document(s)
2. Update any cross-references
3. Update the "Last updated" date
4. Verify links with `grep -r "](./.*\.md)" docs/`

### Documentation Standards

- Use consistent Markdown formatting
- Include tables of contents for long documents
- Provide code examples where applicable
- Keep tables aligned for readability
- Date all documents with "Last updated"

---

*Last updated: 2026-01-25*
