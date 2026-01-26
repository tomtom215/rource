# Architecture Decision Records

This directory contains Architecture Decision Records (ADRs) for the Rource project.

## What is an ADR?

An Architecture Decision Record captures an important architectural decision made along with its context and consequences. ADRs help:

- Document why decisions were made
- Provide context for future maintainers
- Enable informed revisiting of decisions
- Track the evolution of architecture

## ADR Index

| ID | Title | Status | Date |
|----|-------|--------|------|
| [0001](0001-use-barnes-hut-for-force-layout.md) | Use Barnes-Hut Algorithm for Force-Directed Layout | Accepted | 2024-01 |
| [0002](0002-software-renderer-as-primary-backend.md) | Software Renderer as Primary Backend | Accepted | 2024-01 |
| [0003](0003-wasm-first-architecture.md) | WASM-First Architecture | Accepted | 2024-01 |
| [0004](0004-generation-counter-for-spatial-reset.md) | Generation Counter Pattern for Spatial Grid Reset | Accepted | 2025-01 |
| [0005](0005-texture-array-batching.md) | Texture Array Batching for Draw Calls | Accepted | 2025-01 |

## ADR Statuses

- **Proposed**: Under discussion
- **Accepted**: Decision made, implementation in progress or complete
- **Deprecated**: Superseded by another decision
- **Rejected**: Considered but not adopted

## Creating a New ADR

1. Copy `template.md` to `XXXX-title-with-dashes.md`
2. Fill in all sections
3. Add to the index above
4. Submit PR for review

## Template

See [template.md](template.md) for the ADR template.

---

*Last updated: 2026-01-26*
