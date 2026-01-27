# Formal Algorithmic Proofs

This directory contains formal mathematical proofs for the key algorithms used in Rource. Each proof establishes correctness, complexity bounds, and error bounds where applicable.

**PRECISION REQUIREMENT**: Picosecond to nanosecond level. Test hardware theoretical max: 50,000 FPS.

**EXPERT+ STANDARD**: Mathematical rigor, complete proofs, actionable implementation guidance. Zero compromises.

---

## Table of Contents

| # | Proof | Implementation | Category |
|---|-------|----------------|----------|
| 1 | [Barnes-Hut Algorithm](./01-barnes-hut-algorithm.md) | `crates/rource-core/src/physics/barnes_hut.rs` | Physics Simulation |
| 2 | [QuadTree Spatial Index](./02-quadtree-spatial-index.md) | `crates/rource-core/src/physics/spatial.rs` | Spatial Data Structures |
| 3 | [Incremental Spatial Index Maintenance](./03-incremental-spatial-index.md) | `crates/rource-core/src/scene/spatial_methods.rs` | Spatial Data Structures |
| 4 | [Force-Directed Layout Convergence](./04-force-directed-layout.md) | `crates/rource-core/src/physics/force.rs` | Physics Simulation |
| 5 | [Alpha Blending Correctness](./05-alpha-blending.md) | `crates/rource-render/src/backend/software/optimized.rs` | Rendering |
| 6 | [Color Conversion Accuracy](./06-color-conversion.md) | `crates/rource-math/src/color.rs` | Mathematics |
| 7 | [Label Collision Detection (Spatial Hash Grid)](./07-label-collision-detection.md) | `rource-wasm/src/render_phases.rs`, `crates/rource-render/src/label.rs` | Rendering |
| 8 | [Generation Counter Pattern](./08-generation-counter.md) | `rource-wasm/src/render_phases.rs` (LabelPlacer) | Data Structures |
| 9 | [Partial Selection Algorithm](./09-partial-selection.md) | `rource-wasm/src/render_phases.rs` | Algorithms |
| 10 | [Texture Array Batching](./10-texture-array-batching.md) | `crates/rource-render/src/backend/wgpu/textures.rs` | GPU Optimization |
| 11 | [Adaptive Barnes-Hut Theta](./11-adaptive-barnes-hut-theta.md) | `crates/rource-core/src/physics/barnes_hut.rs` | Physics Simulation |
| 12 | [Bloom Effect Sliding Window](./12-bloom-effect-sliding-window.md) | `crates/rource-render/src/effects/bloom.rs` | Rendering Effects |
| 13 | [Floyd's Cycle Detection Algorithm](./13-floyds-cycle-detection.md) | `crates/rource-core/src/scene/tree.rs`, `tests/chaos/wasm/mod.rs` | Data Integrity |

---

## Quick Reference

### Complexity Summary

| Algorithm | Time Complexity | Space Complexity | Key Result |
|-----------|-----------------|------------------|------------|
| Barnes-Hut | O(n log n) | O(n) | ~90% speedup vs O(n²) |
| QuadTree Query | O(log n + k) | O(n) | Optimal range query |
| Incremental Index | O(k log n) | O(n) | 100x vs full rebuild |
| Force Layout | Converges in O(log(1/ε)) frames | O(n) | Guaranteed stability |
| Alpha Blending | O(1) per pixel | O(1) | Max error ±1 |
| Color LUT | O(1) | O(256) | Exact round-trip |
| Label Collision | O(1) expected | O(G + n) | Collision-free |
| Generation Counter | O(1) amortized clear | O(G) | 90x faster reset |
| Partial Selection | O(n) | O(1) | 8.6x vs full sort |
| Texture Array | O(1) draw calls | O(n) | 56% faster |
| Adaptive Theta | O(n log n) | O(n) | Auto-tuned accuracy |
| Bloom Sliding | O(n) | O(n) | 41x vs direct |
| Floyd's Cycle | O(μ + λ) | O(1) | Zero overhead |

---

## Appendices

- [Appendix A: Notation](./appendices.md#appendix-a-notation)
- [Appendix B: References](./appendices.md#appendix-b-references)

---

## Document Information

| Field | Value |
|-------|-------|
| Version | 3.0 |
| Last Updated | 2026-01-27 |
| Validated Against | rource-core v0.1.0, Phases 61-74 |
| Total Proofs | 13 |

---

*Each proof follows the Expert+ standard: mathematical rigor, complete derivations, empirical validation, and actionable implementation guidance.*
