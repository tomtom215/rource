# Algorithm Documentation

This directory contains formal mathematical documentation and proofs for the algorithms used in Rource.

## Documents

| Document | Description |
|----------|-------------|
| [FORMAL_PROOFS.md](./FORMAL_PROOFS.md) | Mathematical proofs for all core algorithms |

## Algorithm Overview

### Spatial Data Structures

| Algorithm | Complexity | Location |
|-----------|-----------|----------|
| QuadTree | O(log n) query/insert | `rource-core/src/physics/spatial.rs` |
| Barnes-Hut | O(n log n) force calc | `rource-core/src/physics/barnes_hut.rs` |
| GPU Spatial Hash | O(n) with GPU | `rource-render/src/backend/wgpu/spatial_hash.rs` |

### Physics Simulation

| Algorithm | Complexity | Location |
|-----------|-----------|----------|
| Force-Directed Layout | O(n log n) | `rource-core/src/physics/force.rs` |
| Semi-Implicit Euler | O(n) | `rource-core/src/physics/force.rs` |

### Rendering

| Algorithm | Complexity | Location |
|-----------|-----------|----------|
| Software Rasterization | O(pixels) | `rource-render/src/backend/software/` |
| Fixed-Point Blending | O(1) per pixel | `rource-render/src/backend/software/optimized.rs` |
| Kawase Blur (Bloom) | O(pixels × passes) | `rource-render/src/backend/wgpu/bloom.rs` |

## Complexity Summary

From [ALGORITHMIC_COMPLEXITY.md](../performance/ALGORITHMIC_COMPLEXITY.md):

- **87%** of functions are O(1)
- **4%** are O(log n)
- **6%** are O(n)
- **2%** are O(n log n)
- **<1%** are O(n²) (fallback paths only)

## Adding New Proofs

When adding a new algorithm:

1. Document the algorithm in code with complexity annotations
2. Add formal proof to `FORMAL_PROOFS.md` if non-trivial
3. Include empirical validation with benchmarks
4. Update complexity summary in `ALGORITHMIC_COMPLEXITY.md`

---

*Last Updated: 2026-01-26*
