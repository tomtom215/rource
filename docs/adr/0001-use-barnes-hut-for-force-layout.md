# ADR 0001: Use Barnes-Hut Algorithm for Force-Directed Layout

## Status

Accepted

## Date

2024-01-15

## Context

The Rource visualization uses force-directed layout to arrange files and directories in a radial tree structure. Force calculations between entities create repulsion to prevent overlap and attraction to maintain hierarchical structure.

**Problem**: Traditional force-directed layout requires O(n²) pairwise force calculations. For repositories with 10,000+ entities, this becomes the primary performance bottleneck:

- 10,000 entities = 100,000,000 force calculations per frame
- At 60 FPS, this requires ~6 billion calculations per second
- CPU bound, cannot leverage GPU efficiently

**Constraints**:
- Must maintain visual quality (layout shouldn't degrade noticeably)
- Must scale to 100,000+ entities
- Must work in WASM environment
- Should support both CPU and GPU physics paths

## Decision

Implement the Barnes-Hut algorithm with adaptive theta parameter for force calculations.

**Barnes-Hut Algorithm**:
1. Build octree (quadtree in 2D) containing all entities
2. For each entity, traverse tree from root
3. If node is sufficiently far away (distance/size > θ), treat as single mass
4. Otherwise, recurse into children

**Adaptive Theta**:
```
θ(n) = 0.8 + 0.7 × clamp(log₂(n/200) / log₂(25), 0, 1)
Clamped to [0.7, 1.5]
```

This automatically increases approximation for larger entity counts while maintaining accuracy for smaller scenes.

## Consequences

### Positive

- **O(n log n) complexity**: Enables 100k+ entity visualization
- **Verified scaling**: 5000 entities runs in 1.64ms (vs 4.25ms with fixed θ)
- **Adaptive accuracy**: Small scenes maintain high accuracy, large scenes trade accuracy for speed
- **61% improvement**: At 5000 entities, adaptive theta is 61% faster than fixed theta

### Negative

- **Increased code complexity**: Octree construction and traversal is non-trivial
- **Approximation error**: Layout differs slightly from exact solution
- **Memory overhead**: Octree requires O(n) additional memory
- **Parameter tuning**: Theta formula required experimentation to balance accuracy/speed

### Neutral

- Tree rebuild is O(n log n) per frame but amortized over force calculations
- GPU physics path uses different algorithm (grid-based), Barnes-Hut is CPU-only

## Alternatives Considered

### Alternative 1: Pairwise O(n²)

Direct force calculation between all pairs.

**Rejected because**:
- 10,000 entities = 50M pairs per frame
- Completely infeasible for target scale

### Alternative 2: Fruchterman-Reingold

Popular force-directed algorithm with cooling schedule.

**Rejected because**:
- Still O(n²) per iteration
- Cooling schedule doesn't fit continuous animation use case

### Alternative 3: GPU Compute Only

Move all physics to GPU compute shaders.

**Rejected because**:
- Not universally available (WebGL2 lacks compute)
- Firefox has performance issues with compute shaders
- Need CPU fallback anyway

### Alternative 4: Fixed Theta

Use constant θ=0.8 regardless of entity count.

**Rejected because**:
- Sub-optimal for both small and large scenes
- Adaptive theta provides 61% improvement at scale

## References

- [Barnes-Hut Wikipedia](https://en.wikipedia.org/wiki/Barnes%E2%80%93Hut_simulation)
- `crates/rource-core/src/physics/barnes_hut.rs`
- `docs/performance/CHRONOLOGY.md` - Phase 62: Adaptive Theta
- Benchmark: `cargo bench -p rource-core --bench barnes_hut_theta`

---

*ADR created: 2024-01-15*
*Last reviewed: 2026-01-26*
