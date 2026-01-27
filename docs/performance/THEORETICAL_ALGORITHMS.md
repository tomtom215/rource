# Theoretical Algorithms Reference

**Purpose**: This document catalogs advanced algorithmic research at the theoretical edge of mathematics
that may inform future Rource development. These algorithms represent the state-of-the-art in their
respective domains but may not have direct applicability to Rource's current architecture.

**Philosophy**: Even when an algorithm doesn't directly apply, understanding its techniques can inspire
optimization strategies and inform architectural decisions.

**Last Updated**: 2026-01-25 (Phase 57 added)

---

## Table of Contents

1. [SSSP: Breaking the Sorting Barrier](#sssp-breaking-the-sorting-barrier)
2. [Graph Coloring Algorithms](#graph-coloring-algorithms)
3. [2025 Mathematical Breakthroughs](#2025-mathematical-breakthroughs)
4. [Targeted Optimization Algorithms (Phase 55)](#targeted-optimization-algorithms-phase-55)
5. [Quantum Algorithms for Classical Simulation (Phase 56)](#quantum-algorithms-for-classical-simulation-phase-56)
6. [Cutting-Edge WASM Optimization Techniques (Phase 57)](#cutting-edge-wasm-optimization-techniques-phase-57)
7. [Applicability Framework](#applicability-framework)
8. [Future Exploration Queue](#future-exploration-queue)

---

## SSSP: Breaking the Sorting Barrier

### Citation

```
Duan, R., Mao, J., Mao, X., Shu, X., Yin, L. (2025).
"Breaking the Sorting Barrier for Directed Single-Source Shortest Paths"
arXiv:2504.17033v2

Affiliations: Tsinghua University, Stanford University, Max Planck Institute for Informatics
```

### Historical Context

Single-source shortest paths (SSSP) is one of the most fundamental problems in computer science.
For decades, researchers believed that any comparison-based SSSP algorithm on directed graphs
with real non-negative edge weights must require Ω(n log n) time—the "sorting barrier"—because
SSSP can encode sorting.

| Year | Algorithm | Complexity | Model |
|------|-----------|------------|-------|
| 1959 | Dijkstra | O(n²) | General |
| 1984 | Fredman-Tarjan (Fibonacci heaps) | O(m + n log n) | General |
| 1997 | Thorup (integer weights) | O(m) | Word RAM |
| 2025 | **This paper** | **O(m log^(2/3) n)** | **Comparison-addition** |

### Main Result

**Theorem 1.1**: There exists a deterministic algorithm that solves single-source shortest paths
on directed graphs with real non-negative edge weights in O(m log^(2/3) n) time.

This is the first result breaking the sorting barrier for directed graphs in the comparison-addition
model.

### Algorithm Overview

#### Parameters

```
n = number of vertices
m = number of edges
k = log^(1/3)(n)     // Pivot granularity
t = log^(2/3)(n)     // Level spacing
L = log(n) / t = k   // Number of recursion levels
```

#### Core Insight

Instead of maintaining a global priority queue (which requires sorting), the algorithm:
1. Limits the "frontier" set S to approximately |Ũ|/log^Ω(1)(n) vertices
2. Uses k-step Bellman-Ford relaxation to identify "pivots" with large subtrees
3. Recursively processes pivots, aggregating results level by level

#### Algorithm 1: FindPivots(B, S)

```
Input: Bound B, vertex set S (complete vertices with shortest path through S)
Output: Sets P (pivots) and W (worked vertices)

W ← S
W₀ ← S

for i = 1 to k do:
    Wᵢ ← ∅
    for each edge (u,v) where u ∈ Wᵢ₋₁:
        if d̂[u] + w(u,v) ≤ d̂[v]:
            d̂[v] ← d̂[u] + w(u,v)
            if d̂[u] + w(u,v) < B:
                Wᵢ ← Wᵢ ∪ {v}
    W ← W ∪ Wᵢ

    if |W| > k|S|:
        P ← S
        return (P, W)

// Construct shortest-path forest from S
F ← {(u,v) ∈ E : u,v ∈ W, d̂[v] = d̂[u] + w(u,v)}

// Pivots: roots with ≥k vertices in subtree
P ← {u ∈ S : |subtree(u, F)| ≥ k}

return (P, W)
```

**Complexity**: O(min{k²|S|, k|Ũ|})

#### Algorithm 2: BaseCase(B, S) (l = 0)

Standard Dijkstra from singleton source, extracting up to k+1 closest vertices.

```
Input: Bound B, singleton S = {x}
Output: Boundary B', complete set U

U₀ ← S
H ← BinaryHeap with ⟨x, d̂[x]⟩

while H non-empty AND |U₀| < k+1:
    ⟨u, d̂[u]⟩ ← H.ExtractMin()
    U₀ ← U₀ ∪ {u}

    for each edge (u,v):
        if d̂[u] + w(u,v) ≤ d̂[v] AND d̂[u] + w(u,v) < B:
            d̂[v] ← d̂[u] + w(u,v)
            H.InsertOrDecreaseKey(⟨v, d̂[v]⟩)

if |U₀| ≤ k:
    return (B' ← B, U ← U₀)
else:
    return (B' ← max{d̂[v] : v ∈ U₀}, U ← {v ∈ U₀ : d̂[v] < B'})
```

#### Algorithm 3: BMSSP(l, B, S) (Main Recursive Algorithm)

```
Input: Level l, bound B, source set S with |S| ≤ 2^(lt)
Output: Boundary B', complete set U ⊆ T_{<B'}(S)

if l = 0:
    return BaseCase(B, S)

// Step 1: Find pivots
(P, W) ← FindPivots(B, S)

// Step 2: Initialize data structure
D.Initialize(M := 2^((l-1)t), B)
for each x ∈ P:
    D.Insert(⟨x, d̂[x]⟩)

i ← 0
B'₀ ← min{d̂[x] : x ∈ P}  (or B if P = ∅)
U ← ∅

// Step 3: Main iteration
while |U| < k·2^(lt) AND D non-empty:
    i ← i + 1

    // Pull next batch of sources
    (Bᵢ, Sᵢ) ← D.Pull()

    // Recursive call
    (B'ᵢ, Uᵢ) ← BMSSP(l-1, Bᵢ, Sᵢ)

    U ← U ∪ Uᵢ
    K ← ∅

    // Step 4: Relax edges from Uᵢ
    for each edge (u,v) where u ∈ Uᵢ:
        if d̂[u] + w(u,v) ≤ d̂[v]:
            d̂[v] ← d̂[u] + w(u,v)

            if d̂[v] ∈ [Bᵢ, B):
                D.Insert(⟨v, d̂[v]⟩)
            else if d̂[v] ∈ [B'ᵢ, Bᵢ):
                K ← K ∪ {⟨v, d̂[v]⟩}

    // Step 5: Batch prepend recovered vertices
    batch ← K ∪ {⟨x, d̂[x]⟩ : x ∈ Sᵢ, d̂[x] ∈ [B'ᵢ, Bᵢ)}
    D.BatchPrepend(batch)

// Step 6: Finalize
B' ← min{B'ᵢ, B}
U ← U ∪ {x ∈ W : d̂[x] < B'}

return (B', U)
```

### Data Structure (Lemma 3.3)

A block-based linked list supporting three operations:

```
Structure:
- D₀: sequence of blocks for batch-prepended elements
- D₁: sequence of blocks for individually inserted elements
- Each block contains ≤ M key/value pairs
- BST maintains block upper bounds for binary search

Insert(⟨a, b⟩):
  Time: O(max{1, log(N/M)}) amortized
  - Locate block via BST
  - Insert into linked list O(1)
  - Split if block exceeds M elements

BatchPrepend(L):
  Time: O(|L| · max{1, log(|L|/M)}) amortized
  - Partition L into O(|L|/M) blocks via medians
  - Prepend sequence to D₀

Pull():
  Time: O(|S'|) amortized
  - Collect smallest M values from D₀ ∪ D₁
  - Return set S' and separator boundary
```

### Correctness Framework

**Lemma 3.6 (Pull Minimum)**: When splitting frontier S at threshold ℬ into X (smaller) and Y (larger),
any incomplete vertex v with d(v) < ℬ has its shortest path through some vertex in X.

**Lemma 3.7**: Algorithm 3 correctly returns U = T_{<B'}(S) with all vertices complete.

*Proof by induction on recursion level l.*

### Time Complexity Analysis

**Lemma 3.12**: Algorithm 3 runs in:
```
O((k + 2t/k)^(l+1) |U| + (t + l·log k)|N⁺_{[min d(x), B)}(U)|)
```

With k = log^(1/3)(n) and t = log^(2/3)(n):

| Component | Contribution |
|-----------|--------------|
| FindPivots (all levels) | O(n · log^(2/3) n) |
| Edge relaxations | O(m · log^(2/3) n) |
| Batch operations | O(m · log^(1/3) n · log log n) |
| **Total** | **O(m · log^(2/3) n)** |

### Implementation Notes

1. **Constant-degree assumption**: Transform general graphs to constant-degree with O(m) overhead
2. **Total order on paths**: Use lexicographic ordering ⟨length, hops, vertex sequence⟩ for tie-breaking
3. **Edge relaxation condition**: Uses "≤" to allow re-relaxation across levels (Remark 3.4)

### Rource Applicability

**Status**: NOT APPLICABLE

**Reason**: Rource operates on tree structures (directory hierarchies) and uses physics simulation
(Barnes-Hut) for layout, not shortest-path computation on general weighted directed graphs.

**Graph structures in Rource**:
- Directory trees (SSSP trivial: O(n) BFS/DFS)
- Commit sequences (linear, no SSSP needed)
- Spatial indices (QuadTree, geometric queries)

**Potential future use cases** (if Rource expanded):
- File dependency graph visualization
- Cross-repository navigation
- Weighted commit ancestry analysis

### Key Takeaways for Optimization

Even though this algorithm doesn't apply, its techniques offer insights:

1. **Frontier Reduction**: Limit working set size to avoid global sorting
2. **Recursive Decomposition**: Break problems into bounded subproblems
3. **Lazy Evaluation**: Process in batches rather than one-at-a-time
4. **Custom Data Structures**: Design structures for specific operation patterns

---

## Graph Coloring Algorithms

### Citation

```
Kakatkar, C. (2025).
"Graph Coloring for Data Science: A Comprehensive Guide"
Towards Data Science, August 2025

Additional references:
- Welsh, D.J.A.; Powell, M.B. (1967). "An upper bound for the chromatic number"
- Brélaz, D. (1979). "New methods to color the vertices of a graph"
```

### Problem Definition

**Graph Coloring**: Assign colors to vertices of a graph G = (V, E) such that no two adjacent
vertices share the same color, while minimizing the number of colors used.

| Metric | Definition |
|--------|------------|
| **Chromatic Number χ(G)** | Minimum colors needed for proper coloring |
| **k-colorable** | Graph can be properly colored with ≤ k colors |
| **Chromatic Polynomial P(G, k)** | Number of proper k-colorings of G |

**Complexity**: Determining χ(G) is NP-hard. Even determining if χ(G) ≤ 3 is NP-complete.

### Algorithm 1: Greedy Coloring

```
GREEDY-COLOR(G, ordering):
    for each vertex v in ordering:
        color[v] ← smallest color not used by N(v)
    return color[]
```

| Property | Value |
|----------|-------|
| Time | O(n + m) with adjacency list |
| Space | O(n) for color array |
| Colors Used | ≤ Δ(G) + 1 where Δ = max degree |
| Optimal? | Order-dependent; worst case uses Grundy number |

**Key Insight**: The greedy bound χ(G) ≤ Δ(G) + 1 is tight only for complete graphs and odd cycles.

### Algorithm 2: Welsh-Powell (1967)

```
WELSH-POWELL(G):
    L ← vertices sorted by degree (descending)
    c ← 0
    while uncolored vertices exist:
        c ← c + 1
        for each uncolored v in L:
            if no neighbor of v has color c:
                color[v] ← c
    return color[]
```

| Property | Value |
|----------|-------|
| Time | O(n²) |
| Space | O(n) |
| Colors Used | ≤ max{min(d(vᵢ) + 1, i)} over degree ordering |
| Optimal? | Heuristic; good for sparse graphs |

**Key Insight**: Processing high-degree vertices first tends to use fewer colors because they
have more constraints early, when more colors are available.

### Algorithm 3: DSatur (Brélaz, 1979)

```
DSATUR(G):
    saturation[v] ← 0 for all v
    Q ← priority queue ordered by (saturation, degree)

    while Q not empty:
        v ← Q.extractMax()
        color[v] ← smallest color not in N(v)'s colors
        for each uncolored neighbor u of v:
            saturation[u] ← |{color[w] : w ∈ N(u), w colored}|
            Q.updateKey(u)

    return color[]
```

| Property | Value |
|----------|-------|
| Time | O((n + m) log n) with red-black tree |
| Space | O(n + m) |
| Exactness | Exact for bipartite, cycle, wheel graphs |
| Best For | Dense graphs; quality over speed |

**Efficient Implementation**: Use two-level bucket queues:
- Level 1: Priority queue keyed by saturation degree
- Level 2: For each saturation bucket, secondary queue by degree in uncolored subgraph

### Algorithm 4: Chromatic Polynomial for Cycles

For cycle graph Cₙ, the chromatic polynomial is:

```
P(Cₙ, k) = (k-1)ⁿ + (-1)ⁿ(k-1)
```

**Derivation via Deletion-Contraction**:

```
Recurrence: P(n, k) = k(k-1)^(n-1) - P(n-1, k)

Base cases:
  P(1, k) = k                    (single vertex)
  P(2, k) = k(k-1)               (single edge)
  P(3, k) = k(k-1)(k-2)          (triangle)

Homogeneous solution: Pₕ(n) = C(-1)ⁿ
Particular solution: Pₚ(n) = (k-1)ⁿ
General solution: P(n, k) = (k-1)ⁿ + C(-1)ⁿ

Using P(3, k) = k(k-1)(k-2):
  (k-1)³ - C = k(k-1)(k-2)
  C = (k-1)³ - k(k-1)(k-2) = (k-1)[(k-1)² - k(k-2)]
  C = (k-1)[k² - 2k + 1 - k² + 2k] = (k-1)

Final: P(n, k) = (k-1)ⁿ + (-1)ⁿ(k-1)
```

| n (vertices) | k=3 colors | k=4 colors |
|--------------|------------|------------|
| 3 | 6 | 24 |
| 4 | 18 | 84 |
| 5 | 30 | 240 |
| 6 | 66 | 732 |

**Python Implementation**:

```python
def chromatic_polynomial_cycle(n: int, k: int) -> int:
    """O(1) closed-form evaluation."""
    return (k - 1)**n + ((-1)**n) * (k - 1)
```

### Application Domains

#### 1. Scheduling and Timetabling

**Conflict Graph Model**:
- Vertices = tasks/events
- Edges = conflicts (cannot occur simultaneously)
- Colors = time slots

**Example**: Exam scheduling where students taking multiple exams create conflicts.

#### 2. Register Allocation (Compilers)

**Interference Graph Model**:
- Vertices = live ranges (variables)
- Edges = overlapping lifetimes
- Colors = CPU registers
- Spilling = when χ(G) > available registers

**Complexity**: Chaitin proved optimal register allocation is NP-complete.

#### 3. Frequency Assignment (Wireless Networks)

**Interference Graph Model**:
- Vertices = transmitters
- Edges = potential interference
- Colors = frequency channels

#### 4. Feature Selection (Machine Learning)

**Correlation Graph Model**:
- Vertices = features
- Edges = high correlation
- Colors = feature groups
- Select one representative per color

### Rource Applicability Analysis

**Status**: NOT DIRECTLY APPLICABLE

**Structural Analysis**:

| Rource Structure | Graph Type | Chromatic Properties |
|-----------------|------------|---------------------|
| Directory Tree | Tree | χ = 2 (bipartite) |
| QuadTree | 4-ary tree | Implicit 4-coloring by quadrant |
| Commit History | DAG | χ ≤ longest path + 1 |
| Spatial Index | Grid/Tree | Bounded chromatic number |

**Why Graph Coloring Doesn't Apply**:

1. **Trees are 2-colorable**: All trees are bipartite, trivially colored in O(n)
2. **QuadTree has inherent coloring**: NW=0, NE=1, SW=2, SE=3 is automatic 4-coloring
3. **No general graphs**: Rource doesn't process arbitrary graphs with cycles
4. **No scheduling conflicts**: No concurrent resource contention requiring coloring
5. **No register allocation**: Rource is not a compiler

**Existing "Coloring" in Rource**:

| Component | Type | Implementation |
|-----------|------|----------------|
| File extensions | Visual assignment | 50+ hardcoded + hash fallback |
| Draw command batching | Conflict grouping | Sort-key ordering |
| Physics repulsion | Conflict detection | `should_repel()` predicate |

These implement the *concept* of conflict detection without requiring explicit graph coloring algorithms.

### Key Takeaways for Optimization

1. **Closed-Form > Recurrence**: The chromatic polynomial example shows O(1) beats O(n)
   - Already applied in Rource: LUT optimizations (Phase 45)

2. **Implicit Coloring**: Spatial structures inherently provide coloring
   - QuadTree quadrants are a natural 4-coloring
   - Tree levels provide 2-coloring

3. **Conflict Detection Patterns**: The concept of "no two adjacent items share property X"
   appears throughout Rource:
   - Physics: siblings repel
   - Rendering: same-texture batches
   - Sorting: group by blend mode

4. **When to Use DSatur**: If Rource ever needed to color a general graph:
   - Use DSatur for quality (exact on many graph classes)
   - Use Welsh-Powell for speed on sparse graphs
   - O((n+m) log n) is acceptable for preprocessing

### Performance Comparison

| Algorithm | Time | Colors (avg) | Best Use Case |
|-----------|------|--------------|---------------|
| Greedy | O(n + m) | Variable | Any, order matters |
| Welsh-Powell | O(n²) | Good | Sparse graphs, speed |
| DSatur | O((n+m) log n) | Best | Dense graphs, quality |
| Branch-and-Bound DSatur | Exponential | Optimal | Small graphs, exact |

### References

- Welsh, D.J.A.; Powell, M.B. (1967). "An upper bound for the chromatic number of a graph"
- Brélaz, D. (1979). "New methods to color the vertices of a graph"
- San Segundo, P. (2012). "A new DSATUR-based algorithm for exact vertex coloring"
- Geeksforgeeks: [DSatur Algorithm](https://www.geeksforgeeks.org/dsa/dsatur-algorithm-for-graph-coloring/)
- Geeksforgeeks: [Welsh-Powell Algorithm](https://www.geeksforgeeks.org/dsa/welsh-powell-graph-colouring-algorithm/)

---

## 2025 Mathematical Breakthroughs

### Overview

Analysis of Scientific American's "10 Biggest Math Breakthroughs of 2025" for algorithmic
insights applicable to computational graphics and physics simulation.

### Moving Sofa Problem (SOLVED)

#### Citation

```
Baek, J. (2024).
"Optimality of Gerver's Sofa"
arXiv:2411.19826, November 2024

Original construction:
Gerver, J. L. (1992). "On Moving a Sofa Around a Corner"
Geometriae Dedicata 42, 267-283
```

#### Problem Statement

Find the largest 2D shape (measured by area) that can navigate a right-angle corner
in an L-shaped corridor of unit width.

#### Solution

Gerver's sofa with 18 curve sections achieves the maximum area:

```
Area = 2.2195316688... (Moving Sofa Constant)
```

The boundary consists of:
- 3 straight line segments
- 15 analytic curves

**Key Parameters** (from solving 4 coupled equations):
```
A = 0.094426560843653...  (curve transition parameter)
B = 1.399203727333547...  (boundary scaling)
φ = 0.039177364790084...  (initial angle)
θ = 0.681301509382725...  (sweep angle)
```

#### Mathematical Framework

**Radial function r(α)**: Distance from origin as function of angle, piecewise defined:

```
r(α) = ½                           for 0 ≤ α < φ
r(α) = (linear interpolation)       for φ ≤ α < θ
r(α) = A + α - φ                   for intermediate region
r(α) = (parabolic decay)           for larger angles
```

**Area integral**: Sum of three terms over angle intervals, incorporating support functions
and their derivatives via the calculus of variations.

#### Proof Technique

1. **Infinite-dimensional representation**: Each sofa shape as a point in function space
2. **Custom Q function**: Defined with properties enabling optimality verification
3. **Euler-Lagrange equations**: Characterize extremal shapes
4. **No computer assistance**: Pure logical reasoning (unusual for such proofs)

#### Rource Applicability

**Status**: NOT DIRECTLY APPLICABLE

Rource doesn't navigate physical corridors. However, variational calculus techniques
could inform future work on:
- Optimal spline interpolation (energy-minimizing curves)
- Camera path smoothing with geometric constraints
- Animation trajectory optimization

### Noperthedron

#### Citation

```
Steininger, J.; Yurkevich, S. (2025).
"A Convex Polyhedron without Rupert's Property"
arXiv:2508.18475, August 2025
```

#### Definition

A 3D convex body has **Rupert's property** if a copy of itself can pass through a
straight hole cut in the body. The noperthedron is the first convex polyhedron
proven to lack this property.

#### Structure

| Property | Value |
|----------|-------|
| Vertices | 90 (3 × 30, point-symmetric) |
| Edges | 240 |
| Faces | 152 (150 triangles + 2 regular 15-gons) |
| Symmetry | C₃₀ group (point-symmetric about origin) |

#### Proof Method

1. **Parameter space discretization**: Divided orientation space into ~18 million blocks
2. **Center point testing**: Checked each block's center for Rupert passage
3. **Local/global theorem application**: Ruled out entire blocks via geometric arguments
4. **Exhaustive elimination**: All blocks ruled out ⟹ no Rupert passage exists

#### Rource Applicability

**Status**: NOT APPLICABLE

Rource is 2D and has no collision/passage detection requirements.

### Hilbert's 6th Problem Progress

#### Citation

```
Deng, Y.; Hani, Z.; Ma, X. (2025).
"Hilbert's Sixth Problem: Derivation of Fluid Equations via Boltzmann's Kinetic Theory"
arXiv:2503.01800, March 2025
```

#### Achievement

Rigorously derived macroscopic fluid equations (Navier-Stokes, compressible Euler)
from Newtonian mechanics via Boltzmann kinetic theory.

#### The Three-Level Hierarchy

```
Level 1: MICROSCOPIC (Newton's laws)
    Individual particles with positions, velocities
    Deterministic dynamics: F = ma
    Scale: ~10²³ particles in physical systems
                    ↓ Boltzmann-Grad limit
Level 2: MESOSCOPIC (Boltzmann equation)
    Distribution function f(x, v, t)
    Statistical description of particle velocities
    ∂f/∂t + v·∇f = Q(f,f)  (collision integral)
                    ↓ Hydrodynamic limit (Knudsen → 0)
Level 3: MACROSCOPIC (Navier-Stokes/Euler)
    Continuum fields: density ρ, velocity u, pressure p
    ∂ρ/∂t + ∇·(ρu) = 0     (continuity)
    ρ(∂u/∂t + u·∇u) = -∇p + μΔu  (momentum)
```

#### Key Innovations

- **Long bonds**: Mathematical construct connecting temporally separated collisions
- **Layered cluster forest structure**: Hierarchical organization of collision events
- **Arbitrary time horizons**: Previous proofs only worked on short timescales

#### Rource Applicability

**Status**: NOT DIRECTLY APPLICABLE (but conceptually parallel)

Rource uses discrete particle simulation (Barnes-Hut), not continuum PDEs.
However, the hierarchical modeling parallels Barnes-Hut:

| Hilbert Concept | Barnes-Hut Analog |
|-----------------|-------------------|
| Particles | Directory nodes |
| Boltzmann distribution | QuadTree node aggregates |
| Navier-Stokes continuum | Center-of-mass approximation |
| Knudsen number → 0 | θ parameter → 0 |

### Fibonacci Pick-up Sticks Problem

#### Citation

```
Sudbury, A.; Sun, A.; Treeby, D.; Wang, E. (2025).
"Pick-up Sticks and the Fibonacci Factorial"
arXiv:2504.19911, April 2025
```

#### The Problem

Given n sticks with random lengths uniformly distributed in [0, 1], what is the
probability that no three sticks can form a triangle?

#### The Discovery

The probability equals the reciprocal of the **Fibonorial** (product of Fibonacci numbers):

```
P(no triangle among n sticks) = 1 / ∏(i=1 to n) F_i

where F_i is the i-th Fibonacci number: 1, 1, 2, 3, 5, 8, 13, 21, ...
```

**Examples**:
```
n = 3: P = 1/(1×1×2) = 1/2
n = 4: P = 1/(1×1×2×3) = 1/6
n = 5: P = 1/(1×1×2×3×5) = 1/30
n = 6: P = 1/(1×1×2×3×5×8) = 1/240
n = 7: P = 1/(1×1×2×3×5×8×13) = 1/3120
```

#### Significance

The appearance of Fibonacci numbers was completely unexpected—demonstrating that
problems with "obvious" iterative solutions may have elegant closed forms.

#### Rource Applicability

**Status**: NOT DIRECTLY APPLICABLE

No triangle-formation probability in Rource. However, reinforces the principle
that closed-form solutions should be sought (already applied in Phase 45 LUTs).

### Dudeney's Dissection Optimality

#### Citation

```
Demaine, E.; Kamata, T.; Uehara, R. (2024).
"Dudeney's Dissection is Optimal"
arXiv:2412.03865, December 2024
```

#### The Problem

What is the minimum number of pieces needed to dissect an equilateral triangle
and reassemble into a square of equal area?

#### The Result

**4 pieces is optimal** (Dudeney's 1902 solution cannot be improved).

**Proof technique**: Matching diagrams to systematically rule out 2-piece and 3-piece
dissections under the constraint that pieces cannot be flipped.

#### Rource Applicability

**Status**: NOT APPLICABLE

No geometric dissection operations in Rource.

### Conceptual Insights Summary

| Breakthrough | Transferable Concept | Rource Connection |
|--------------|---------------------|-------------------|
| Moving Sofa | Variational calculus | Spline optimization |
| Noperthedron | Exhaustive block elimination | Parameter space testing |
| Hilbert's 6th | Hierarchical scale bridging | Barnes-Hut analogy |
| Fibonacci Sticks | Unexpected closed forms | LUT philosophy |
| Dissection | Matching diagram proofs | N/A |

### References

- [arXiv:2411.19826](https://arxiv.org/abs/2411.19826) - Optimality of Gerver's Sofa
- [arXiv:2508.18475](https://arxiv.org/abs/2508.18475) - Noperthedron
- [arXiv:2503.01800](https://arxiv.org/abs/2503.01800) - Hilbert's 6th Problem
- [arXiv:2504.19911](https://arxiv.org/abs/2504.19911) - Fibonacci Pick-up Sticks
- [arXiv:2412.03865](https://arxiv.org/abs/2412.03865) - Dudeney's Dissection
- [Wolfram MathWorld: Gerver Sofa](https://mathworld.wolfram.com/GerverSofa.html)
- [Quanta Magazine: Moving Sofa](https://www.quantamagazine.org/the-largest-sofa-you-can-move-around-a-corner-20250214/)
- [Scientific American: 2025 Breakthroughs](https://www.scientificamerican.com/article/the-top-10-math-discoveries-of-2025/)

---

## Targeted Optimization Algorithms (Phase 55)

### Overview

This section documents algorithms specifically targeted at Rource's workload: force-directed layout,
spatial indexing, WASM memory efficiency, and tree operations. Unlike general mathematical
breakthroughs, these algorithms have existing Rust implementations and clear applicability paths.

### GPU Force-Directed Layout

#### GraphWaGu (Eurographics 2022)

```
Dyken, L.; Poudel, P.; Usher, W.; Petruzza, S.; Chen, J.Y.; Kumar, S. (2022)
"GraphWaGu: GPU Powered Large Scale Graph Layout Computation and Rendering for the Web"
Eurographics Symposium on Parallel Graphics and Visualization
```

**Achievement**: First WebGPU-based graph visualization achieving 100K nodes + 2M edges at
interactive rates in web browsers.

**Technical Approach**:
1. Modified Fruchterman-Reingold with Barnes-Hut approximation
2. Quadtree built in compute shaders each frame
3. Buffer allocation: `6 × |V|` nodes pre-allocated
4. Node storage: boundary rect, center of mass, mass, 4 child indices

**WGSL Compute Shader Structure**:
```wgsl
struct QuadNode {
    min_x: f32, min_y: f32, max_x: f32, max_y: f32,  // boundary
    mass_x: f32, mass_y: f32, mass: f32,              // center of mass
    nw: u32, ne: u32, sw: u32, se: u32,               // child indices (0 = none)
}

@group(0) @binding(0) var<storage, read_write> nodes: array<QuadNode>;
@group(0) @binding(1) var<storage, read> positions: array<vec2<f32>>;
```

**Rource Applicability**: **ALREADY IMPLEMENTED (different approach)**

Rource uses a 9-pass GPU spatial hash pipeline instead of GPU Barnes-Hut:

| Pass | Operation | Purpose |
|------|-----------|---------|
| 1 | Clear cell counts | Initialize grid |
| 2 | Count entities per cell | Population count |
| 3 | Prefix sum (local) | Cell offsets (workgroup) |
| 4 | Prefix sum (partials) | Combine partial sums |
| 5 | Prefix sum (add) | Finalize offsets |
| 6 | Init scatter offsets | Reset write pointers |
| 7 | Scatter entities | Sort by cell |
| 8 | Calculate forces | O(n) 3×3 neighborhood |
| 9 | Integrate | Update positions |

**Complexity Comparison** (5000 entities):

| Approach | Comparisons | Notes |
|----------|-------------|-------|
| O(n²) brute force | 25,000,000 | Exact |
| O(n log n) Barnes-Hut | ~65,000 | Approximate (θ=0.8) |
| O(n) spatial hash | ~11,000 | Exact (neighbors only) |

The spatial hash approach avoids tree construction overhead while achieving better
asymptotic complexity for Rource's uniform entity distribution.

#### GPU ForceAtlas2 (ICPP 2017)

```
Brinkmann, M.; Ziegler, H. (2017)
"GPU ForceAtlas2"
International Conference on Parallel Processing
```

**Performance**: 40-123× speedup over CPU ForceAtlas2.
Handles 4M nodes + 120M edges in 14 minutes vs 9+ hours CPU.

**Implementation**: Available in LonestarGPU (Burtscher & Pingali). CUDA-only, but algorithm
translates to WGSL/SPIR-V.

**Rource Applicability**: **ALREADY IMPLEMENTED (spatial hash)**

---

### Spatial Indexing Alternatives

#### Loose QuadTree

**Concept**: Each quadrant boundary overflows 50% into neighbors.

```
Standard QuadTree:          Loose QuadTree:
+-------+-------+           +----+----+----+
|       |       |           |    | OL |    |  OL = overlap region
|  NW   |  NE   |           +----+----+----+
|       |       |           | OL |    | OL |
+-------+-------+    →      +----+----+----+
|       |       |           |    | OL |    |
|  SW   |  SE   |           +----+----+----+
|       |       |
+-------+-------+
```

**Benefit**: Objects near boundaries fit in multiple valid quadrants without restructuring.

**Trade-off**: More objects checked during queries due to boundary overlap.

**Complexity**:
- Insert: O(1) amortized (no restructuring)
- Query: O(k) where k = objects in overlapping regions

**Rource Applicability**: **FUTURE CONSIDERATION**

Current implementation uses clear-and-rebuild pattern each frame. Loose quadtree would
benefit incremental update scenarios more than full rebuild.

#### Geohash Grid

**Concept**: Fixed-depth spatial encoding via interleaved coordinate bits.

```rust
// Standard approach
fn geohash(x: u32, y: u32, bits: u32) -> u64 {
    let mut hash = 0u64;
    for i in 0..bits {
        hash |= ((x >> (bits - 1 - i)) & 1) as u64) << (2 * i + 1);
        hash |= ((y >> (bits - 1 - i)) & 1) as u64) << (2 * i);
    }
    hash
}

// Simplified for power-of-2 grids
fn grid_cell(x: f32, y: f32, shift: u32, width: u32) -> usize {
    let ix = (x as u32) >> shift;
    let iy = (y as u32) >> shift;
    (iy * width + ix) as usize
}
```

**Complexity**:
- Cell lookup: O(1) vs QuadTree O(log n)
- Neighbor iteration: O(9) for 3×3 neighborhood

**Rource Applicability**: **FUTURE CONSIDERATION**

GPU spatial hash already uses grid-based approach. Applying same pattern to CPU
would unify implementations.

#### KD-Tree

**When KD-Tree Wins**: Non-uniform distribution with adaptive split planes.

**When QuadTree Wins**: Uniform distribution with powers-of-two arithmetic.

**Rource Applicability**: **NOT NEEDED**

Rource entities are relatively uniformly distributed (file nodes spread across
directory tree). QuadTree's simpler implementation is preferable.

---

### Succinct Data Structures

#### vers-vecs

**Crate**: `vers-vecs` v1.1.0

**Data Structures**:
- `RsVec`: O(1) rank, O(log n) select
- `EliasFanoVec`: Constant-time predecessor on monotonic sequences
- `BinaryRmq`/`FastRmq`: O(1) range minimum queries
- `WaveletMatrix`: O(k) rank/select for k-bit symbols
- `BpTree`: O(log n) tree navigation

**Performance**: "Among the fastest publicly available bit vector implementations"

**WASM Compatibility**: **NOT COMPATIBLE**

Uses x86_64 intrinsics (popcnt, pdep, tzcnt). Fallback implementations are
"significantly worse" per documentation.

**Rource Applicability**: **NOT APPLICABLE FOR WASM**

#### succinctly

**Crate**: `succinctly`

**Data Structures**:
- `BitVec`: O(1) rank, O(log n) select with ~3% space overhead
- `BalancedParens`: O(1) tree operations with ~6% overhead
- `JsonIndex`: SIMD-accelerated JSON semi-indexing (880 MiB/s x86_64)
- `YamlIndex`: Complete YAML 1.2 with anchor/alias resolution
- `DsvIndex`: 85-1,676 MiB/s CSV parsing

**Performance Benchmarks** (x86_64):
- Rank: ~3 ns
- Select: ~50 ns
- JSON throughput: 510 MiB/s (vs 167 MiB/s serde_json)
- Memory: 17-46× less than DOM parsers

**WASM Compatibility**: **COMPATIBLE**

> "no_std compatible - Works in embedded and WASM environments"

**Rource Applicability**: **POTENTIALLY APPLICABLE**

| Use Case | Current | With Succinctly | Memory Savings |
|----------|---------|-----------------|----------------|
| 100K file visibility | 100KB (Vec<bool>) | 12.5KB (BitVec) | 8× |
| Entity selection | ~4MB (FxHashSet) | ~12.5KB (BitVec) | ~320× |
| Directory tree | Pointers | BP Tree | ~10× |

**Recommendation**: Low priority. Benchmark succinctly's WASM performance before adopting.
Current FxHashSet approach is already fast for typical repository sizes.

---

### Learned Indexes

#### PGM-Index

**Citation**:
```
Ferragina, P.; Vinciguerra, G. (2020)
"The PGM-index: a fully-dynamic compressed learned index with provable worst-case bounds"
VLDB 2020
```

**Concept**: Replace B-tree levels with piecewise linear models predicting element position.

**Complexity**:
- Query: O(log n / log ε) where ε = error bound
- Space: O(n / ε)
- Build: O(n)

**Performance Claims**:
- 3-10× faster than binary search for large sorted datasets
- 1.7× faster than BTreeSet on 1M random keys
- 3× less memory than B-trees

**Rust Crate**: `pgm_index`

```rust
use pgm_index::PGMIndex;

let keys: Vec<u64> = sorted_file_hashes();
let index = PGMIndex::new(&keys, 64);  // epsilon=64

// Lookup returns approximate position
let pos = index.search(target_hash);
// Binary search in range [pos - epsilon, pos + epsilon]
```

**Rource Applicability**: **NOT APPLICABLE**

| Criterion | PGM-Index | FxHashMap (Current) |
|-----------|-----------|---------------------|
| Best for | Range queries on sorted data | Point queries |
| Lookup | O(log n / log ε) | O(1) average |
| Requires | Sorted keys | None |
| Rource pattern | Range queries rare | Point queries dominant |

Rource's file lookup is point-query dominated (find file by exact path).
FxHashMap's O(1) average case is superior for this workload.

---

### Tree Balancing

#### Grandchildren-Weight-Balanced Trees (WADS 2025)

**Citation**:
```
arXiv:2410.08825 (2025)
"Grandchildren-Weight-Balanced Trees"
Workshop on Algorithms and Data Structures
```

**Innovation**: Balance invariant on grandchildren instead of children.

**Results**:
- Height: < 2 log₂(n) (vs ≥ 2 log₂(n) for standard weight-balanced)
- Rotations: O(1) amortized per update (vs O(log n) for AVL)

**Rource Applicability**: **NOT APPLICABLE**

Rource uses n-ary directory trees with HashMap child index, not self-balancing BSTs.
Directory operations are infrequent relative to physics/rendering.

#### UFO Trees (PPoPP 2026)

**Citation**:
```
arXiv:2601.10706 (2026)
"UFO Trees: Batch-Dynamic Trees with Polylogarithmic Depth"
Principles and Practice of Parallel Programming
```

**Innovation**: Process multiple tree updates simultaneously.

**Complexity**:
- Work: O(min{k log(1+n/k), kD}) where k = batch size, D = max depth
- Depth: O(log n log k) with parallelism

**Requirement**: WASM threads (SharedArrayBuffer)

**Rource Applicability**: **NOT APPLICABLE**

1. Requires WASM threads—limited browser support
2. Rource processes commits sequentially
3. Directory tree updates are not a bottleneck

---

### Phase 55 References

- [GraphWaGu Paper](https://stevepetruzza.io/pubs/graphwagu-2022.pdf)
- [GraphWaGu GitHub](https://github.com/harp-lab/GraphWaGu)
- [vers-vecs Documentation](https://docs.rs/vers-vecs/latest/vers_vecs/)
- [succinctly GitHub](https://github.com/rust-works/succinctly)
- [PGM-Index Rust](https://docs.rs/pgm_index/latest/pgm_index/)
- [PGM-Index Original](https://github.com/gvinciguerra/PGM-index)
- [Grandchildren-WB Trees](https://arxiv.org/abs/2410.08825)
- [UFO Trees](https://arxiv.org/abs/2601.10706)

---

## Quantum Algorithms for Classical Simulation (Phase 56)

### Overview

This section documents quantum algorithms implemented in Rust that can run on classical computers
via simulation. While these algorithms promise speedups on actual quantum hardware, their utility
on classical simulators is limited by exponential state-space growth.

### Rust Quantum Libraries

#### LogosQ

**Citation**:
```
An, S.; Wang, J.; Slavakis, K. (2025)
"LogosQ: A High-Performance and Type-Safe Quantum Computing Library in Rust"
arXiv:2512.23183, December 2025
Georgia Institute of Technology, Institute of Science Tokyo
```

**Key Features**:
- Type-safe quantum circuits via Rust's static analysis
- Direct state-vector manipulation
- FFT-optimized Quantum Fourier Transform
- Adaptive parallel processing

**Performance Benchmarks**:
| Comparison | Speedup |
|------------|---------|
| vs Qiskit (Python) | 2-5× |
| vs Yao.jl (Julia) | 6-22× |
| vs Q# | Competitive |
| State preparation | Up to 900× |

**Crate**: `logosq` v0.2.5+

#### QuantRS2

**Features**:
- Multi-backend simulation (state-vector, tensor-network)
- Built-in QAOA, Grover, QFT, QPE, simplified Shor
- GPU acceleration, SIMD optimization
- Hardware integration (IBM, Azure, D-Wave)

**Architecture**:
- `quantrs2-core`: Types, traits, abstractions
- `quantrs2-circuit`: Circuit DSL, gate definitions
- `quantrs2-sim`: Simulators (30+ qubit capacity)
- `quantrs2-anneal`: Quantum annealing, classical annealing

**Crate**: `quantrs2` v0.1.0-rc.1

---

### VQE (Variational Quantum Eigensolver)

**Problem Class**: Ground-state energy of quantum Hamiltonians (chemistry).

**Algorithm Structure**:
```
1. Initialize parameterized quantum circuit U(θ)
2. Prepare trial state |ψ(θ)⟩ = U(θ)|0⟩
3. Measure expectation value ⟨H⟩ = ⟨ψ(θ)|H|ψ(θ)⟩
4. Classical optimizer updates θ to minimize ⟨H⟩
5. Repeat until convergence
```

**Complexity**:
- Quantum: O(poly(n)) per measurement
- Classical optimizer: Problem-dependent (typically gradient-based)

**Applications**:
- Molecular ground states (H₂, LiH, H₂O)
- Condensed matter (Heisenberg models)
- Drug discovery (molecular interactions)

**Rource Applicability**: **NOT APPLICABLE**
- VQE solves quantum chemistry problems
- Rource has no chemistry computation requirements

---

### QAOA (Quantum Approximate Optimization Algorithm)

**Problem Class**: Combinatorial optimization encoded as QUBO/Ising.

**QUBO Formulation**:
```
Minimize: f(x) = x^T Q x
where x ∈ {0,1}^n (binary vector)
      Q = n×n real symmetric matrix
```

**Ising Formulation**:
```
Minimize: H = Σᵢⱼ Jᵢⱼ σᵢ σⱼ + Σᵢ hᵢ σᵢ
where σᵢ ∈ {-1, +1}
```

**Algorithm Structure**:
```
1. Encode objective as problem Hamiltonian Hₚ
2. Define mixer Hamiltonian Hₘ (typically Σᵢ Xᵢ)
3. Prepare initial state |+⟩⊗n
4. Apply p layers: U(β,γ) = ∏ₖ e^{-iβₖHₘ} e^{-iγₖHₚ}
5. Measure and decode solution
6. Classical optimizer tunes (β,γ)
```

**2025 Results**:
- 156-qubit IBM: Outperformed CPLEX, simulated annealing
- Graph decomposition: 100-vertex MaxCut reduced to ~10 vertices
- Approximation ratio: 0.96 average

**Theoretical Connection to Force-Directed Layout**:

Force layout energy:
```
E = Σ_{edges} k·(d - d₀)² + Σ_{pairs} C/d²
```

This resembles quadratic optimization, BUT:
- Force layout uses continuous variables (x,y ∈ ℝ)
- QAOA requires binary variables (z ∈ {0,1})

**QUBO Encoding** (theoretical, impractical):
```
1. Discretize space: G×G grid cells
2. Variables: xᵢₖ = 1 if entity i in cell k
3. Problem size: n·G² binary variables
4. 10K entities × 100² grid = 100M variables
```

**Rource Applicability**: **NOT APPLICABLE**
- Scale: Classical simulation limited to ~30 qubits
- Variable type: QAOA needs discrete; layout is continuous
- Current algorithm: O(n) GPU spatial hash is optimal

---

### Grover's Algorithm

**Problem Class**: Unstructured database search.

**Speedup**: O(√n) vs O(n) classical.

**Algorithm Structure**:
```
1. Initialize uniform superposition |s⟩ = H⊗n|0⟩
2. Apply Grover iteration O(√n) times:
   a. Oracle: |x⟩ → -|x⟩ if f(x)=1
   b. Diffusion: 2|s⟩⟨s| - I
3. Measure to obtain marked item
```

**Optimal Iterations**: π√n/4

**Rource Search Operations**:

| Operation | Current | Complexity | vs Grover O(√n) |
|-----------|---------|------------|-----------------|
| File by path | FxHashMap | O(1) | O(1) << O(√n) |
| File by ID | FxHashMap | O(1) | O(1) << O(√n) |
| Spatial query | QuadTree | O(log n) | O(log n) < O(√n) |
| Range search | QuadTree | O(log n + k) | Comparable for small k |

**Rource Applicability**: **NOT APPLICABLE**
- Structured data: Hash tables and spatial indices beat O(√n)
- Grover only helps when NO structure is exploitable

---

### Quantum Fourier Transform (QFT)

**Definition**: Quantum analog of Discrete Fourier Transform.

```
|j⟩ → (1/√N) Σₖ e^{2πijk/N} |k⟩
```

**Gate Complexity**: O(n²) for n qubits (O(n log n) with approximation).

**Applications**:
- Phase estimation
- Shor's algorithm (period finding)
- Quantum signal processing

**LogosQ Optimization**: FFT-based classical preprocessing achieves 900× speedup.

**Potential Rource Application**: Convolution for blur effects.

**Bloom Effect Analysis**:
```
Current: Sliding window O(n) for kernel size k
FFT:     O(n log n) regardless of k
```

| Method | k=7 | k=15 | k=64 | k=256 |
|--------|-----|------|------|-------|
| Direct O(n·k) | 7n | 15n | 64n | 256n |
| Sliding O(n) | n | n | n | n |
| FFT O(n log n) | n·log n | n·log n | n·log n | n·log n |

For small kernels (k < 64), sliding window wins.

**Rource Applicability**: **NOT APPLICABLE**
- Bloom uses small kernels (7-15 pixels)
- Sliding window O(n) is already optimal
- QFT simulation overhead negates theoretical advantage

---

### Quantum Annealing

**Problem Class**: QUBO/Ising minimization via simulated quantum tunneling.

**QuantRS2-Anneal Backends**:
- Classical simulated annealing
- Path integral Monte Carlo
- Coherent Ising machine simulation

**Hardware**: D-Wave systems (2000+ qubits, but sparse connectivity).

**Force Layout as Ising** (theoretical):

```
Standard force energy: E = Σ springs + Σ repulsions

Discretized Ising: σᵢₖ = 1 if entity i at grid cell k
                   E = ΣΣ J(i,j,k,l) σᵢₖ σⱼₗ
```

**Challenges**:
- Variable explosion: n × G² binary variables
- Connectivity constraints: D-Wave graph is sparse
- Embedding overhead: Logical → physical qubit mapping
- Precision loss: Continuous → discrete

**Rource Applicability**: **NOT APPLICABLE**
- Current O(n) GPU hash is asymptotically optimal
- Continuous gradient descent is natural for layout
- Simulated annealing (classical) available if needed

---

### Qubit Simulation Limits

**State Vector Growth**:

| Qubits | States | Memory (complex128) |
|--------|--------|---------------------|
| 20 | 2²⁰ ≈ 1M | 16 MB |
| 25 | 2²⁵ ≈ 33M | 512 MB |
| 30 | 2³⁰ ≈ 1B | 16 GB |
| 35 | 2³⁵ ≈ 34B | 512 GB |
| 40 | 2⁴⁰ ≈ 1T | 16 TB |

**Practical Limit**: ~30 qubits for general circuits on standard hardware.

**Tensor Network Extension**: 50+ qubits for low-entanglement circuits.

**Implication**: At most ~30 "decision variables" per quantum subroutine,
far below Rource's 10K-100K+ entity requirements.

---

### Phase 56 References

- [LogosQ Paper](https://arxiv.org/abs/2512.23183)
- [LogosQ crates.io](https://crates.io/crates/logosq)
- [QuantRS2 GitHub](https://github.com/cool-japan/quantrs)
- [QuantRS2 Documentation](https://docs.rs/quantrs2)
- [QAOA Nature Paper](https://www.nature.com/articles/s41534-025-01082-1)
- [Spring Embedders Survey](https://arxiv.org/abs/1201.3011)

---

## Cutting-Edge WASM Optimization Techniques (Phase 57)

### Overview

This section documents cutting-edge Rust + WebAssembly optimization techniques for 2025-2026,
evaluating their applicability to Rource's deterministic rendering and physics simulation workloads.

**Source**: "Cutting-edge Rust + WebAssembly optimization techniques for 2025-2026"

### Techniques Evaluated

| Technique | Category | Expected Gain | Rource Status |
|-----------|----------|---------------|---------------|
| Relaxed-SIMD | Instruction | 15-30% | NOT APPLICABLE (determinism) |
| Morton-ordered structures | Spatial | 20-50% | MARGINALLY APPLICABLE |
| Structure-of-Arrays (SoA) | Memory | 20-200% | LOW PRIORITY |
| wasm-opt -O4 | Build | 10-40% | ALREADY EQUIVALENT |
| WebGPU subgroups | GPU | 30-50% | NOT APPLICABLE (browser support) |
| Dual Kawase blur | Rendering | 200-400% | NOT APPLICABLE (small kernel) |
| Hierarchical Z-buffer | Rendering | 50-200% | NOT APPLICABLE (2D only) |

---

### Relaxed-SIMD (+relaxed-simd)

**Specification**: WebAssembly Relaxed-SIMD (Phase 5, standardized)

**New Instructions**:
- `f32x4.relaxed_fma`: Fused multiply-add
- `f32x4.relaxed_reciprocal_sqrt`: Hardware rsqrt (~12 bits precision)
- `i8x16.relaxed_laneselect`: Branchless lane selection

**Enable Flag**:
```toml
# .cargo/config.toml
[target.wasm32-unknown-unknown]
rustflags = ["-C", "target-feature=+simd128,+relaxed-simd"]
```

**Critical Caveat**:

> "Relaxed-SIMD introduces non-deterministic behavior—identical inputs may produce
> slightly different outputs across hardware."

**Rource Assessment**: **NOT APPLICABLE**

Rource's software renderer requires 100% deterministic output:
- Fixed-point arithmetic (8.8, 16.16 formats)
- Compile-time lookup tables for sqrt, division
- Explicit rounding modes

Relaxed-SIMD would break the determinism guarantee that ensures reproducible
visualization output across all platforms.

---

### Morton-Ordered Linear Structures

**Concept**: Replace pointer-based trees with Morton-encoded sorted arrays.

**Morton (Z-order) Encoding**:
```rust
pub fn morton_encode_2d(x: u16, y: u16) -> u32 {
    fn spread(mut n: u32) -> u32 {
        n = (n | (n << 8)) & 0x00FF00FF;
        n = (n | (n << 4)) & 0x0F0F0F0F;
        n = (n | (n << 2)) & 0x33333333;
        (n | (n << 1)) & 0x55555555
    }
    spread(x as u32) | (spread(y as u32) << 1)
}
```

**Benefits**:
- Cache-friendly sequential access
- ~2× bandwidth reduction vs pointer chasing
- Simple binary search for queries

**Complexity**:
| Operation | QuadTree | Morton Linear |
|-----------|----------|---------------|
| Lookup | O(log n) | O(log n) |
| Range query | O(log n + k) | O(log n + k) |
| Insert | O(log n) | O(n) resort |
| Cache | Pointer chasing | Sequential |

**Rource Assessment**: **MARGINALLY APPLICABLE**

Current QuadTree is already O(log n). GPU spatial hash uses grid-based indexing
(conceptually similar to Morton). Marginal benefit for high refactoring cost.

---

### Structure-of-Arrays (SoA)

**Concept**: Separate Vec per field instead of Vec of structs.

**soa_derive Crate** (v0.14.0):
```rust
use soa_derive::StructOfArray;

#[derive(StructOfArray)]
pub struct Entity {
    pub position: [f32; 2],
    pub velocity: [f32; 2],
    pub color: [u8; 4],
    pub flags: u32,
}

// Physics only touches positions and velocities
fn update(entities: &mut EntityVec) {
    for (pos, vel) in soa_zip!(&mut entities, [mut position, velocity]) {
        pos[0] += vel[0];
        pos[1] += vel[1];
    }
}
```

**Benefits**:
- Cache-friendly field-selective iteration
- 1.2-4× speedup depending on access patterns
- Automatic with `soa_derive`

**Rource Assessment**: **LOW PRIORITY**

- FileNode has 16 fields; SoA would require major refactoring
- GPU physics already uses minimal `ComputeEntity` struct
- CPU physics is fallback only

---

### wasm-opt Configuration

**Research Recommendation**:
```toml
wasm-opt = ["-O4", "--flexible-inline-max-function-size", "4294967295"]
```

**Current Rource Configuration** (build-wasm.sh):
```bash
wasm-opt \
    --enable-simd \
    --enable-bulk-memory \
    -O3 --converge --low-memory-unused \
    -o output.wasm input.wasm
```

**Comparison**:
| Setting | Recommended | Rource Current |
|---------|-------------|----------------|
| Level | -O4 | -O3 --converge |
| Inlining | Unlimited | Default |
| Features | Basic | 5 flags enabled |

**Rource Assessment**: **ALREADY EQUIVALENT**

`-O3 --converge` iterates optimization passes until no further improvement,
achieving the same effect as `-O4`. Unlimited inlining would increase binary
size beyond the ~1MB gzipped target.

---

### WebGPU Subgroups

**Concept**: Intra-SIMD lane communication without shared memory barriers.

**WGSL Example**:
```wgsl
enable subgroups;

@compute @workgroup_size(64)
fn reduce_sum() {
    let sum = subgroupAdd(value);  // No barrier needed
}
```

**Browser Support**:
| Browser | subgroups | subgroupAdd |
|---------|-----------|-------------|
| Chrome 128+ | Yes | Chrome 134+ |
| Firefox | Development | No |
| Safari | Development | No |

**Rource Assessment**: **NOT APPLICABLE NOW**

Limited to Chrome. Would require maintaining dual code paths (subgroups + fallback).
Current Blelloch prefix sum with shared memory barriers works across all browsers.

**Future**: Revisit when Firefox and Safari ship subgroup support (estimated 2026+).

---

### Dual Kawase Blur

**Concept**: Pyramid-based blur with logarithmic pass scaling.

**Algorithm**:
1. Downsample with 5-tap Kawase filter (1 center + 4 corners)
2. Repeat N times for pyramid
3. Upsample with 9-tap tent filter
4. Accumulate results

**Complexity**:
| Blur Radius | Box Blur | Gaussian | Kawase |
|-------------|----------|----------|--------|
| 7 | O(n) × 2 | O(n) × 7 | O(n) × 4 |
| 35 | O(n) × 2 | O(n) × 35 | O(n) × 5 |
| 64+ | O(n) × 2 | O(n) × 64 | O(n) × 6 |

**Rource Assessment**: **NOT APPLICABLE**

Current bloom uses `radius: 2` (5-tap kernel). Sliding window box blur is already
O(n) independent of kernel size. Kawase advantage only manifests for large radii
(35+ pixels).

---

### Hierarchical Z-Buffer

**Concept**: Dual-layer depth tiles with coverage masks for occlusion culling.

**Intel Masked Occlusion Culling**:
```rust
struct HiZTile {
    z_max0: f32,  // Layer 0 furthest depth
    z_max1: f32,  // Layer 1 furthest depth
    mask: u32,    // Coverage mask
}
```

**Rource Assessment**: **NOT APPLICABLE**

Rource is a 2D visualization. No depth buffer, no Z-based occlusion.
2D visibility uses camera frustum culling and painter's algorithm (draw order).

---

### Key Findings

1. **Determinism Constraint**: Relaxed-SIMD's non-determinism conflicts with Rource's
   reproducible output guarantee

2. **Already Optimized**: wasm-opt, LTO, codegen-units, SIMD128 already at maximum

3. **Wrong Scale**: Kawase blur benefits large kernels (35+ pixels); Rource uses radius=2

4. **Wrong Dimension**: Hi-Z buffer is for 3D; Rource is 2D

5. **Browser Support**: WebGPU subgroups require Chrome 128+, no Firefox/Safari

### Phase 57 References

- [WebAssembly Relaxed-SIMD Proposal](https://github.com/WebAssembly/relaxed-simd)
- [Morton Codes (Z-order curve)](https://en.wikipedia.org/wiki/Z-order_curve)
- [soa_derive crate](https://docs.rs/soa_derive/latest/soa_derive/)
- [wasm-opt / Binaryen](https://github.com/WebAssembly/binaryen)
- [WebGPU Subgroups Specification](https://www.w3.org/TR/webgpu/#subgroups)
- [Dual Kawase Blur (Intel)](https://www.intel.com/content/www/us/en/developer/articles/technical/an-investigation-of-fast-real-time-gpu-based-image-blur-algorithms.html)
- [Masked Occlusion Culling](https://github.com/GameTechDev/MaskedOcclusionCulling)

---

## Applicability Framework

When evaluating theoretical algorithms for Rource, assess:

| Criterion | Question |
|-----------|----------|
| **Problem Match** | Does Rource solve this problem? |
| **Graph Structure** | What graphs does Rource operate on? |
| **Scale Relevance** | Does n in Rource reach where the algorithm shines? |
| **Constant Factors** | Are hidden constants practical? |
| **Implementation Complexity** | Is the engineering effort justified? |
| **WASM Compatibility** | Can it run in browsers? |

### Current Rource Graph Structures

| Structure | Type | SSSP Complexity | Current Algorithm |
|-----------|------|-----------------|-------------------|
| Directory Tree | Tree | O(n) trivial | BFS/DFS traversal |
| Commit History | Linear/DAG | O(n) trivial | Sequential iteration |
| Spatial Index | QuadTree | N/A (geometric) | O(log n) queries |
| Force Simulation | N-body | N/A (physics) | Barnes-Hut O(n log n) |

---

## Future Exploration Queue

Algorithms to explore for potential future applicability:

| Algorithm | Domain | Potential Use Case | Priority |
|-----------|--------|-------------------|----------|
| Loose QuadTree | Spatial | Reduced restructuring during layout | Low |
| Grid-based CPU spatial index | Spatial | Unify CPU/GPU approaches | Low |
| succinctly BitVec | Memory | Large repo WASM memory pressure | Low |
| Minimum spanning tree improvements | Graph theory | Dependency tree visualization | Low |
| Dynamic graph algorithms | Streaming graphs | Real-time commit monitoring | Medium |
| Parallel BFS/DFS | Graph traversal | Large repository initialization | Low |
| Approximate nearest neighbor | Spatial | Faster hover detection at scale | Low |

**Benchmarked and Deferred** (from Phase 55):

| Algorithm | Reason for Deferral |
|-----------|---------------------|
| vers-vecs | Not WASM-compatible (x86_64 intrinsics) |
| PGM-Index | Wrong access pattern (point queries, not range) |
| Grandchildren-WB Trees | Rource uses n-ary trees, not BSTs |
| UFO Trees | Requires WASM threads (limited support) |

**Quantum Algorithms Evaluated** (from Phase 56):

| Algorithm | Reason Not Applicable |
|-----------|----------------------|
| VQE | Domain mismatch (chemistry, not visualization) |
| QAOA | Variable type (discrete vs continuous positions) |
| Grover | O(√n) worse than O(1) hash, O(log n) tree |
| QFT | Small kernel blur already O(n) optimal |
| Quantum Annealing | Scale limit (~30 qubits vs 10K+ entities) |

**WASM Optimization Techniques Evaluated** (from Phase 57):

| Technique | Reason Not Applicable |
|-----------|----------------------|
| Relaxed-SIMD | Non-deterministic (conflicts with reproducible output) |
| Morton-ordered | Marginal benefit over existing QuadTree |
| SoA layout | High refactoring effort, GPU already optimized |
| wasm-opt -O4 | Already equivalent with -O3 --converge |
| WebGPU subgroups | Limited browser support (Chrome-only) |
| Kawase blur | Small kernel (radius=2) doesn't benefit |
| Hi-Z buffer | 2D rendering only |

---

## References

### Papers Analyzed

1. Duan et al. (2025) - "Breaking the Sorting Barrier for Directed Single-Source Shortest Paths"
   - arXiv:2504.17033v2
   - Status: Analyzed, not applicable (Phase 52)

2. Kakatkar (2025) - "Graph Coloring for Data Science: A Comprehensive Guide"
   - Towards Data Science, August 2025
   - Algorithms: Greedy, Welsh-Powell, DSatur, Chromatic Polynomials
   - Status: Analyzed, not applicable (Phase 53)
   - Key algorithms preserved for reference

3. Scientific American (2025) - "The 10 Biggest Math Breakthroughs of 2025"
   - December 19, 2025
   - Including: Moving Sofa (Baek), Noperthedron (Steininger/Yurkevich),
     Hilbert's 6th (Deng/Hani/Ma), Fibonacci Sticks (Treeby et al.)
   - Status: Analyzed, not directly applicable (Phase 54)
   - Conceptual insights preserved

4. Targeted Optimization Research Document (2026)
   - "Algorithmic Research for Rource: Targeted Optimizations"
   - Algorithms: GraphWaGu, GPU ForceAtlas2, Loose QuadTree, Geohash,
     vers-vecs, succinctly, PGM-Index, Grandchildren-WB Trees, UFO Trees
   - Status: Analyzed (Phase 55)
   - Finding: GPU pipeline already optimal; succinct structures potentially applicable
   - Future candidates: Loose QuadTree, Grid-based CPU index, succinctly BitVec

5. Quantum Algorithms Research Document (2026)
   - "Production-Ready Quantum Algorithms in Rust (2025)"
   - Algorithms: VQE, QAOA, Grover, QFT, Quantum Annealing
   - Libraries: LogosQ v0.2.5, QuantRS2 v0.1.0-rc.1
   - Status: Analyzed (Phase 56)
   - Finding: All algorithms NOT APPLICABLE due to:
     - Scale mismatch (~30 qubit limit vs 10K+ entities)
     - Variable type mismatch (discrete vs continuous)
     - Superior classical alternatives (O(1) hash, O(n) spatial hash)
   - Conceptual insights preserved for energy minimization framing

6. WASM Optimization Research Document (2026)
   - "Cutting-edge Rust + WebAssembly optimization techniques for 2025-2026"
   - Techniques: Relaxed-SIMD, Morton ordering, SoA, wasm-opt -O4, WebGPU subgroups,
     Kawase blur, Hierarchical Z-buffer
   - Status: Analyzed (Phase 57)
   - Finding: Most techniques NOT APPLICABLE due to:
     - Determinism conflicts (Relaxed-SIMD)
     - Already equivalent (wasm-opt configuration)
     - Wrong scale (Kawase for small kernels)
     - Wrong dimension (Hi-Z for 2D)
     - Browser support (WebGPU subgroups)
   - Marginally applicable: Morton ordering, SoA layout (low priority)

### Related Rource Documentation

- [Performance Documentation](./README.md) - Optimization history (59 phases)
- [ALGORITHMIC_COMPLEXITY.md](./ALGORITHMIC_COMPLEXITY.md) - Big-O analysis of existing code
- [CLAUDE.md](../../CLAUDE.md) - Development guidelines

---

*This document is maintained as part of Rource's commitment to algorithmic excellence and
mathematical rigor, even when exploring algorithms beyond current applicability.*
