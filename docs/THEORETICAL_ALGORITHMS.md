# Theoretical Algorithms Reference

**Purpose**: This document catalogs advanced algorithmic research at the theoretical edge of mathematics
that may inform future Rource development. These algorithms represent the state-of-the-art in their
respective domains but may not have direct applicability to Rource's current architecture.

**Philosophy**: Even when an algorithm doesn't directly apply, understanding its techniques can inspire
optimization strategies and inform architectural decisions.

**Last Updated**: 2026-01-25 (Phase 54 added)

---

## Table of Contents

1. [SSSP: Breaking the Sorting Barrier](#sssp-breaking-the-sorting-barrier)
2. [Graph Coloring Algorithms](#graph-coloring-algorithms)
3. [2025 Mathematical Breakthroughs](#2025-mathematical-breakthroughs)
4. [Applicability Framework](#applicability-framework)
5. [Future Exploration Queue](#future-exploration-queue)

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
| Minimum spanning tree improvements | Graph theory | Dependency tree visualization | Low |
| Dynamic graph algorithms | Streaming graphs | Real-time commit monitoring | Medium |
| Parallel BFS/DFS | Graph traversal | Large repository initialization | Low |
| Approximate nearest neighbor | Spatial | Faster hover detection at scale | Low |

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

### Related Rource Documentation

- [PERFORMANCE.md](../PERFORMANCE.md) - Optimization history
- [ALGORITHMIC_COMPLEXITY.md](./ALGORITHMIC_COMPLEXITY.md) - Big-O analysis of existing code
- [CLAUDE.md](../CLAUDE.md) - Development guidelines

---

*This document is maintained as part of Rource's commitment to algorithmic excellence and
mathematical rigor, even when exploring algorithms beyond current applicability.*
