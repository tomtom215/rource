# Theoretical Algorithms Reference

**Purpose**: This document catalogs advanced algorithmic research at the theoretical edge of mathematics
that may inform future Rource development. These algorithms represent the state-of-the-art in their
respective domains but may not have direct applicability to Rource's current architecture.

**Philosophy**: Even when an algorithm doesn't directly apply, understanding its techniques can inspire
optimization strategies and inform architectural decisions.

**Last Updated**: 2026-01-25

---

## Table of Contents

1. [SSSP: Breaking the Sorting Barrier](#sssp-breaking-the-sorting-barrier)
2. [Applicability Framework](#applicability-framework)
3. [Future Exploration Queue](#future-exploration-queue)

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
   - Status: Analyzed, not applicable

### Related Rource Documentation

- [PERFORMANCE.md](../PERFORMANCE.md) - Optimization history
- [ALGORITHMIC_COMPLEXITY.md](./ALGORITHMIC_COMPLEXITY.md) - Big-O analysis of existing code
- [CLAUDE.md](../CLAUDE.md) - Development guidelines

---

*This document is maintained as part of Rource's commitment to algorithmic excellence and
mathematical rigor, even when exploring algorithms beyond current applicability.*
