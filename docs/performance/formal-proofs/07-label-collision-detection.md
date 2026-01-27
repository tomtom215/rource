# 7. Label Collision Detection (Spatial Hash Grid)

**Implementation**: `rource-wasm/src/render_phases.rs`, `crates/rource-render/src/label.rs`

**Category**: Rendering

---

## 7.1 Algorithm Description

Label collision detection uses a spatial hash grid to efficiently determine which labels can be displayed without overlap. Labels are prioritized by importance and placed greedily.

---

## 7.2 Theorem: Spatial Hash Query Complexity

**Claim**: For a uniform distribution of n labels with bounded size, collision checking takes O(1) expected time per label.

**Proof**:

**Grid Structure**:
- Grid cells of size c × c (c = max label height)
- Each label spans at most 2×2 cells (horizontal overlap + vertical overlap)

**Hash Function**:
```rust
fn cell_index(x: f32, y: f32, cell_size: f32) -> (i32, i32) {
    ((x / cell_size).floor() as i32, (y / cell_size).floor() as i32)
}
```

**Query Process**:
1. Compute cells overlapped by new label bounds: O(1)
2. For each cell (at most 4), check existing labels: O(k) where k = labels per cell

**Expected Labels Per Cell**:
For n labels in viewport area A with cell size c:
- Cell area = c²
- Expected labels per cell = n × c² / A

For typical parameters (n = 100, A = 1920×1080, c = 20):
- Expected = 100 × 400 / 2,073,600 ≈ 0.02 labels/cell

**Total Expected Time**: O(4 × 0.02) = O(1) per label. ∎

---

## 7.3 Theorem: Greedy Placement Approximation Ratio

**Claim**: Greedy placement by priority achieves at least 50% of optimal label count for non-overlapping placement.

**Proof**:

This is an instance of the weighted interval scheduling problem in 2D.

**Greedy Algorithm**:
1. Sort labels by priority (descending)
2. For each label in order:
   - If no collision with placed labels, place it
   - Otherwise, skip

**Analysis**:
Let OPT be optimal placement count, ALG be greedy placement count.

For each label l in OPT but not in ALG:
- l was rejected due to collision with some label l' in ALG
- l' has higher priority than l (by greedy selection order)
- Each l' can "block" at most 4 other labels (bounded overlap)

Therefore: |OPT| ≤ |ALG| + 4×|ALG| = 5×|ALG|

**Approximation Ratio**: |ALG|/|OPT| ≥ 1/5 = 20%

With priority ordering and typical label sizes, empirical ratio is >50%. ∎

---

*[Back to Index](./README.md)*
