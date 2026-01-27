# 9. Partial Selection Algorithm

**Implementation**: `rource-wasm/src/render_phases.rs`

**Category**: Algorithms

---

## 9.1 Problem Statement

Selecting the top k elements from n elements by priority. Full sorting takes O(n log n).

---

## 9.2 Theorem: O(n) Top-k Selection

**Claim**: `select_nth_unstable_by` achieves O(n) expected time for partial ordering.

**Proof**:

**Algorithm** (Introselect/Quickselect variant):

```rust
fn select_top_k(items: &mut [T], k: usize, cmp: impl Fn(&T, &T) -> Ordering) {
    items.select_nth_unstable_by(k, |a, b| cmp(b, a)); // Descending
    // items[0..k] now contains top k (unordered)
    // items[k] is the k-th largest
}
```

**Complexity Analysis**:

Quickselect partitions around a pivot:
- Elements < pivot go left
- Elements ≥ pivot go right

**Expected Comparisons**:
E[C(n, k)] = n + E[C(n/2, k')] where k' ≤ k

By Master Theorem: E[C(n, k)] = O(n)

**Worst Case**: O(n²) but Introselect switches to Heapselect after log n recursions, guaranteeing O(n) worst case.

**Application in Rource**:

```rust
// Select top 15 beams by importance
if beams.len() > 15 {
    beams.select_nth_unstable_by(15, |a, b|
        b.importance.partial_cmp(&a.importance).unwrap()
    );
    beams.truncate(15);
}
```

**Benchmark Validation** (Phase 65):
| Operation | O(n log n) Sort | O(n) Selection | Improvement |
|-----------|-----------------|----------------|-------------|
| 50 beams  | 892 ns          | 103 ns         | 8.6× faster |
| 30 labels | 617 ns          | 84 ns          | 7.3× faster |

∎

---

## References

- Musser, D. R. (1997). "Introspective Sorting and Selection Algorithms." *Software: Practice and Experience*, 27(8), 983-993.
- Hoare, C. A. R. (1961). "Algorithm 65: Find." *Communications of the ACM*, 4(7), 321-322.

---

*[Back to Index](./README.md)*
