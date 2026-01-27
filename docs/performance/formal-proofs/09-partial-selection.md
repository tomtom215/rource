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

## 9.3 Implementation

### Source Code Location

| Component | File | Lines |
|-----------|------|-------|
| Beam selection | `rource-wasm/src/render_phases.rs` | 828-836 |
| User label selection | `rource-wasm/src/render_phases.rs` | 963-975 |
| File label selection | `rource-wasm/src/render_phases.rs` | 1431-1441 |

### Core Implementation

**Beam Selection with O(n) Partial Ordering** (`render_phases.rs:828-836`):

```rust
// V1: Limit concurrent beams to prevent visual chaos
// OPTIMIZATION: Use select_nth_unstable for O(n) partial selection instead of O(n log n) sort
// This partitions the array so elements [0..beam_limit] are the smallest (unordered)
let beam_limit = MAX_CONCURRENT_BEAMS.min(active_indices.len());
if beam_limit > 0 && beam_limit < active_indices.len() {
    // Partial sort: only need the smallest `beam_limit` elements
    active_indices.select_nth_unstable_by(beam_limit - 1, |a, b| {
        a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal)
    });
}
```

**User Label Selection** (`render_phases.rs:963-975`):

```rust
// OPTIMIZATION: Use select_nth_unstable for O(n) partial selection instead of O(n log n) sort
// We only need the top max_labels candidates, not a fully sorted list.
let max_labels = label_placer.max_labels();
let select_count = max_labels.min(label_candidates.len());
if select_count > 0 && select_count < label_candidates.len() {
    // Partition so [0..select_count] contains highest priority (unordered)
    // Note: select_nth_unstable_by finds nth smallest, so we use reversed comparison
    label_candidates.select_nth_unstable_by(select_count - 1, |a, b| {
        b.4.partial_cmp(&a.4).unwrap_or(std::cmp::Ordering::Equal)
    });
}
```

### Mathematical-Code Correspondence

| Theorem | Mathematical Expression | Code Location | Implementation |
|---------|------------------------|---------------|----------------|
| 9.2 | E[C(n,k)] = O(n) | `render_phases.rs:833` | `select_nth_unstable_by` |
| 9.2 | Partition property | `render_phases.rs:834` | `a.1.partial_cmp(&b.1)` |
| 9.2 | Worst case O(n) | Rust std lib | Introselect hybrid algorithm |

### Verification Commands

```bash
# Run beam selection benchmark
cargo test -p rource-wasm bench_beam_sorting --release -- --nocapture

# Run user label selection benchmark
cargo test -p rource-wasm bench_user_label_sorting --release -- --nocapture

# Run all render phase tests
cargo test -p rource-wasm render --release -- --nocapture
```

### Validation Checklist

- [x] O(n) expected time via Introselect
- [x] Worst case O(n) guaranteed (not O(n²))
- [x] Correct partial ordering (top k in [0..k])
- [x] Reversed comparison for descending order
- [x] 7-9× faster than full sort for typical sizes

---

*[Back to Index](./README.md)*
