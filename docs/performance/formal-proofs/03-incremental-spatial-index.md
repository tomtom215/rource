# 3. Incremental Spatial Index Maintenance

**Implementation**: `crates/rource-core/src/scene/spatial_methods.rs`

**Category**: Spatial Data Structures

---

## 3.1 Theorem: Incremental Update Advantage

**Claim**: For k entity position changes per frame out of n total entities, incremental maintenance achieves O(k log n) vs O(n log n) full rebuild.

**Proof**:

**Full Rebuild**:
- Clear tree: O(1)
- Insert all n entities: n × O(log n) = O(n log n)

**Incremental Update**:
- Remove k changed entities: k × O(log n)
- Re-insert k changed entities: k × O(log n)
- Total: O(k log n)

**Speedup Ratio**: n/k

**Practical Impact** (n = 10,000, k = 100):
- Full rebuild: ~130,000 operations
- Incremental: ~1,300 operations
- Speedup: **100x**. ∎

---

## 3.2 Implementation Strategy

Current implementation uses throttled full rebuild every 5 frames for simplicity. Incremental updates are a planned optimization for Phase 61.

**Trade-off Analysis**:

| Approach | Complexity | Cache Locality | Implementation |
|----------|-----------|----------------|----------------|
| Full Rebuild | O(n log n) | Excellent | Simple |
| Incremental | O(k log n) | Good | Complex (tombstones) |
| Hybrid (throttled) | O(n log n / 5) | Excellent | Simple |

---

*[Back to Index](./README.md)*
