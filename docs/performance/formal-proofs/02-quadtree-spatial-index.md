# 2. QuadTree Spatial Index

**Implementation**: `crates/rource-core/src/physics/spatial.rs`

**Category**: Spatial Data Structures

---

## 2.1 Theorem: Query Complexity

**Claim**: Range query on a QuadTree with n items returns k items in O(log n + k) time for a query region of fixed size.

**Proof**:

Let Q be the query rectangle.

**Tree Traversal**:
1. At each node, check if Q intersects node bounds: O(1)
2. If intersection, visit children (up to 4)

**Nodes Visited**: For query rectangle of fixed size A:
- At depth d, nodes have area D²/4^d
- Q intersects at most O(A × 4^d / D²) = O(4^d × A/D²) nodes at depth d
- For small A/D², this is O(1) at each level
- Total nodes visited: O(log n)

**Item Examination**: Each visited node may have up to MAX_ITEMS items.
- Only items within Q are returned: k items
- Work: O(k)

**Total**: O(log n + k). ∎

---

## 2.2 Theorem: Insert Complexity

**Claim**: Inserting an item into a QuadTree with n items takes O(log n) time.

**Proof**:

1. **Traversal**: Find correct leaf by checking which quadrant contains point.
   - Each level: O(1) comparison
   - Max depth: O(log n)
   - Total traversal: O(log n)

2. **Subdivision**: If leaf exceeds MAX_ITEMS:
   - Create 4 children: O(1)
   - Redistribute items: O(MAX_ITEMS) = O(1)
   - Subdivisions cascade at most O(log n) times

**Total**: O(log n). ∎

---

## 2.3 Space Complexity

**Claim**: A QuadTree with n items uses O(n) space.

**Proof**:

- Each item stored exactly once: O(n)
- Each node has O(1) metadata
- Maximum nodes: At most 4n (each item can cause one subdivision)
- But typically: O(n/MAX_ITEMS) = O(n/16) = O(n) nodes

**Total Space**: O(n). ∎

---

## References

- Samet, H. (1984). "The quadtree and related hierarchical data structures." *ACM Computing Surveys*, 16(2), 187-260.

---

*[Back to Index](./README.md)*
