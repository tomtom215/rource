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

---

## 2.4 Implementation

### Source Code

Located in: `crates/rource-core/src/physics/spatial.rs`

#### QuadTree Structure (lines 22-40)

```rust
#[derive(Debug, Clone)]
pub struct QuadTree<T: Clone> {
    /// The bounds of this node.
    bounds: Bounds,

    /// Items stored at this node.
    items: Vec<(Vec2, T)>,

    /// Child nodes (if subdivided).
    children: Option<Box<[Self; 4]>>,

    /// Maximum items before subdivision.
    max_items: usize,

    /// Maximum depth of the tree.
    max_depth: usize,

    /// Current depth of this node.
    depth: usize,
}
```

#### Insert with Subdivision (lines 116-134)

```rust
/// Inserts an item at the given position.
pub fn insert(&mut self, position: Vec2, item: T) {
    if !self.bounds.contains(position) {
        return;
    }

    // If we have children, delegate to the appropriate child
    if self.children.is_some() {
        self.insert_into_child(position, item);
        return;
    }

    // Store at this node
    self.items.push((position, item));

    // Subdivide if we exceed capacity and haven't reached max depth
    if self.items.len() > self.max_items && self.depth < self.max_depth {
        self.subdivide();
    }
}
```

#### Query with Bounds Intersection (lines 278-296)

```rust
/// Recursive query implementation.
fn query_recursive<'a>(&'a self, bounds: &Bounds, results: &mut Vec<&'a T>) {
    if !self.bounds.intersects(*bounds) {
        return;  // O(1) bounds check enables O(log n) traversal
    }

    // Check items at this node
    for (pos, item) in &self.items {
        if bounds.contains(*pos) {
            results.push(item);  // O(k) output
        }
    }

    // Check children
    if let Some(ref children) = self.children {
        for child in children.iter() {
            child.query_recursive(bounds, results);
        }
    }
}
```

#### Zero-Allocation Visitor Pattern (lines 252-275)

```rust
/// Queries items and calls a closure for each match (zero-allocation).
#[inline]
pub fn query_for_each(&self, bounds: &Bounds, mut visitor: impl FnMut(&T)) {
    self.query_for_each_recursive(bounds, &mut visitor);
}

fn query_for_each_recursive(&self, bounds: &Bounds, visitor: &mut impl FnMut(&T)) {
    if !self.bounds.intersects(*bounds) {
        return;
    }

    for (pos, item) in &self.items {
        if bounds.contains(*pos) {
            visitor(item);
        }
    }

    if let Some(ref children) = self.children {
        for child in children.iter() {
            child.query_for_each_recursive(bounds, visitor);
        }
    }
}
```

### Mathematical-Code Correspondence

| Theorem/Equation | Code Location | Line(s) | Verification |
|------------------|---------------|---------|--------------|
| Theorem 2.1: Query O(log n + k) | `query_recursive` | 278-296 | ✓ Bounds intersection prunes non-overlapping subtrees |
| Theorem 2.2: Insert O(log n) | `insert` | 116-134 | ✓ Single path to leaf, max depth bounded |
| Space O(n) | `items: Vec<(Vec2, T)>` | 27 | ✓ Each item stored once |
| MAX_ITEMS subdivision | `self.items.len() > self.max_items` | 131 | ✓ Triggers subdivision |
| Depth bound | `self.depth < self.max_depth` | 131 | ✓ Prevents infinite recursion |

### Verification Commands

```bash
# Run unit tests
cargo test -p rource-core quadtree --release -- --nocapture

# Run query tests
cargo test -p rource-core test_quadtree_query --release -- --nocapture

# Run all spatial tests
cargo test -p rource-core spatial --release -- --nocapture
```

### Validation Checklist

- [x] Code matches mathematical specification exactly
- [x] All theorems have corresponding code locations
- [x] Bounds intersection test is O(1)
- [x] Zero-allocation visitor pattern available
- [x] Subdivision triggered only when exceeding max_items

---

## References

- Samet, H. (1984). "The quadtree and related hierarchical data structures." *ACM Computing Surveys*, 16(2), 187-260.

---

*[Back to Index](./README.md)*
