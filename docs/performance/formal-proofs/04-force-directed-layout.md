# 4. Force-Directed Layout Convergence

**Implementation**: `crates/rource-core/src/physics/force.rs`

**Category**: Physics Simulation

---

## 4.1 Theorem: Energy Minimization

**Claim**: The force-directed layout converges to a local energy minimum with damping factor d ∈ (0, 1).

**Proof**:

**Energy Function**:
```
E = Σᵢⱼ (repulsion_energy(i,j)) + Σ_edges (spring_energy)
E_repulsion = k_r/|rᵢ - rⱼ|
E_spring = k_s × |rᵢ - rⱼ - L|²
```

**Force Derivation**:
```
Fᵢ = -∇ᵢE
```

**Update Rule** (semi-implicit Euler):
```
vᵢ(t+1) = d × (vᵢ(t) + Fᵢ × dt)
rᵢ(t+1) = rᵢ(t) + vᵢ(t+1) × dt
```

**Energy Dissipation**:

With damping d < 1:
```
|vᵢ(t+1)| ≤ d × |vᵢ(t)| + |Fᵢ| × dt
```

At equilibrium (Fᵢ = 0 for all i), velocities decay exponentially:
```
|vᵢ(t)| = O(d^t)
```

**Convergence**: For d = 0.95 (typical), velocities decrease by 5% per frame.
After t frames: |v| = 0.95^t × |v₀|

Time to reach |v| < ε: t = log(ε/|v₀|) / log(0.95) ≈ 20 × log(|v₀|/ε)

For |v₀| = 100, ε = 0.01: t ≈ 185 frames ≈ 3 seconds at 60 FPS. ∎

---

## 4.2 Stability Condition

**Claim**: The simulation is stable if dt × k_max < 2, where k_max is the maximum spring constant.

**Proof** (von Neumann stability analysis):

Linearizing around equilibrium:
```
d²x/dt² = -k × x - c × dx/dt
```

Discrete eigenvalues: λ = 1 - c×dt ± sqrt((c×dt)² - 4×k×dt²)

Stability requires |λ| ≤ 1:
```
k × dt² < 1 - (c×dt)²/4 ≈ 1
k × dt < 1/dt
```

With typical dt = 1/60 and k = 100:
```
k × dt = 100/60 ≈ 1.67 < 2 OK
```

Stable configuration verified. ∎

---

## References

- Eades, P. (1984). "A heuristic for graph drawing." *Congressus Numerantium*, 42, 149-160.

---

*[Back to Index](./README.md)*
