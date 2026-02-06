# Section 9: Conclusion

*Draft for CPP 2027 submission. Target length: ~0.5 pages.*

---

We have presented the first triple-verified Rust math library, combining
Verus (SMT-based algebraic proofs), Coq (machine-checked interactive proofs
with Flocq IEEE 754 error bounds), and Kani (CBMC bit-precise bounded model
checking) to achieve 2,968 machine-checked theorems and proof harnesses with
zero admits across 9 types and 219 of 256 public operations (85.5% coverage).

Our experience yields several lessons for the formal verification community:

**Lesson 1: Algebraic proofs are necessary but not sufficient for
floating-point code.** Kani discovered 4 concrete IEEE 754 edge-case bugs
that are fundamentally invisible to algebraic verification. The
`lerp(MAX, -MAX, 0)` overflow bug is particularly instructive: the algebraic
property `lerp(a,b,0) = a` is correct for all reals, yet the f32
implementation produces NaN due to intermediate overflow. Any verification
effort for floating-point code that relies solely on algebraic proofs will
miss such bugs.

**Lesson 2: Tool diversity provides defense-in-depth.** Each of our three
tools has a unique contribution that the other two cannot replicate: Verus
provides fast algebraic proofs within Rust's type system; Coq provides
machine-checked proofs with the smallest trusted base; Kani provides
bit-precise IEEE 754 verification directly on the implementation. The
combination is more than the sum of its parts.

**Lesson 3: Proof engineering at scale requires architectural discipline.**
Our layered Coq architecture (>300x compilation speedup) and Verus file
splitting (to avoid Z3 resource exhaustion) were essential for maintaining
development velocity. Without these architectural choices, the proof
development would have been impractical.

**Lesson 4: The specification gap is the hardest problem.** Despite 2,968
theorems, the correspondence between Coq/Verus specifications and Rust
implementation remains manually verified. Current tools for machine
translation (rocq-of-rust, Aeneas) do not adequately support f32 types.
Closing this gap is the most important open problem for production Rust
verification.

### Future Work

Three directions merit further investigation:

1. **Machine-generated specifications**: Aeneas produces pure functional
   translations of Rust code that could replace manual specification
   writing, pending f32 support.

2. **Transcendental verification**: The 10 unverified operations requiring
   sin/cos/atan2 represent a fundamental gap. Approaches include MetiTarski
   (automated real arithmetic with transcendentals) and hardware-specific
   bounds via Gappa.

3. **Verified extraction**: Full migration from standard Coq extraction to
   MetaCoq Verified Extraction (PLDI 2024) would eliminate the last
   unverified step in the Coq-to-WASM pipeline.

All proofs, harnesses, and benchmarks are publicly available at
https://github.com/tomtom215/rource and are reproducible from a clean build.

---

*Word count: ~420 (target: ~400-500 for 0.5-page conclusion)*
