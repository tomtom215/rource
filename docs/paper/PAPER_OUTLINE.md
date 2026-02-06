# Paper Outline: Triple-Verified

**Full Title**: Triple-Verified: Hybrid Formal Verification of a Production
Rust Math Library using Verus, Coq, and Kani

**Target Venue**: CPP 2027 (Certified Programs and Proofs)
**Page Limit**: ~20 pages (ACM format)

---

## Section Map

| Section | File | Status | Est. Pages |
|---------|------|--------|------------|
| Abstract | `ABSTRACT.md` | **Draft complete** | 0.5 |
| 1. Introduction | `INTRODUCTION.md` | **Draft complete** | 2.0 |
| 2. Background | `BACKGROUND.md` | **Draft complete** | 2.0 |
| 3. Architecture | `ARCHITECTURE.md` | **Draft complete** | 2.5 |
| 4. Methodology | `METHODOLOGY.md` | **Draft complete** | 3.5 |
| 5. Extraction | `EXTRACTION.md` | **Draft complete** | 1.5 |
| 6. Evaluation | `EVALUATION.md` | **Draft complete** | 2.0 |
| 7. Discussion (Threats) | `THREATS_TO_VALIDITY.md` | **Draft complete** | 2.0 |
| 8. Related Work | `RELATED_WORK.md` | **Draft complete** | 2.0 |
| 9. Conclusion | `CONCLUSION.md` | **Draft complete** | 0.5 |
| References | — | To compile | 1.0 |
| **Total** | | | **~17.5** |

## Supporting Documents

| Document | File | Status |
|----------|------|--------|
| Contributions | `CONTRIBUTIONS.md` | **Complete** |
| Spec-Impl Correspondence | `../verification/SPEC_IMPL_CORRESPONDENCE.md` | **Complete** |
| 10-Operation Audit | `TEN_OPERATION_AUDIT.md` | **Complete** |
| Mutation Testing | `MUTATION_TESTING.md` | **Complete** |

## Key Claims and Evidence

| Claim | Evidence File | Quantified? |
|-------|---------------|-------------|
| 2968 machine-checked theorems | `metrics/verification-counts.json` | Yes (automated count) |
| Zero admits | `grep -rn 'admit\|Admitted' proofs/` | Yes (verifiable) |
| 85.5% operation coverage | `VERIFICATION_COVERAGE.md` (219/256) | Yes |
| 4 IEEE 754 bugs | `VERIFICATION_COVERAGE.md:463-469` | Yes (concrete counterexamples) |
| >300x Coq compilation speedup | `METHODOLOGY.md` Section 4.2 | Yes (45s vs ~15min) |
| 6.8 KB WASM extraction | `WASM_EXTRACTION_PIPELINE.md` | Yes (measured) |
| 91.2% raw / 100% adjusted mutation score | `MUTATION_TESTING.md` | Yes (20 equivalent mutants) |
| 361 FP error bounds | `metrics/verification-counts.json` | Yes (automated count) |

## Figures Needed

| # | Figure | Section | Status |
|---|--------|---------|--------|
| 1 | Verification triangle (Verus/Coq/Kani) | 3.1 | TODO |
| 2 | Coq layer dependency DAG | 3.2 / 4.2 | TODO |
| 3 | Lemma decomposition call graph (mat3_mul_assoc) | 4.1 | TODO |
| 4 | Per-type coverage heatmap | 6.2 | TODO |
| 5 | Tool overlap Venn diagram | 6.4 | TODO |
| 6 | WASM extraction pipeline diagram | 5.1 | TODO |
| 7 | FP error bound example (dot product) | 4.4 | TODO |

## Tables in Paper

| # | Table | Section | Data Source |
|---|-------|---------|-------------|
| 1 | Compact comparison matrix (9 projects) | 8 | `RELATED_WORK.md` |
| 2 | Per-type verification coverage | 6.2 | `VERIFICATION_COVERAGE.md` |
| 3 | Per-tool theorem counts | 3.4 | `verification-counts.json` |
| 4 | Unverified operations breakdown | 6.2 | `VERIFICATION_COVERAGE.md` |
| 5 | Compilation time by tool | 6.3 | Measured |
| 6 | 4 IEEE 754 bugs | 4.3 | `VERIFICATION_COVERAGE.md` |
| 7 | Threats to validity summary | 7 | `THREATS_TO_VALIDITY.md` |
| 8 | WASM pipeline stages | 5.4 | `WASM_EXTRACTION_PIPELINE.md` |

## References (Preliminary)

### Core Tools
- [Lattuada+23] Verus, OOPSLA 2023
- [Coq Team 2024] The Coq Proof Assistant
- [Bae+24] Kani ICSE-SEIP 2024
- [Boldo+11] Flocq: IEEE 754 in Coq, JSC 2011

### Related Work
- [Erbsen+19] Fiat-Crypto, IEEE S&P 2019
- [Leroy09] CompCert, CACM 2009
- [mathlib20] Lean Mathematical Library, CPP 2020
- [Kellison+23] LAProof, IEEE ARITH 2023
- [Kellison+24] VCFloat2, CPP 2024
- [Gilot+26] Stainless FP, arXiv 2601.14059
- [Jung+18] RustBelt, POPL 2018
- [Gaher+24] RefinedRust, PLDI 2024
- [Bhargavan+24] hax, VSTTE 2024

### Supporting
- [Sozeau+24] MetaCoq Verified Extraction, PLDI 2024
- [Yang+24] AutoVerus, arXiv 2409.13082
- [IEEE 2019] IEEE 754-2019

## Next Steps (Priority Order)

1. **T5.1**: WASM extraction benchmarks (compare extracted vs production)
2. **T8**: Verify ~10 new methods (close coverage gap)
3. **T9**: Create reproducibility artifact (Dockerfile, scripts)
4. Compile all sections into single LaTeX document
5. Create figures (TikZ diagrams)
6. Format references (BibTeX)
7. Internal review and revision cycle

---

*Created: 2026-02-06*
*All section drafts complete. Ready for compilation into LaTeX.*
