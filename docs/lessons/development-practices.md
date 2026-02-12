# Lessons Learned: Development Practices

> Part of the [Lessons Learned Knowledge Base](README.md).
> Categories: Tool Installation, Shell Scripting, CI/Workflow, Documentation Automation, Documentation Auditing, Measurement & Honesty.
>
> New entries should also be added to the [Chronological Audit Log](chronological-log.md).

---

## Category: Tool Installation & Environment

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 6 | coq-of-rust incompatible with Rust 1.93 | Requires older nightly | Manual Coq specs instead |
| 8 | No automated Verus/Coq setup | Tools required manual installation | Created `scripts/setup-formal-verification.sh` |
| 9 | Coq installation via apt needs `coq-theories` | apt only installs `coqc` without theories | `apt-get install -y coq coq-theories` |
| 11 | Network issues can block apt-get | Transient DNS failures | Retry with exponential backoff |
| 32 | MetaCoq blocked by Coq opam repo HTTP 503 | Repository infra intermittently unavailable | Try alternative sources or GitHub pins |
| 34 | MetaCoq buildable from source despite opam 503 | All opam repos return 503 | Clone from GitHub, pin coq-equations from source |
| 35 | coq-equations pinnable from GitHub source | opam pin bypasses broken infra | `opam pin add coq-equations "git+https://github.com/mattam82/Coq-Equations.git#v1.3-8.18"` |
| 36 | MetaCoq coq-8.18 branch != MetaRocq/rocq-verified-extraction | rocq-verified-extraction requires 8.19+ | Use `MetaCoq/metacoq#coq-8.18` |
| 38 | `libgmp-dev` required for zarith/MetaCoq build | zarith needs GMP dev headers | `apt-get install -y libgmp-dev` |
| 39 | Coq renamed to Rocq Prover (v9.0, March 2025) | Official rebranding | Stay on Coq 8.18; migrate to Rocq 9.x later |
| 40 | Both Coq AND Rocq opam repos return HTTP 503 | Infrastructure issue | Use `opam.ocaml.org` + GitHub pins |
| 41 | MetaCoq → MetaRocq rename (v1.4 for Rocq 9.0) | Namespace change | Coq 8.18: MetaCoq branch. Rocq 9.x: MetaRocq |
| 42 | rocq-core 9.1.0 available on opam.ocaml.org | Default opam repo has Rocq | `opam pin add rocq-prover 9.0.0` works |
| 43 | MetaRocq 1.4.1 is latest (Dec 2024, Rocq 9.1) | GitHub releases per Rocq target | Check releases page for version compat |
| 44 | MetaCoq built from source bypasses opam 503 | 8 components build in ~30 min | Build order: utils→common→template-coq→pcuic→template-pcuic→safechecker→erasure→erasure-plugin |
| 45 | apt Coq vs opam Coq .vo file inconsistency | .vo compiled with different Coq installations incompatible | `rm -f *.vo *.vos *.vok *.glob` then recompile with `eval $(opam env)` |
| 46 | `make install` for MetaCoq takes ~15-20 min | Builds quotation theories | Budget time; monitor with verbose output |
| 47 | Recompilation order matters for Coq .vo files | Layer dependencies: specs → proofs → compute → extraction | Always recompile in order |
| 48 | `verify_coq_proofs()` has 4 layers | Each depends on prior; MetaCoq layer optional | Layer 4 is not a failure if unavailable |
| 73 | `RUSTUP_TOOLCHAIN=nightly-2024-12-07` for rocq-of-rust | Uses rustc internals | Set env var + `LD_LIBRARY_PATH` |

---

## Category: Shell Scripting & Automation

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 37 | Setup scripts must pass shellcheck | Subtle bugs in shell scripts | `bash -n` + `shellcheck --severity=info` before commit |
| 101 | GNU sed only supports POSIX ERE | `(?!...)`, `(?=...)`, `\b` not available | Never use Perl-style features; use context anchoring |
| 102 | `local` keyword only valid inside bash functions | `local VAR=...` at top-level is error | Use plain `VAR=...` outside functions |
| 103 | Context-aware sed patterns prevent cross-contamination | Generic `s/[0-9]+/NEW/` matches wrong numbers | Use line-context anchors with unique surrounding text |
| 104 | Idempotency verification essential | Double-run may corrupt if patterns match own output | Test: `./script.sh && ./script.sh && ./script.sh --check` |
| 111 | Per-file sed patterns scale linearly but are necessary | 23 patterns for SETUP_GUIDE.md | No shortcuts; generic patterns cause cross-contamination |

---

## Category: CI / Workflow Configuration

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 7 | Windows CI benchmark timeout | Threshold too tight for CI variability | Increased threshold 100µs→150µs |
| 105 | Cargo package names differ from directory names | `rource-cli/` has package name `rource` | Check `Cargo.toml` `[package] name`; `-p` uses package name |
| 129 | `cargo bench --workspace` fails with `--noplot` | Binary targets use default harness, not criterion | Add `--benches` flag: `cargo bench --workspace --benches -- --noplot` |
| 130 | Mutation testing timeout too low for CI | Complex mutants need >60s on CI runners | Default timeout 60s→120s in `mutation.yml` |
| 131 | Feature-gated modules skip clippy unless `--all-features` | `cache` module behind `#[cfg(feature = "cache")]` | Always run `cargo clippy --all-targets --all-features -- -D warnings` |
| 132 | Display format hex vs decimal causes cross-platform test failure | `CacheError::RepositoryMismatch` formats `{:016x}` | Test assertions must match actual Display format, not assumed format |
| 133 | Docker Trivy scanning 138 OS-level CVEs from `debian:trixie-slim` | `runtime-with-git` pulls git + transitive deps (openldap, pam, ncurses, curl, etc.) | Switch default Docker target to `runtime-distroless` (cc-debian13); git stage opt-in |
| 134 | NEVER dismiss security alerts as "pre-existing" or "base image issue" | Assumption that alerts auto-resolve proved wrong | Fix root cause: minimize attack surface; never assume issues resolve themselves |
| 137 | Docker glibc version mismatch: build vs runtime | Builder on Trixie (glibc 2.39) + distroless cc-debian12 (glibc 2.36) = `GLIBC_2.39 not found` | All stages must use same Debian generation; upgrade distroless to cc-debian13 |
| 200 | `coq-flocq` not found: "No package named coq-flocq found" after `opam install` | `coq-flocq` is NOT in the default opam.ocaml.org repository; it requires the Coq released opam repo (`coq.inria.fr/opam/released`) which returns HTTP 503 | Cascading fallback: try HTTPS endpoints, then clone GitHub mirror (`github.com/coq/opam` → `released/` directory) as local opam repo |

---

## Category: Documentation & Metrics Automation

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 106 | Rounded display strings resist minor fluctuations | "2700+" stays valid across small changes | Rounded form + `+` suffix for display; exact in JSON |
| 107 | Peripheral docs need same automation as primary docs | SETUP_GUIDE.md, etc. had stale counts | Automation must cover ALL files with metrics |
| 108 | Documentation drift inevitable without CI enforcement | Counts go stale within a single session | CI must enforce `--check` mode on both scripts |
| 109 | Two-tier script architecture for doc automation | Verification counts vs other metrics need different extraction | `update-verification-counts.sh` + `update-doc-metrics.sh` |
| 110 | Ground truth must come from source files | Hardcoded counts go stale immediately | Parse actual source: `grep -cE` patterns |
| 140 | Sed patterns with hardcoded old counts become stale | Script used `**446 theorems**` literal | Use `[0-9]+` patterns for numbers; never hardcode previous values |
| 145 | README.md sed patterns must match actual Markdown table format | Expected `N theorems, 0 admits | Machine-checked` vs actual `N theorems | Zero admits` | Row-anchored: `/Coq \(R-based\)/s/[0-9]+ theorems/$N theorems/` |
| 146 | WASM_EXTRACTION_PIPELINE.md had no update rule in script | File with Coq counts was created without script entry | When creating doc files with metrics, ALWAYS add sed patterns to update script |
| 147 | CLAUDE.md per-type verification table needs automated updates | Per-type Bounds/Utils rows went stale | Added per-type row patterns to `update-verification-counts.sh` |
| 184 | New FP Coq files require 3-place script update | Script needs: count variable, TOTAL formula update, JSON output entry | Checklist: `COQ_FP_<TYPE>=$(count_coq ...)`, add to `COQ_FP_TOTAL`, add to JSON `coq_fp` block |

---

## Category: Measurement & Intellectual Honesty

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 1 | Timing variations reported as perf improvements | Module refactoring doesn't affect binary | Added "Invalid Performance Claims" table |
| 2 | "10% is noise" at picosecond scale | Wrong precision assumptions | "Measurement Precision at Scale" section |
| 3 | Low coverage blamed on tarpaulin | Excuse instead of investigation | Added `--engine Llvm` requirement |
| 55 | **STANDARDS VIOLATION**: Coq proofs committed without machine-checking | Coq was not installed | NEVER commit proofs without `coqc`. Install tools FIRST. |

---

## Category: Documentation Content Auditing

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 233 | Non-existent CLI flags documented in TROUBLESHOOTING.md (7+ flags) | Docs written speculatively without verifying `args/mod.rs` | Always grep `rource-cli/src/args/` for any CLI flag referenced in docs |
| 234 | Wrong WASM API method names in RUNBOOK.md (8+ methods) | Names guessed from conventions instead of checked against `wasm_api/` | Always grep `rource-wasm/src/wasm_api/` and `lib.rs` for `#[wasm_bindgen]` exports |
| 235 | JS API constructor `new Rource(canvas)` never existed — factory is `await Rource.create(canvas)` | Docs assumed constructor pattern; actual API uses async factory | Verify JS API against `rource-wasm/src/lib.rs` `create()` method |
| 236 | Renderer trait signatures wrong in ARCHITECTURE.md and RENDERING.md | Documented from memory instead of source; missing `width` param on `draw_circle`, missing `draw_disc` | Always read `crates/rource-render/src/lib.rs` `pub trait Renderer` for authoritative signatures |
| 237 | Backend selection order wrong in RENDERING.md (said WebGL2 first; actual is wgpu first) | Documented assumption contradicted by `Rource::create()` in `lib.rs` | Check `rource-wasm/src/lib.rs` `create()` for actual initialization sequence |
| 238 | `getRendererType()` return strings documented as PascalCase but are lowercase | Convention assumed; actual strings are `"wgpu"`, `"webgl2"`, `"software"` | Check `get_renderer_type()` in `wasm_api/rendering.rs` for exact return values |
| 239 | ADR 0004 (generation counter) accepted but pattern never implemented | Decision documented but LabelPlacer uses `Vec::clear()` not generation counters | Audit ADRs against actual implementation; mark as Superseded when pattern differs |
| 240 | CONTRIBUTING.md JS directory tree had 12 entries but actual directory has 30+ files | Tree written once and never updated as files were added | Verify directory trees with `find` or `ls -R` before documenting |
| 241 | GOURCE_COMPARISON.md listed 3 features as "roadmap" that were already implemented | Feature status not updated when implementation completed | Cross-reference feature claims with `grep` in source before marking status |
| 242 | `getMetrics()` referenced in TELEMETRY.md but actual method is `getFrameStats()` | API renamed but docs not updated | Use `grep -r 'wasm_bindgen' rource-wasm/src/` to find actual exported names |
| 243 | Broken link in docs/README.md (`performance/FORMAL_PROOFS.md` → `performance/formal-proofs/README.md`) | Path changed but cross-reference not updated | Run link checker (`grep -oP` + file existence check) before committing doc changes |
| 244 | Verification proof counts drifted from source (Vec2 Verus: 55→61, Color Verus: 57→64, Coq-Z totals: 417→471) | Phase 1 metrics update missed per-file granular counts in VERUS_PROOFS.md and COQ_PROOFS.md | Automation scripts must cover ALL files containing per-type/per-file counts, not just summary totals |
| 245 | Subagent audit results must be verified before applying | Agent reported `getDetailedFrameStats` as non-existent but it exists at `lib.rs:1042` | Always cross-check agent-reported violations against source before editing |
| 246 | Files with most violations: TROUBLESHOOTING.md (7+), RUNBOOK.md (8+), RENDERING.md (5+), ARCHITECTURE.md (5+) | These files describe implementation details that change frequently | Prioritize these files in future audits; consider automation for API-referencing docs |
| 259 | Verus uses `proof fn` keyword, NOT `#[verifier::proof]` attribute | ARCHITECTURE.md had deprecated syntax | Always verify tool syntax against actual proof files |
| 260 | FP_Common.v uses named constants `prec32`/`emin32`/`fexp32`, not inline `binary32 := FLT_exp (-149) 24` | Paper simplified beyond accuracy | Diff code snippets against actual `.v` files |
| 261 | Kani proofs directory (`kani_proofs/`, 10 files), not single file `kani_proofs.rs` | Module refactored from file to directory | Update all grep/counting commands after refactors |
| 262 | ALL 8 Coq Record field names wrong in SPEC_IMPL_CORRESPONDENCE.md | Written from memory, never verified | ALWAYS read actual `.v` Record definitions |
| 263 | Utils.v MUST compile before Vec2.v, Vec3.v, Vec4.v | `Require Import RourceMath.Utils` dependency chain | Verify compilation order with `grep 'Require Import'` |
| 264 | Per-file Z-compute breakdown stale: Vec2(62→76), Rect(51→79); sum was 429, not claimed 471 | Per-file counts not updated | Cross-check per-file breakdowns SUM to claimed total |
| 265 | RENDERING_BOTTLENECK_ANALYSIS.md stale code snippet (Phase 70 changes not reflected) | Optimization applied but doc not updated | Re-verify before/after snippets after each optimization phase |
| 266 | BENCHMARKS.md test count "2,076" severely stale (actual 2964) | Snapshot never updated | Use rounded display strings or automate |
| 267 | File paths missing `crates/` prefix in 2 BENCHMARKS.md references | Shorthand without repo-root prefix | ALWAYS use full path from repo root |
| 292 | Triple-nested `Vec` spatial hash: 3 pointer dereferences per cell access at nanosecond scale | Cache misses dominate when data structures have deep indirection | Flatten multi-level `Vec<Vec<Vec<T>>>` to single `Vec<Vec<T>>` with arithmetic indexing |
| 293 | Generation counter branch in tight inner loop (~160 iterations/frame) | Branch prediction failures at nanosecond scale add up | Replace generation-based invalidation with dirty-cell tracking for branch-free inner loops |
| 294 | Browser timer resolution (~5 µs) causes dt aliasing at >2K FPS | Frame time approaches timer quantization, creating alternating 0/2× dt | Use simulation time accumulator with minimum step threshold (1/480 Hz) |
| 295 | Per-entry `(usize, u32)` wastes 50% on generation tags when dirty-cell tracking is used | Metadata per entry redundant if container-level tracking ensures freshness | Strip metadata from hot-path data; use container-level tracking for invalidation |

---

*Part of the [Lessons Learned Knowledge Base](README.md) | [Chronological Log](chronological-log.md) | [Formal Verification](formal-verification.md)*
