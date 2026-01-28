# CLAUDE.md - Rource Project Guide

This document provides context and guidance for Claude (AI assistant) when working on the Rource project.

---

## Table of Contents

1. [Expert+ Excellence Standard](#expert-excellence-standard)
2. [Performance Scale and Precision](#performance-scale-and-precision)
3. [Core Operating Principles](#core-operating-principles)
4. [Quality Domains](#quality-domains)
5. [Project Overview](#project-overview)
6. [Quick Start](#quick-start)
7. [Architecture](#architecture)
8. [Development Guidelines](#development-guidelines)
9. [Performance Optimization Standards](#performance-optimization-standards)
10. [UI/UX Excellence Standards](#uiux-excellence-standards)
11. [Testing & Quality Standards](#testing--quality-standards)
12. [Security Standards](#security-standards)
13. [Accessibility Standards](#accessibility-standards)
14. [Documentation Standards](#documentation-standards)
15. [Common Tasks](#common-tasks)
16. [CI/CD Pipeline](#cicd-pipeline)
17. [Debugging](#debugging)
18. [Dependencies Philosophy](#dependencies-philosophy)
19. [Git Workflow](#git-workflow)
20. [Troubleshooting](#troubleshooting)
21. [Reference Links](#reference-links)
22. [Roadmap Documents](#roadmap-documents)
23. [Session Best Practices](#session-best-practices)

---

## Expert+ Excellence Standard

### THE MANDATE

**This project is a professional portfolio showpiece and publicly deployed WASM demo.** Every single contribution—every line of code, every UI element, every test, every document—MUST meet **Expert+ level excellence** with **zero compromises**.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                     EXPERT+ EXCELLENCE STANDARD                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  This standard applies to EVERY session, EVERY commit, EVERY change.        │
│                                                                             │
│  There are NO exceptions. There are NO shortcuts. There is NO "good enough."│
│                                                                             │
│  If it cannot be measured, it did not happen.                               │
│  If it was not tested, it does not work.                                    │
│  If it was not documented, it does not exist.                               │
│  If it was not benchmarked BEFORE and AFTER, it is speculation.             │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Target Ratings

Every domain must achieve and maintain **Expert+ (10/10)** rating:

| Domain | Current | Target | Tracking Document |
|--------|---------|--------|-------------------|
| Technical Excellence | Expert | Expert+ | `docs/performance/CHRONOLOGY.md` |
| Performance Engineering | Expert+ | Expert+ | `docs/performance/BENCHMARKS.md` |
| UI/UX Design | 3/10 | Expert+ | `docs/ux/MOBILE_UX_ROADMAP.md` |
| Testing Maturity | Senior+ | Expert+ | `docs/performance/FUTURE_WORK.md` |
| Security Posture | Senior | Expert+ | `docs/performance/FUTURE_WORK.md` |
| Accessibility | Not Rated | Expert+ | `docs/ux/MOBILE_UX_ROADMAP.md` |
| Operational Readiness | Senior+ | Expert+ | `docs/performance/FUTURE_WORK.md` |
| Documentation Quality | Expert | Expert+ | This document |

### The Non-Negotiable Rules

| Rule | Requirement | Consequence of Violation |
|------|-------------|--------------------------|
| **Never Assume** | Verify every claim with data | Work is invalid |
| **Never Guess** | Base all decisions on measurements | Work is invalid |
| **Never Skip Tests** | Run full test suite before claiming success | Work is invalid |
| **Never Ship Broken UX** | Mobile-first, touch-first, accessible | Work is invalid |
| **Never Commit Undocumented** | Every change documented with metrics | Work is invalid |
| **Never Ignore Warnings** | Zero clippy warnings, zero console errors | Work is invalid |
| **Never Approximate** | "~50%" is wrong; "52.5% (2.41µs → 1.15µs)" is correct | Work is invalid |

---

## Core Operating Principles

### The Standard

| Principle | Requirement |
|-----------|-------------|
| **Never Assume** | Verify every claim with data. If unsure, investigate first. |
| **Never Guess** | Base all decisions on measurements, not intuition. |
| **Always Test** | Run the full test suite before claiming success. |
| **Always Measure** | Use criterion benchmarks with statistical significance. |
| **Always Verify** | Confirm results are reproducible across runs. |
| **Always Validate** | Cross-check implementations against requirements. |
| **Always Document** | Every change needs before/after measurements in docs. |
| **Always Review** | Check mobile UX, accessibility, and user impact. |

### Precision Requirements

We operate at **nanosecond to picosecond precision** for performance and **pixel-perfect precision** for UI:

| Domain | Precision Level | Example |
|--------|-----------------|---------|
| **Performance** | Picoseconds-Nanoseconds | Draw call: 360 ps ± 6.8 ps |
| **Touch Targets** | Exact pixels | Minimum 44×44px (no exceptions) |
| **Typography** | Exact pixels | Minimum 12px body, 4.5:1 contrast |
| **Layout** | Percentage of viewport | Visualization: 85%+ during playback |
| **Animation** | Milliseconds | 16.67ms frame budget at 60 FPS |

### Anti-Patterns to Avoid

| Anti-Pattern | Why It's Wrong | Correct Approach |
|--------------|----------------|------------------|
| "This should be faster" | Speculation | Benchmark before and after |
| "~50% improvement" | Approximation | "52.5% improvement (2.41µs → 1.15µs)" |
| "Looks fine on my screen" | Single device | Test on mobile Safari, Chrome, Firefox |
| "Users will figure it out" | Assumption | Icons need labels, gestures need hints |
| "I'll document it later" | Never happens | Document as you implement |
| "The tests pass" | Insufficient | Also check mobile UX, accessibility |
| "It works on desktop" | Desktop bias | Mobile-first development required |
| **"Pre-existing issue"** | **Abdication of responsibility** | **Fix it NOW** |
| **"Unrelated to my changes"** | **Destroys trust and quality** | **You touched it, you own it** |

### CRITICAL: The "Pre-Existing Issue" Fallacy

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    **  ABSOLUTE PROHIBITION  **                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  NEVER dismiss ANY issue as "pre-existing" or "unrelated to my changes."   │
│                                                                             │
│  This behavior is ABSOLUTELY UNACCEPTABLE and represents:                   │
│                                                                             │
│  - A fundamental violation of Expert+ standards                             │
│  - An abdication of professional responsibility                             │
│  - A betrayal of trust with the project owner                               │
│  - A threat to the integrity of the entire codebase                         │
│  - Potential hidden bugs that will surface in production                    │
│                                                                             │
│  The correct response to ANY warning, error, or issue is:                   │
│                                                                             │
│  1. FIX IT IMMEDIATELY                                                      │
│  2. If you cannot fix it, DOCUMENT why and create a tracking issue          │
│  3. NEVER proceed with other work until the codebase is clean               │
│                                                                             │
│  Remember: This is a PORTFOLIO SHOWPIECE and PUBLIC WASM DEMO.              │
│  Every clippy warning, every test failure, every console error              │
│  reflects directly on the quality of the project and its author.            │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

**The Rule**: If you encounter ANY issue during your work session—whether you caused it or not—you are responsible for fixing it. There is no "not my problem." There is no "out of scope." If clippy reports 20 warnings, you fix 20 warnings. If tests fail, you fix the tests. Period.

**Why This Matters**:
1. **Hidden bugs accumulate**: "Pre-existing" issues often mask real bugs
2. **Trust erosion**: Dismissing issues signals you don't care about quality
3. **Technical debt compounds**: Every ignored warning makes the next one easier to ignore
4. **Portfolio damage**: A single clippy warning in a public demo undermines credibility
5. **Production risk**: Warnings today become crashes tomorrow

---

## Intellectual Honesty Standards

### The Honesty Mandate

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    ABSOLUTE INTELLECTUAL HONESTY                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  NEVER guess. NEVER assume. NEVER exaggerate. NEVER overstate.              │
│  NEVER skim. NEVER compromise. NEVER take shortcuts with truth.             │
│                                                                             │
│  Every claim must be:                                                       │
│    • VERIFIABLE - Can be independently reproduced                           │
│    • AUDITABLE - Evidence exists and is documented                          │
│    • PRECISE - Exact values, not approximations                             │
│    • HONEST - Acknowledges limitations and uncertainty                      │
│                                                                             │
│  When uncertain, say "I don't know" or "This needs verification."           │
│  When wrong, immediately correct and document the error.                    │
│  When results are inconclusive, say so explicitly.                          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### What Constitutes a Valid Performance Claim

| Claim Type | Required Evidence | Invalid Without |
|------------|-------------------|-----------------|
| **"X% faster"** | Criterion benchmark, 100+ samples, 95% CI, before/after | Statistical significance test |
| **"No regression"** | Same benchmark methodology, threshold-based pass/fail | Defined acceptance thresholds |
| **"Optimization"** | Algorithmic/data structure change + measured improvement | Actual code change that affects runtime |
| **"Improvement"** | Quantified metric with baseline comparison | Reproducible measurement |

### Invalid Performance Claims

The following are **NEVER** valid performance claims:

| Invalid Claim | Why It's Wrong | Correct Approach |
|---------------|----------------|------------------|
| "Module refactoring improved performance" | Module organization doesn't affect compiled binary | "Module refactoring improved maintainability; verified no regression" |
| "~X% improvement" | Approximation violates precision standards | "X.XX% improvement (before: Y, after: Z)" |
| "Should be faster" | Speculation, not measurement | Benchmark before claiming |
| "Feels faster" | Subjective, unmeasurable | Use objective metrics |
| "Minor improvement" | Vague, unquantified | Provide exact numbers |
| Timing variations without statistical analysis | Measurement requires rigor | Use criterion: 100+ samples, 95% CI, reproducible |

### Measurement Precision at Scale

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    PRECISION AT PICOSECOND SCALE                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  At our frame budget of 20µs (target: <10µs), EVERY PERCENT MATTERS:        │
│                                                                             │
│    • 10% of 20µs = 2µs = 6,000 CPU cycles = NOT NOISE                       │
│    • 5% of 20µs = 1µs = 3,000 CPU cycles = SIGNIFICANT                      │
│    • 1% of 20µs = 200ns = 600 CPU cycles = MEASURABLE                       │
│                                                                             │
│  We are measuring INDIVIDUAL CPU CLOCK CYCLES. There is no such thing       │
│  as "acceptable noise" at this precision level. Timing variations that      │
│  would be noise in millisecond-scale applications are REAL COSTS here.      │
│                                                                             │
│  Sources of variance (NOT noise - actual measurement considerations):       │
│    • CPU frequency scaling: Control with `cpupower frequency-set`           │
│    • Cache state: Warm up with 100+ samples before measuring                │
│    • System load: Use dedicated test environment, minimize processes        │
│    • Memory allocation: Pre-allocate, avoid measurement-time allocs         │
│    • Kernel scheduling: Use real-time priority, isolate CPU cores           │
│                                                                             │
│  To establish statistical confidence:                                       │
│    1. Use criterion with 100+ samples (statistical rigor)                   │
│    2. Verify 95% confidence intervals don't overlap                         │
│    3. Report exact values: "52.3% improvement" not "~50%"                   │
│    4. Run multiple independent benchmark sessions                           │
│    5. Control for variance sources listed above                             │
│                                                                             │
│  If criterion reports "No change" - report exactly that.                    │
│  If criterion reports a change - verify it's reproducible, then report it.  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Code Quality vs. Performance

**Code quality changes** (refactoring, module organization, documentation) should be:
- Documented as code quality improvements, NOT performance improvements
- Verified to cause no regression (threshold-based pass/fail)
- Not claimed as optimizations (the binary is identical)

**Performance changes** (algorithmic improvements, data structure changes) should be:
- Documented with criterion benchmarks (100+ samples, 95% CI)
- Include before/after measurements with exact values
- Calculate exact improvement percentages
- Verify statistical significance

### Self-Correction Protocol

When an error in reporting is discovered:

1. **Immediately acknowledge** the error explicitly
2. **Correct the documentation** with accurate information
3. **Explain** what was wrong and why
4. **Prevent recurrence** by strengthening standards if needed
5. **Do not minimize** or make excuses

Example of proper self-correction:
> "I incorrectly reported timing variations as performance improvements.
> Module refactoring does not affect compiled binary; observed timing
> differences were measurement artifacts within noise margin. The correct
> claim is: verified no regression against defined thresholds."

### Self-Improvement Protocol

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    ITERATIVE EXCELLENCE IMPROVEMENT                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  When ANY EXPERT+ violation occurs, this document MUST be updated:          │
│                                                                             │
│  1. IDENTIFY the violation class                                            │
│     └─ Performance claim without evidence                                   │
│     └─ Approximation instead of exact measurement                           │
│     └─ Overstated or exaggerated results                                    │
│     └─ Skipped verification step                                            │
│     └─ Incorrect precision assumptions                                      │
│                                                                             │
│  2. DOCUMENT the specific error                                             │
│     └─ What was claimed vs. what was true                                   │
│     └─ Why the error occurred (root cause)                                  │
│     └─ What damage could have resulted                                      │
│                                                                             │
│  3. ADD PREVENTIVE GUIDANCE to CLAUDE.md                                    │
│     └─ New rule, checklist item, or warning                                 │
│     └─ Specific enough to prevent recurrence                                │
│     └─ Placed in the relevant section                                       │
│                                                                             │
│  4. UPDATE the Lessons Learned log (below)                                  │
│     └─ Date, violation type, correction made                                │
│                                                                             │
│  This creates an iterative, self-improving system that tightens             │
│  tolerances with each session. The goal: ZERO EXPERT+ violations.           │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### Lessons Learned Log

| Date | Violation | Root Cause | Correction Added |
|------|-----------|------------|------------------|
| 2026-01-28 | Reported timing variations as performance improvements | Module refactoring doesn't affect compiled binary | Added "Invalid Performance Claims" table; clarified code quality vs performance |
| 2026-01-28 | Stated "10% is noise" at picosecond precision | Incorrect understanding of scale | Replaced "Noise Margin Rule" with "Measurement Precision at Scale" showing 10% = 6,000 CPU cycles |

---

## Performance Scale and Precision

### The 50,000 FPS Target

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    CRITICAL: FRAME BUDGET CONSTRAINT                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Target FPS:     50,000 FPS (theoretical maximum on test hardware)          │
│  Frame Budget:   20 microseconds (20,000 nanoseconds) MAXIMUM               │
│                                                                             │
│  At this scale:                                                             │
│    • 1 microsecond = 5% of frame budget                                     │
│    • 100 nanoseconds = 0.5% of frame budget                                 │
│    • 10 nanoseconds = 0.05% of frame budget                                 │
│    • 1 nanosecond = 0.005% of frame budget                                  │
│                                                                             │
│  Every nanosecond matters. Every CPU cycle counts.                          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### CPU Clock Cycle Reference

On a 3.0 GHz CPU (typical test hardware):

| Duration | Clock Cycles | Significance |
|----------|--------------|--------------|
| 1 picosecond | 0.003 cycles | Sub-instruction timing |
| 1 nanosecond | 3 cycles | Single instruction |
| 10 nanoseconds | 30 cycles | L1 cache access |
| 100 nanoseconds | 300 cycles | L2 cache access |
| 1 microsecond | 3,000 cycles | Complex operation |
| 10 microseconds | 30,000 cycles | Half frame budget |
| 20 microseconds | 60,000 cycles | **FULL FRAME BUDGET** |

### Measurement Precision Requirements

| Measurement | Precision Required | Example |
|-------------|-------------------|---------|
| Per-operation timing | Picoseconds | Draw call: 360 ps ± 6.8 ps |
| Per-label timing | Nanoseconds | Label placement: 88.9 ns |
| Per-frame timing | Microseconds | Full frame: 18.4 µs |
| Improvement claims | Exact percentage | 52.3% improvement (not "~50%") |

### The Absolute Rule

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  NEVER guess about performance. NEVER assume an optimization helps.         │
│  NEVER overstate improvements. NEVER approximate measurements.              │
│                                                                             │
│  The ONLY acceptable evidence is:                                           │
│                                                                             │
│  1. BEFORE benchmark (criterion, 100+ samples, 95% CI)                      │
│  2. AFTER benchmark (same methodology, same conditions)                     │
│  3. EXACT improvement calculation with measured values                      │
│  4. Statistical significance verification                                   │
│                                                                             │
│  If you cannot measure it, you cannot claim it.                             │
│  If you did not benchmark BEFORE changes, the change is speculation.        │
│  If the improvement is not statistically significant, it did not happen.    │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Current Performance Status

| Metric | Current | Target | Status |
|--------|---------|--------|--------|
| Frame time | ~18-23 µs | <20 µs | Near target |
| Optimization phases | 79 | Ongoing | Active |
| Algorithms evaluated | 79+ | Comprehensive | See ALGORITHM_CANDIDATES.md |

---

## Quality Domains

### Domain 1: Performance Engineering (Expert+)

**Standard**: Picosecond-to-nanosecond optimization with mathematical proof

| Criterion | Requirement |
|-----------|-------------|
| Benchmarks | Criterion with 100+ samples, 95% CI |
| Documentation | Before/after in CHRONOLOGY.md, BENCHMARKS.md |
| Complexity | Big-O analysis with scaling verification |
| Proof | Mathematical proof for complexity claims |
| Precision | Picosecond/nanosecond measurements |
| Frame Budget | Total render time < 20 µs |

**Reference**: `docs/performance/CHRONOLOGY.md` (79 phases)

---

### Domain 2: UI/UX Excellence (Target: Expert+)

**Standard**: Mobile-first, touch-first, user-centric design

| Criterion | Requirement |
|-----------|-------------|
| Touch targets | 44×44px minimum (Apple HIG) |
| Typography | 12px minimum, 4.5:1 contrast ratio (WCAG AA) |
| Layout | 85%+ viewport for primary content during use |
| Labels | All icons must have text labels or tooltips |
| Feedback | Every action has visible/haptic feedback |
| Progressive disclosure | Show less, reveal more on demand |
| Mobile testing | Test on real iOS Safari before merge |

**Reference**: `docs/ux/MOBILE_UX_ROADMAP.md` (46 issues tracked)

**Critical Mobile UX Rules**:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    MOBILE UX REQUIREMENTS                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. TOUCH TARGETS: Every interactive element ≥ 44×44px                  │
│     └─ Buttons, links, sliders, toggles, pills, icons                   │
│                                                                         │
│  2. TYPOGRAPHY: Minimum 12px, prefer 14-16px for body text              │
│     └─ Contrast ratio ≥ 4.5:1 for all text                              │
│     └─ No overlapping labels (collision detection required)             │
│                                                                         │
│  3. LAYOUT: Primary content takes 80%+ of viewport                      │
│     └─ Stats/chrome collapsible or auto-hide during use                 │
│     └─ Safe areas respected (notch, Dynamic Island, home indicator)     │
│                                                                         │
│  4. ICONS: Must have labels OR long-press tooltips                      │
│     └─ Mystery meat navigation is FORBIDDEN                             │
│                                                                         │
│  5. INFORMATION: Progressive disclosure, not information dump           │
│     └─ Developer metrics hidden by default                              │
│     └─ User-centric language, no jargon                                 │
│                                                                         │
│  6. GESTURES: Swipe-to-dismiss, pinch-to-zoom, pan supported            │
│     └─ First-time gesture hints for discoverability                     │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

### Domain 3: Testing Maturity (Target: Expert+)

**Standard**: Comprehensive testing with mutation analysis

| Criterion | Requirement |
|-----------|-------------|
| Unit tests | All public functions tested |
| Property tests | Mathematical invariants verified |
| Mutation testing | 80%+ mutation score for critical crates |
| Visual regression | Golden image comparison for rendering |
| Cross-browser | Chrome, Firefox, Safari, Edge |
| Load testing | 100k commits, 30 minutes, <5% memory growth |

**Reference**: `docs/performance/FUTURE_WORK.md` (TST-1 through TST-4)

---

### Domain 4: Security Posture (Target: Expert+)

**Standard**: Quantified security with supply chain transparency

| Criterion | Requirement |
|-----------|-------------|
| Fuzzing | Quantified coverage (75%+ edge coverage) |
| SBOM | Generated with every release |
| Audits | Weekly `cargo audit`, zero known vulnerabilities |
| Unsafe | Minimal, documented, justified |
| Dependencies | Audited, minimal, justified |

**Reference**: `docs/performance/FUTURE_WORK.md` (SEC-1 through SEC-4)

---

### Domain 5: Accessibility (Target: Expert+)

**Standard**: WCAG 2.1 AA compliance

| Criterion | Requirement |
|-----------|-------------|
| Keyboard | Full navigation without mouse |
| Screen reader | VoiceOver/TalkBack compatible |
| Contrast | 4.5:1 minimum for text, 3:1 for UI elements |
| Focus | Visible focus indicators |
| Motion | Reduced motion support |
| Touch | 44×44px targets, no hover-only interactions |

**Reference**: `docs/ux/MOBILE_UX_ROADMAP.md` (ACC-1 through ACC-5)

---

### Domain 6: Operational Readiness (Target: Expert+)

**Standard**: Production-grade telemetry and SLOs

| Criterion | Requirement |
|-----------|-------------|
| Telemetry | Tracing spans in hot paths |
| Metrics | P50/P99/P99.9 latency documented |
| Load testing | 30-minute stability test |
| Memory | Budget documented, growth <5% |
| Error tracking | Categorized, measured, alerted |

**Reference**: `docs/performance/FUTURE_WORK.md` (OP-1 through OP-5)

---

### Domain 7: Documentation Quality (Target: Expert+)

**Standard**: Complete, accurate, actionable documentation

| Criterion | Requirement |
|-----------|-------------|
| API stability | STABILITY.md with semver policy |
| Architecture | ADRs for key decisions |
| Runbooks | Operational playbooks |
| Performance | Before/after measurements always |
| UI/UX | Screenshots, issue tracking |

**Reference**: `docs/performance/FUTURE_WORK.md` (DOC-1 through DOC-3)

---

## Project Overview

**Rource** (Rust + Gource) is a complete rewrite of [Gource](https://github.com/acaudwell/Gource), the software version control visualization tool, in Rust with WebAssembly support.

### Goals

| Goal             | Description                                               |
|------------------|-----------------------------------------------------------|
| **Portable**     | Run on any CPU architecture without requiring a dedicated GPU |
| **Lightweight**  | Minimal dependencies, small binary size (~3.8MB native, ~1MB WASM gzip) |
| **Fast**         | Leverage Rust's performance and modern rendering techniques |
| **User-friendly**| Better UI/UX than original Gource (Expert+ mobile experience) |
| **Feature-complete** | Maintain at minimum feature parity with Gource        |
| **Accessible**   | WCAG 2.1 AA compliant, keyboard navigable                 |

### Key Documents

| Document | Purpose |
|----------|---------|
| `README.md` | Project overview and usage |
| `CONTRIBUTING.md` | Development guidelines |
| `docs/REVIEW_STANDARDS.md` | Code review requirements |
| `STABILITY.md` | API stability policy |
| `SECURITY.md` | Security policy |
| `docs/performance/CHRONOLOGY.md` | Optimization history (77 phases) |
| `docs/performance/BENCHMARKS.md` | Raw benchmark data |
| `docs/performance/NOT_APPLICABLE.md` | Algorithms evaluated as N/A |
| `docs/performance/ALGORITHM_CANDIDATES.md` | Future optimization candidates |
| `docs/performance/SUCCESSFUL_OPTIMIZATIONS.md` | Implemented optimizations catalog |
| `docs/performance/FUTURE_WORK.md` | Expert+ technical roadmap |
| `docs/ux/MOBILE_UX_ROADMAP.md` | Expert+ UI/UX roadmap |
| `LICENSE` | GPL-3.0 license |

---

## Quick Start

### Session Setup

Before starting development, run the setup script:

```bash
source scripts/session-setup.sh
```

### Session Checklist

**Before ANY work begins, verify**:

```bash
# 1. Tests pass
cargo test

# 2. No warnings
cargo clippy -- -D warnings

# 3. Formatted
cargo fmt --check

# 4. Read the roadmaps to understand current priorities
cat docs/performance/FUTURE_WORK.md
cat docs/ux/MOBILE_UX_ROADMAP.md
```

### Required Tools

| Tool | Version | Purpose |
|------|---------|---------|
| Rust | 1.93+ | Core language |
| Cargo | Latest | Package manager |
| wasm-pack | 0.12+ | WASM bundling |
| rustup | Latest | Toolchain management |

### Running the Project

```bash
# Windowed mode (interactive)
cargo run --release -- .

# Headless mode (batch export)
cargo run --release -- --headless --output /tmp/frames --seconds-per-day 0.5 .
```

---

## Architecture

### Crate Structure

```
rource/
├── crates/
│   ├── rource-math/       # Math types (Vec2, Vec3, Vec4, Mat3, Mat4, Color)
│   ├── rource-vcs/        # VCS log parsing (Git, SVN, Custom, Mercurial, Bazaar)
│   ├── rource-core/       # Core engine (scene, physics, animation, camera, config)
│   └── rource-render/     # Rendering (software, WebGL2, wgpu, bloom, shadows)
├── rource-cli/            # Native CLI application (winit + softbuffer)
└── rource-wasm/           # WebAssembly application
```

**Test Count**: 2,100+ tests total across all crates.

### Rendering Backends

| Backend | Platform | Description |
|---------|----------|-------------|
| wgpu | Native + WASM | Cross-platform GPU via WebGPU/Vulkan/Metal/DX12 |
| WebGL2 | WASM | GPU-accelerated browser rendering (fallback) |
| Software | All | Pure CPU rendering, maximum compatibility |

### CLI and WASM Rendering Synchronization

**The CLI and WASM have separate rendering code that must be kept in sync.**

When making visual/rendering changes:
1. **BENCHMARK BASELINE FIRST** - Run `cargo test -p rource-wasm bench_ --release -- --nocapture`
2. Update `rource-cli/src/rendering.rs` for native CLI
3. **Also update** `rource-wasm/src/lib.rs` and `rource-wasm/src/render_phases.rs` with same changes
4. Update `crates/rource-render/src/label.rs` if label-related changes
5. **BENCHMARK AFTER** - Compare with baseline, verify < 5% regression
6. Rebuild WASM with `./scripts/build-wasm.sh`
7. Test both CLI and WASM to verify visual parity
8. **Test on mobile Safari** to verify mobile UX
9. Document benchmark results in commit message

---

## Development Guidelines

### The Development Workflow

Every change MUST follow this workflow:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    EXPERT+ DEVELOPMENT WORKFLOW                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. UNDERSTAND                                                          │
│     └─ Read relevant roadmap docs (FUTURE_WORK.md, MOBILE_UX_ROADMAP.md)│
│     └─ Understand the current state and target state                    │
│     └─ Identify success criteria BEFORE starting                        │
│                                                                         │
│  2. MEASURE BASELINE (if applicable)                                    │
│     └─ Performance: Create criterion benchmarks                         │
│     └─ UI/UX: Screenshot current state on mobile                        │
│     └─ Tests: Note current coverage/mutation score                      │
│                                                                         │
│  3. IMPLEMENT                                                           │
│     └─ Make targeted, minimal changes                                   │
│     └─ Follow all domain-specific standards                             │
│     └─ Add tests for new functionality                                  │
│                                                                         │
│  4. VERIFY CORRECTNESS                                                  │
│     └─ cargo test (all 2,100+ tests pass)                               │
│     └─ cargo clippy -- -D warnings (zero warnings)                      │
│     └─ cargo fmt --check (formatted)                                    │
│     └─ Mobile Safari test (if UI change)                                │
│                                                                         │
│  5. MEASURE IMPROVEMENT                                                 │
│     └─ Performance: Run same benchmarks, calculate exact improvement    │
│     └─ UI/UX: Screenshot new state, compare                             │
│     └─ Tests: Verify coverage maintained/improved                       │
│                                                                         │
│  6. DOCUMENT                                                            │
│     └─ Performance: CHRONOLOGY.md, BENCHMARKS.md                        │
│     └─ UI/UX: Update MOBILE_UX_ROADMAP.md status                        │
│     └─ Update relevant roadmap documents                                │
│                                                                         │
│  7. COMMIT                                                              │
│     └─ Clear message with metrics and impact                            │
│     └─ Reference issue/task IDs                                         │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Code Style

- Use `cargo fmt` before committing
- Run `cargo clippy -- -D warnings` and fix ALL warnings
- Follow Rust API guidelines: https://rust-lang.github.io/api-guidelines/

### Building

```bash
# Debug build (native)
cargo build

# Release build (native)
cargo build --release

# WASM build
wasm-pack build --target web --release
```

### Testing

```bash
# Run all tests
cargo test

# Run specific crate tests
cargo test -p rource-core

# Run with output
cargo test -- --nocapture
```

---

## Performance Optimization Standards

### The Optimization Workflow

Every optimization MUST follow this exact process:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    OPTIMIZATION WORKFLOW                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. IDENTIFY                                                            │
│     └─ Profile, grep for patterns, analyze algorithmic complexity       │
│                                                                         │
│  2. BENCHMARK BASELINE                                                  │
│     └─ Create criterion benchmark BEFORE any changes                    │
│     └─ Record exact measurements with statistical significance          │
│     └─ Test multiple input sizes to verify complexity                   │
│                                                                         │
│  3. IMPLEMENT                                                           │
│     └─ Make targeted, minimal changes                                   │
│     └─ Add comments explaining the optimization                         │
│     └─ Preserve all existing behavior                                   │
│                                                                         │
│  4. VERIFY CORRECTNESS                                                  │
│     └─ Run ALL tests: cargo test                                        │
│     └─ Run clippy: cargo clippy -- -D warnings                          │
│     └─ Run rustfmt: cargo fmt --check                                   │
│                                                                         │
│  5. BENCHMARK OPTIMIZED                                                 │
│     └─ Run same benchmarks as step 2                                    │
│     └─ Calculate exact improvement percentages                          │
│     └─ Verify scaling behavior matches theoretical complexity           │
│                                                                         │
│  6. DOCUMENT                                                            │
│     └─ CHRONOLOGY.md: Full phase documentation                          │
│     └─ BENCHMARKS.md: Raw data tables                                   │
│     └─ SUCCESSFUL_OPTIMIZATIONS.md: Summary entry                       │
│                                                                         │
│  7. COMMIT                                                              │
│     └─ Clear message with phase number and key metrics                  │
│     └─ Include improvement percentages in commit body                   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Quality Bar

| Criterion | Requirement |
|-----------|-------------|
| **Measurable** | Backed by criterion benchmarks with statistical significance |
| **Documented** | Added to ALL THREE docs/performance/ files |
| **Correct** | All 2,100+ tests must pass |
| **Clean** | Clippy and rustfmt compliant |
| **Verifiable** | Benchmarks can be re-run to reproduce results |
| **Mathematical** | Include complexity analysis and/or mathematical proof |

### Statistical Rigor Requirements

All benchmark claims must include:

1. **Sample size**: Minimum 100 samples (criterion default)
2. **Confidence interval**: 95% CI reported
3. **Multiple input sizes**: Test scaling behavior (e.g., 50, 100, 200, 300, 500)
4. **Throughput metrics**: Elements/second where applicable
5. **Outlier analysis**: Report and explain outliers
6. **Reproducibility**: Same results on repeated runs

Example of proper benchmark reporting:

```
Instance Population (criterion, 100 samples, 95% CI):

| Avatar Count | Per-Texture | Texture Array | Improvement |
|--------------|-------------|---------------|-------------|
| 50           | 586.38 ns   | 300.28 ns     | -48.8%      |
| 100          | 1.1552 µs   | 564.60 ns     | -51.1%      |
| 300          | 3.9438 µs   | 1.7219 µs     | -56.3%      |

Mathematical Proof:
- Per-texture: T(n) = 1.06n ns (linear regression, R² ≈ 0.999)
- Texture array: T(n) = 360 ps ± 6.8 ps (constant)
- Complexity: O(n) → O(1) verified
```

### Current Optimization History

See `docs/performance/CHRONOLOGY.md` for complete history (77 phases).

### MANDATORY: Benchmark Before Committing Performance-Sensitive Code

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    CRITICAL: NEVER ASSUME, ALWAYS BENCHMARK                  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ANY change to the following code paths REQUIRES A/B benchmarking           │
│  BEFORE committing:                                                         │
│                                                                             │
│  • Label rendering (LabelPlacer, try_place, collision detection)            │
│  • Rendering loops (render_files, render_users, render_actions)             │
│  • Spatial data structures (grids, hashes, trees)                           │
│  • Per-frame operations (reset, update, draw calls)                         │
│  • Hot paths in rource-render, rource-wasm/render_phases.rs                 │
│  • Any code with "optimization", "performance", or "LOD" in comments        │
│                                                                             │
│  Even "simple" changes like adding 4 comparisons can have unexpected        │
│  impacts due to: cache effects, branch prediction, struct size changes,     │
│  compiler optimization differences, or memory layout changes.               │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

**A/B Benchmarking Protocol**:

```bash
# 1. BEFORE making changes, run baseline benchmarks
cargo test -p rource-wasm bench_ --release -- --nocapture

# 2. Record baseline numbers (copy/paste output)

# 3. Make your changes

# 4. Run SAME benchmarks again
cargo test -p rource-wasm bench_ --release -- --nocapture

# 5. Compare results - regression threshold is 5%
#    If regression > 5%, investigate before committing

# 6. For proper A/B comparison, use git checkout:
git stash
git checkout HEAD~1 -- <files>   # Baseline
cargo test -p rource-wasm bench_<name> --release -- --nocapture
git checkout HEAD -- <files>      # With changes
cargo test -p rource-wasm bench_<name> --release -- --nocapture
git stash pop
```

**Available Benchmarks**:

| Benchmark | What It Measures | Location |
|-----------|------------------|----------|
| `bench_label_placer_new` | LabelPlacer creation cost | render_phases/tests/benchmark_tests.rs |
| `bench_label_placer_reset` | Per-frame reset cost | render_phases/tests/benchmark_tests.rs |
| `bench_label_placer_try_place` | Single label placement | render_phases/tests/benchmark_tests.rs |
| `bench_label_placer_try_place_with_fallback` | Placement with collision | render_phases/tests/benchmark_tests.rs |
| `bench_full_label_placement_scenario` | Full frame (30+50 labels) | render_phases/tests/benchmark_tests.rs |
| `bench_beam_sorting` | Action beam ordering | render_phases/tests/benchmark_tests.rs |
| `bench_user_label_sorting` | User label prioritization | render_phases/tests/benchmark_tests.rs |
| `bench_estimate_text_width` | Text width estimation | render_phases/tests/benchmark_tests.rs |
| `bench_glow_lod_culling` | Glow LOD decision overhead | render_phases/tests/benchmark_tests.rs |

**Regression Thresholds**:

| Severity | Threshold | Action |
|----------|-----------|--------|
| Acceptable | < 5% | Document in commit message |
| Warning | 5-10% | Investigate, justify in PR |
| Blocking | > 10% | Do NOT commit without review |

**Session 7 Lesson Learned**: T9 viewport bounds check was committed without benchmarking. Post-commit A/B testing revealed +2.7% overhead (acceptable) but this should have been verified BEFORE committing. Always benchmark first.

---

## UI/UX Excellence Standards

### The Mobile-First Mandate

**Every UI change MUST be tested on mobile Safari before merge.**

The mobile experience is the PRIMARY experience. Desktop is the fallback.

### The UI/UX Workflow

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    UI/UX CHANGE WORKFLOW                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. CHECK ROADMAP                                                       │
│     └─ Read docs/ux/MOBILE_UX_ROADMAP.md                                │
│     └─ Identify relevant issue IDs (L1-L9, T1-T7, A1-A8, etc.)          │
│                                                                         │
│  2. SCREENSHOT BASELINE                                                 │
│     └─ Take screenshot on mobile Safari BEFORE changes                  │
│     └─ Note specific measurements (touch target sizes, font sizes)      │
│                                                                         │
│  3. IMPLEMENT                                                           │
│     └─ Follow the implementation guidance in roadmap                    │
│     └─ Respect all constraints (44px touch, 12px font, 4.5:1 contrast)  │
│     └─ Test on mobile during development, not after                     │
│                                                                         │
│  4. VERIFY                                                              │
│     └─ Screenshot on mobile Safari AFTER changes                        │
│     └─ Verify touch targets with inspector                              │
│     └─ Verify contrast ratios                                           │
│     └─ Test all gestures (tap, swipe, pinch)                            │
│     └─ Test with VoiceOver/screen reader                                │
│                                                                         │
│  5. DOCUMENT                                                            │
│     └─ Update issue status in MOBILE_UX_ROADMAP.md                      │
│     └─ Include before/after screenshots in commit                       │
│                                                                         │
│  6. COMMIT                                                              │
│     └─ Reference issue ID: "fix(L1): collapse stats panel by default"   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Non-Negotiable UI/UX Requirements

| Requirement | Specification | Verification |
|-------------|---------------|--------------|
| Touch targets | ≥44×44px | Browser inspector measurement |
| Font size | ≥12px body, ≥14px preferred | Browser inspector |
| Contrast | ≥4.5:1 text, ≥3:1 UI elements | Contrast checker tool |
| Labels | All icons have labels or tooltips | Visual inspection |
| Safe areas | Respect notch, Dynamic Island, home indicator | iOS device test |
| Viewport | Primary content ≥80% during use | Screenshot measurement |
| Collision | No overlapping labels | Visual inspection at all zoom levels |

### Current UI/UX Issues

See `docs/ux/MOBILE_UX_ROADMAP.md` for complete tracking (46 issues).

---

## Testing & Quality Standards

### Pre-Commit Checklist

**EVERY commit must pass this checklist:**

```bash
# 1. All tests pass
cargo test

# 2. No clippy warnings
cargo clippy -- -D warnings

# 3. Code is formatted
cargo fmt --check

# 4. Release build works
cargo build --release

# 5. WASM build works (if WASM changes)
wasm-pack build --target web --release

# 6. Mobile Safari test (if UI changes)
# Manual test required
```

### EXPERT+ Coverage Verification (MANDATORY)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    COVERAGE VERIFICATION REQUIREMENTS                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  To claim EXPERT+ quality, coverage must be MEASURED and DOCUMENTED.        │
│  "I think the tests are good" is NOT acceptable.                            │
│  "Coverage is X% (measured by tarpaulin)" IS acceptable.                    │
│                                                                             │
│  EVERY session that adds/modifies code MUST run these verifications:        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 1. Documentation Coverage (REQUIRED)

```bash
# Must produce ZERO warnings
cargo doc --no-deps --all-features 2>&1 | grep -E "(warning|error)"

# Expected output: (empty - no warnings)
# If warnings appear, FIX THEM before committing
```

**What this verifies:**
- All public items have documentation
- No broken doc links or unclosed HTML tags
- Doc examples compile correctly

#### 2. Line Coverage Analysis (REQUIRED)

```bash
# Install cargo-tarpaulin (done by session-setup.sh)
cargo install cargo-tarpaulin

# Run coverage analysis on core library crates
cargo tarpaulin -p rource-math -p rource-vcs -p rource-core -p rource-render \
    --out Stdout --skip-clean 2>&1 | tail -50

# Record the coverage percentage in commit messages
```

**Coverage Targets:**

| Crate | Target | Acceptable | Notes |
|-------|--------|------------|-------|
| rource-math | 80%+ | 60%+ | Pure functions, highly testable |
| rource-vcs | 70%+ | 50%+ | Parser logic, edge cases |
| rource-core | 60%+ | 40%+ | Scene, physics, animation |
| rource-render | 50%+ | 30%+ | Some GPU code untestable |
| rource-wasm | 30%+ | 20%+ | Platform-specific code |

**What coverage analysis reveals:**
- Which lines are never executed by tests
- Which branches are not covered
- Potential dead code or untested edge cases

#### 3. Coverage Reporting Protocol

**When adding tests, ALWAYS report:**

```markdown
Coverage improvement:
- Before: X% (Y/Z lines)
- After: X% (Y/Z lines)
- Delta: +X% (N new lines covered)
```

**When modifying code, ALWAYS verify:**

```bash
# Before changes
cargo tarpaulin -p <crate> --out Stdout 2>&1 | grep "coverage"

# After changes
cargo tarpaulin -p <crate> --out Stdout 2>&1 | grep "coverage"

# Coverage should NOT decrease
```

#### 4. Per-File Coverage Check (Optional but Recommended)

```bash
# Get detailed per-file breakdown
cargo tarpaulin -p rource-core --out Stdout 2>&1 | grep -E "^\\|\\| crates/"

# Example output:
# || crates/rource-core/src/animation/spline.rs: 93/138 +0.00%
# || crates/rource-core/src/physics/barnes_hut.rs: 51/83 +0.00%
```

#### 5. Coverage Exceptions

Some code CANNOT be covered by unit tests:

| Category | Example | Reason |
|----------|---------|--------|
| Platform-specific | WASM bindings | Requires browser runtime |
| GPU code | WebGL2 shaders | Requires GPU context |
| CLI entry points | main() | Integration test territory |
| Interactive code | Event handlers | Requires user input |

**For uncoverable code:**
- Document WHY it can't be unit tested
- Ensure it's integration tested or manually verified
- Mark with `// COVERAGE: Integration tested` comment

### Testing Requirements

| Test Type | Requirement | Status |
|-----------|-------------|--------|
| Unit tests | All public functions | Yes (2,076 tests) |
| Property tests | Math crate invariants | Yes (Implemented) |
| Chaos tests | Edge cases, unicode, boundaries | Yes (Implemented) |
| Benchmarks | Critical paths | Yes (13 benchmark suites) |
| Mutation testing | 80%+ score | TODO |
| Visual regression | Rendering consistency | TODO |
| Cross-browser | Chrome, Firefox, Safari, Edge | TODO |
| Load testing | 100k commits, 30 min | TODO |

### Determinism Requirements

For 100% deterministic output:

1. **Use fixed time step**: In headless mode, use `dt = 1.0 / framerate`
2. **Seed random generators**: Any randomness should use a fixed seed
3. **Pre-warm the scene**: Run ~30 update cycles before first render
4. **Force camera position**: Use `jump_to()` + `set_zoom()`

---

## Security Standards

### Security Requirements

| Requirement | Status |
|-------------|--------|
| `cargo audit` clean | Yes (CI enforced) |
| Minimal unsafe code | Yes (1 block, documented) |
| SBOM generation | Yes (SPDX + CycloneDX) |
| Fuzzing coverage | TODO (target: 75%+) |
| SECURITY.md | Yes (vulnerability reporting process) |

### Unsafe Code Policy

- Unsafe code requires explicit justification
- Must have `// SAFETY:` comment explaining invariants
- Must be reviewed for soundness
- Current unsafe: 1 block in `webgl2/buffers.rs` (float reinterpretation)

---

## Accessibility Standards

### WCAG 2.1 AA Requirements

| Criterion | Requirement | Status |
|-----------|-------------|--------|
| 1.4.3 Contrast | ≥4.5:1 for text | TODO: Fix gray text |
| 2.1.1 Keyboard | All functionality via keyboard | TODO |
| 2.4.7 Focus Visible | Clear focus indicators | TODO |
| 2.5.5 Target Size | ≥44×44px | TODO: Many violations |

### Accessibility Checklist

For every UI change:

- [ ] All interactive elements have visible focus state
- [ ] All icons have text labels or `aria-label`
- [ ] Color is not the only way to convey information
- [ ] Contrast ratios meet WCAG AA (4.5:1 text, 3:1 UI)
- [ ] Touch targets are ≥44×44px
- [ ] Screen reader announces state changes
- [ ] Reduced motion preference is respected

---

## Documentation Standards

### Documentation Requirements

Every change must be documented:

| Change Type | Documentation Required |
|-------------|------------------------|
| Performance optimization | CHRONOLOGY.md, BENCHMARKS.md, SUCCESSFUL_OPTIMIZATIONS.md |
| UI/UX improvement | MOBILE_UX_ROADMAP.md status update |
| New feature | README.md, API docs, usage examples |
| Bug fix | Commit message with root cause |
| Architecture change | ADR in docs/adr/ (TODO) |

### Commit Message Format

```
<type>(<scope>): <description>

<body with metrics and impact>

<footer with references>
```

Examples:

```
perf(phase65): implement label collision detection

- Label overlap: 100% → 0% (collision-free)
- Performance: 847µs for 1000 labels
- Algorithm: Spatial hash with greedy placement

Addresses: T1, T5 in MOBILE_UX_ROADMAP.md

fix(L1): collapse stats panel by default on mobile

- Visualization area: 20% → 85% of viewport
- Touch target: Play button now 48×48px
- Implements iOS-style swipe-to-dismiss

Before: Stats panel covers 40% of visualization
After: Stats panel collapsed, tap to expand

Addresses: L1, L7, L8 in MOBILE_UX_ROADMAP.md
```

---

## Common Tasks

### Adding a New VCS Parser

1. Create `crates/rource-vcs/src/parser/newvcs.rs`
2. Implement the `Parser` trait
3. Register in `crates/rource-vcs/src/detect.rs`
4. Add tests (unit + property + fuzz)
5. Update documentation

### Adding a New UI Component

1. Check `docs/ux/MOBILE_UX_ROADMAP.md` for requirements
2. Design mobile-first (44px targets, 12px fonts, 4.5:1 contrast)
3. Implement with accessibility (labels, focus, ARIA)
4. Test on mobile Safari
5. Update roadmap status

### Adding a New Configuration Option

1. Add field to appropriate module in `rource-core/src/config/settings/`
2. Add CLI argument in `rource-cli/src/args/mod.rs`
3. Add environment variable in `rource-core/src/config/config_env.rs`
4. Add WASM binding in `rource-wasm/src/wasm_api/settings.rs`
5. Update documentation (README, CLAUDE.md if significant)

---

## CI/CD Pipeline

### Workflow Overview

| Workflow | Purpose |
|----------|---------|
| CI | Core quality gates (format, clippy, test, build) |
| Coverage | Code coverage with Codecov |
| Benchmarks | Performance regression detection |
| Integration | Headless rendering tests |
| Security | Audits, license checks |
| Release | Multi-platform builds, signing |

### CI Jobs

| Job | Description |
|-----|-------------|
| Format | `cargo fmt --check` |
| Clippy | All lints with `-D warnings` |
| Test | Multi-platform (Linux, macOS, Windows) |
| MSRV | Minimum Supported Rust Version (1.93) |
| Build Native | Release binary with size report |
| Build WASM | WebAssembly with gzip size check |
| Documentation | Rustdoc with warning-as-error |

### Local CI Verification

```bash
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test --all
cargo doc --no-deps --all-features
cargo build --release
```

---

## Debugging

### Native

```bash
RUST_BACKTRACE=1 cargo run
RUST_LOG=debug cargo run
```

### WASM

- Browser DevTools console
- Enable `console_error_panic_hook`
- Use `web-sys` console logging

### Mobile Safari

1. Connect iPhone to Mac
2. Safari → Develop → [Device Name] → [Page]
3. Use Web Inspector for debugging

---

## Dependencies Philosophy

We minimize external dependencies to:
- Reduce binary size
- Improve compile times
- Ensure WASM compatibility
- Avoid security surface area

### Approved Dependencies

| Crate | Reason |
|-------|--------|
| `fontdue` | Best pure-Rust font rasterizer |
| `regex-lite` | Lighter than `regex`, no PCRE |
| `chrono` | Date/time handling |
| `wasm-bindgen` | Required for WASM |
| `clap` | CLI only, feature-gated |

### Avoid

- Heavy GUI frameworks (egui, iced)
- Full `image` crate
- `tokio`/`async-std`
- `serde` for core (optional for config)

---

## Git Workflow

### Branches

| Branch | Purpose |
|--------|---------|
| `main` | Stable releases |
| `develop` | Integration branch |
| `feature/*` | New features |
| `fix/*` | Bug fixes |
| `claude/*` | AI-assisted development |

### Commit Messages

Follow conventional commits with metrics:

```
feat: add git log parser
fix: correct spline interpolation at endpoints
docs: update CLAUDE.md with Expert+ standards
perf(phase65): label collision detection
ux(L1): collapsible stats panel
a11y(A1): add icon labels
```

---

## Troubleshooting

### Common Issues

| Symptom | Cause | Solution |
|---------|-------|----------|
| Black frames | Files haven't faded in | Pre-warm scene |
| Mobile UI cramped | Desktop-first design | Follow MOBILE_UX_ROADMAP.md |
| Labels overlap | No collision detection | Implement T1 from roadmap |
| Touch doesn't work | Targets too small | Ensure ≥44×44px |
| Low contrast | Wrong colors | Use contrast checker |

### WASM Build Fails

```bash
rustup target add wasm32-unknown-unknown
wasm-pack --version  # Check version
```

---

## Reference Links

| Resource | URL |
|----------|-----|
| Original Gource | https://github.com/acaudwell/Gource |
| Rust WASM Book | https://rustwasm.github.io/docs/book/ |
| Apple HIG | https://developer.apple.com/design/human-interface-guidelines/ |
| WCAG 2.1 | https://www.w3.org/WAI/WCAG21/quickref/ |
| Material Design | https://material.io/design |

---

## Roadmap Documents

### Active Roadmaps

| Document | Purpose | Priority |
|----------|---------|----------|
| `docs/REVIEW_STANDARDS.md` | Code review requirements | Critical |
| `docs/performance/FUTURE_WORK.md` | Technical excellence roadmap | High |
| `docs/ux/MOBILE_UX_ROADMAP.md` | UI/UX excellence roadmap | Critical |

### Roadmap Priority Order

**Phase A: Critical (Current Focus)**
1. Mobile UX fixes (L1, T1, A1, I1, V1)
2. Performance regression gates (CI-1)
3. Fuzzing coverage metrics (SEC-1)
4. API stability policy (DOC-1)

**Phase B: High Priority**
5. Load testing suite (OP-3)
6. Mutation testing (TST-1)
7. Label collision detection (T1, T5)
8. Touch target fixes (A2, A3)

**Phase C-E: Subsequent Phases**
See individual roadmap documents for complete priority order.

---

## Session Best Practices

### Starting a Session

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    SESSION STARTUP CHECKLIST                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  1. RUN VERIFICATION                                                        │
│     cargo test                          # All tests must pass               │
│     cargo clippy -- -D warnings         # Zero warnings allowed             │
│     cargo fmt --check                   # Must be formatted                 │
│     cargo doc --no-deps --all-features  # Zero doc warnings                 │
│                                                                             │
│  2. READ CURRENT STATE                                                      │
│     docs/performance/CHRONOLOGY.md      # What phase are we on?             │
│     docs/performance/ALGORITHM_CANDIDATES.md  # What's next?                │
│     docs/performance/NOT_APPLICABLE.md  # What's been ruled out?            │
│                                                                             │
│  3. ESTABLISH BASELINE                                                      │
│     cargo test -p rource-wasm bench_ --release -- --nocapture               │
│     Record exact numbers BEFORE any changes                                 │
│                                                                             │
│  4. RECORD COVERAGE BASELINE (if adding/modifying code)                     │
│     cargo tarpaulin -p <crate> --out Stdout | grep "coverage"               │
│     Record percentage BEFORE making changes                                 │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### During a Session

| Action | Requirement |
|--------|-------------|
| Before changing hot path code | Benchmark baseline |
| After changing hot path code | Benchmark again, compare |
| Claiming an improvement | Exact % with before/after values |
| Claiming N/A status | Document WHY with evidence |
| Any optimization attempt | Update CHRONOLOGY.md with phase number |

### Ending a Session

1. **Verify clean state**:
   ```bash
   cargo test && cargo clippy -- -D warnings && cargo doc --no-deps --all-features
   ```
2. **Verify coverage (if code was added/modified)**:
   ```bash
   cargo tarpaulin -p <crate> --out Stdout | grep "coverage"
   # Coverage should NOT decrease from baseline
   ```
3. **Update documentation**: CHRONOLOGY.md, NOT_APPLICABLE.md as needed
4. **Commit with metrics**: Include exact measurements AND coverage in commit message
5. **Push to branch**: Ensure all changes are pushed

### Tips for Expert+ Quality

1. **Never trust intuition**
   - "This should be faster" is not evidence
   - The only evidence is before/after benchmarks
   - Even "obvious" improvements can regress performance

2. **Measure twice, claim once**
   - Run benchmarks multiple times
   - Ensure statistical significance (95% CI)
   - Account for measurement noise

3. **Document the negative results**
   - NOT APPLICABLE findings are valuable
   - They prevent future sessions from repeating work
   - Always explain WHY something didn't work

4. **Respect the 20 µs budget**
   - At 50,000 FPS, every nanosecond counts
   - 1 µs = 5% of frame budget
   - Small regressions compound

5. **Use the phase system**
   - Every optimization attempt gets a phase number
   - Implemented, N/A, or Failed - all get documented
   - The CHRONOLOGY is the project's optimization history

6. **Read before implementing**
   - Check NOT_APPLICABLE.md before trying an algorithm
   - Check SUCCESSFUL_OPTIMIZATIONS.md for patterns
   - Don't repeat work that's already been done

7. **Benchmark protocol**
   ```bash
   # Always do this before AND after changes:
   cargo test -p rource-wasm bench_ --release -- --nocapture 2>&1 | tee benchmark_$(date +%Y%m%d_%H%M%S).txt
   ```

### Common Pitfalls to Avoid

| Pitfall | Why It's Wrong | Correct Approach |
|---------|---------------|------------------|
| "I didn't benchmark before" | No baseline = speculation | Always baseline first |
| "The improvement is obvious" | Intuition ≠ data | Measure everything |
| "~50% faster" | Approximation | "52.3% faster (2.41µs → 1.15µs)" |
| "Works on my machine" | Not reproducible | Use criterion with CI |
| "This is a pre-existing issue" | Abdication | Fix it or document it |
| "I'll document later" | Never happens | Document as you implement |

### Performance Vocabulary

Use precise language:

| Imprecise | Precise |
|-----------|---------|
| "faster" | "52.3% reduction in execution time (2.41µs → 1.15µs)" |
| "slower" | "+15.2% regression (1.15µs → 1.32µs)" |
| "about 50%" | "52.3% (calculated from measured values)" |
| "significant improvement" | "statistically significant (p < 0.05, 95% CI)" |
| "no change" | "within noise margin (±2.1%, not statistically significant)" |

---

## Summary: The Expert+ Standard

Every session, every commit, every line of code must meet this standard:

| Aspect | Requirement |
|--------|-------------|
| **Performance** | Picosecond/nanosecond precision, <20µs frame budget, criterion benchmarks |
| **Measurement** | BEFORE and AFTER benchmarks mandatory, exact percentages required |
| **UI/UX** | Mobile-first, 44px touch targets, 12px fonts, 4.5:1 contrast |
| **Testing** | All tests pass, mutations killed, cross-browser verified |
| **Security** | Audited, fuzzed, minimal unsafe, SBOM generated |
| **Accessibility** | WCAG AA, keyboard navigable, screen reader compatible |
| **Documentation** | Before/after metrics, CHRONOLOGY.md updated, phase number assigned |

**The questions to ask before every commit:**

1. "Did I benchmark BEFORE making changes?"
2. "Did I benchmark AFTER making changes?"
3. "Is the improvement statistically significant?"
4. "Is the documentation complete with exact metrics?"
5. "Would this pass review by a principal engineer at a top tech company?"

If the answer to ANY of these is "no," the work is not complete.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  50,000 FPS = 20 µs frame budget                                            │
│  1 µs = 5% of frame budget = 3,000 CPU cycles                               │
│  Every nanosecond matters.                                                  │
│                                                                             │
│  Never guess. Never assume. Never overstate. Always measure.                │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

*Last updated: 2026-01-27*
*Standard: Expert+ Excellence (Zero Compromises)*
*Optimization Phases: 77 (see docs/performance/CHRONOLOGY.md)*
