# Code Review Standards: Expert+ Excellence

**Status**: Active Standard
**Created**: 2026-01-26
**Purpose**: Codify review requirements for Expert+ quality across all contributions
**Enforcement**: All PRs MUST pass these standards before merge

---

## Executive Summary

This document defines the **mandatory review standards** for the Rource project. Every pull request—regardless of size—must meet these standards. There are **no exceptions**.

```
+-----------------------------------------------------------------------------+
|                     REVIEW GATE SUMMARY                                      |
+-----------------------------------------------------------------------------+
|                                                                             |
|  Every PR must pass ALL of these gates before merge:                        |
|                                                                             |
|  [ ] CI Pipeline         - All checks green                                 |
|  [ ] Code Quality        - Zero warnings, formatted, documented             |
|  [ ] Test Coverage       - Tests for new/changed code                       |
|  [ ] Performance         - No regressions, benchmarks if applicable         |
|  [ ] Mobile UX           - Tested on mobile Safari (if UI changes)          |
|  [ ] Accessibility       - WCAG AA compliance (if UI changes)               |
|  [ ] Documentation       - Updated roadmaps, changelogs, docs               |
|  [ ] Security            - No new vulnerabilities, audit clean              |
|                                                                             |
+-----------------------------------------------------------------------------+
```

---

## Quick Reference: Review Checklists

### Universal Checklist (ALL PRs)

Every PR, regardless of type, must satisfy:

```
[ ] cargo test              - All 2900+ tests pass
[ ] cargo clippy            - Zero warnings (-D warnings)
[ ] cargo fmt --check       - Code formatted
[ ] cargo doc               - Documentation builds without warnings
[ ] Commit messages         - Conventional commits format
[ ] No secrets              - No API keys, passwords, or credentials
[ ] No console.log/println! - No debug output in production code
```

### Performance Change Checklist

Additional requirements for performance-related changes:

```
[ ] Baseline benchmark      - Criterion benchmark BEFORE changes
[ ] Optimized benchmark     - Same benchmark AFTER changes
[ ] Improvement documented  - Exact percentages (not "~50%", but "52.3%")
[ ] Statistical rigor       - 100+ samples, 95% CI reported
[ ] CHRONOLOGY.md updated   - Full phase documentation
[ ] BENCHMARKS.md updated   - Raw data tables
[ ] No regressions          - Other benchmarks not degraded by >5%
```

### UI/UX Change Checklist

Additional requirements for UI/UX changes:

```
[ ] Mobile Safari tested    - iPhone Safari (real device or simulator)
[ ] Touch targets >=44px    - All interactive elements measured
[ ] Font size >=12px        - All text measured
[ ] Contrast >=4.5:1        - Text against background verified
[ ] Labels on icons         - No mystery meat navigation
[ ] Safe areas respected    - Notch, Dynamic Island, home indicator
[ ] MOBILE_UX_ROADMAP.md    - Issue status updated
[ ] Screenshots included    - Before/after in PR description
```

### Accessibility Change Checklist

Additional requirements for accessibility changes:

```
[ ] Keyboard navigable      - All controls accessible via keyboard
[ ] Focus visible           - Clear focus indicators
[ ] ARIA labels             - All interactive elements labeled
[ ] Screen reader tested    - VoiceOver/TalkBack compatible
[ ] Color not sole cue      - Information not conveyed by color alone
[ ] Reduced motion          - Respects prefers-reduced-motion
```

### Security Change Checklist

Additional requirements for security-sensitive changes:

```
[ ] cargo audit             - No known vulnerabilities
[ ] Unsafe code justified   - SAFETY comment with invariants
[ ] Input validation        - All external input validated
[ ] No new dependencies     - Or dependencies audited
[ ] SBOM updated            - If dependencies changed
```

---

## Detailed Standards

### 1. Code Quality Gate

**Requirement**: All code must pass static analysis with zero tolerance for warnings.

#### Verification Commands

```bash
# Must all pass with zero errors/warnings
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test --all
cargo doc --no-deps --all-features
```

#### Failure Criteria

| Issue | Severity | Action |
|-------|----------|--------|
| Clippy warning | Blocking | Fix before merge |
| Format violation | Blocking | Run `cargo fmt` |
| Test failure | Blocking | Fix or update test |
| Doc warning | Blocking | Fix documentation |

#### Acceptable Suppressions

Suppressions are **rarely** acceptable and require explicit justification:

```rust
// ACCEPTABLE: Known false positive with documented issue
#[allow(clippy::too_many_arguments)]
// Justification: This function is internal and breaking it up
// would reduce readability. See discussion in PR #123.
fn complex_internal_function(...) { ... }

// NOT ACCEPTABLE: Suppression without justification
#[allow(clippy::too_many_arguments)]
fn some_function(...) { ... }
```

---

### 2. Performance Gate

**Requirement**: No performance regressions. Optimizations must be benchmarked.

#### When Benchmarks Are Required

| Change Type | Benchmark Required |
|-------------|-------------------|
| Hot path modification | Yes |
| Algorithm change | Yes |
| Data structure change | Yes |
| New feature | If impacts perf |
| Bug fix | If in hot path |
| Refactoring | If in hot path |

#### Benchmark Standards

1. **Tool**: Use Criterion for all benchmarks
2. **Samples**: Minimum 100 samples (Criterion default)
3. **Confidence**: Report 95% confidence intervals
4. **Scaling**: Test multiple input sizes (e.g., 50, 100, 200, 300, 500)
5. **Reproducibility**: Results must be reproducible across runs

#### Reporting Format

```markdown
## Performance Impact

### Benchmark: scene_layout_update

| Input Size | Before | After | Change |
|------------|--------|-------|--------|
| 100 | 2.41 µs | 1.15 µs | -52.3% |
| 500 | 12.05 µs | 5.73 µs | -52.4% |
| 1000 | 24.11 µs | 11.45 µs | -52.5% |

**Method**: Criterion, 100 samples, 95% CI
**Hardware**: Apple M2 Pro, 32GB RAM
**Complexity**: O(n) maintained (verified via scaling)
```

#### Regression Policy

| Regression | Action |
|------------|--------|
| <2% | Document, acceptable |
| 2-5% | Justify in PR, needs approval |
| 5-10% | Requires strong justification |
| >10% | Blocking, must be fixed |

---

### 3. Mobile UX Gate

**Requirement**: All UI changes must be tested on mobile Safari.

#### Why Mobile Safari?

1. Safari has the most restrictive WebGL implementation
2. iOS is the primary mobile platform for target users
3. Touch interactions differ significantly from desktop
4. Safe areas (notch, Dynamic Island) require testing

#### Testing Process

1. **Build WASM**: `./scripts/build-wasm.sh`
2. **Start server**: `cd rource-wasm/www && python3 -m http.server 8080`
3. **Connect iPhone**: Enable Web Inspector in Safari settings
4. **Open page**: Navigate to `http://<your-ip>:8080` on iPhone
5. **Test interactions**: All touch targets, gestures, layouts
6. **Inspect**: Use Safari Web Inspector from Mac

#### Measurement Requirements

| Element | Minimum | Tool |
|---------|---------|------|
| Touch targets | 44x44px | Browser inspector |
| Font size | 12px | Browser inspector |
| Contrast ratio | 4.5:1 | Contrast checker |
| Visualization area | 80%+ during playback | Screenshot |

#### Screenshot Requirements

PRs with UI changes must include:

1. **Before screenshot**: Current state on mobile
2. **After screenshot**: New state on mobile
3. **Measurements**: Touch target sizes, font sizes annotated
4. **Device info**: iPhone model, iOS version, Safari version

---

### 4. Accessibility Gate

**Requirement**: WCAG 2.1 AA compliance for all UI elements.

#### Minimum Requirements

| WCAG Criterion | Requirement |
|----------------|-------------|
| 1.4.3 Contrast | 4.5:1 for normal text, 3:1 for large text |
| 1.4.11 Non-text Contrast | 3:1 for UI components |
| 2.1.1 Keyboard | All functionality via keyboard |
| 2.4.7 Focus Visible | Clear focus indicators |
| 2.5.5 Target Size | 44x44px minimum |

#### Testing Tools

- **axe DevTools**: Browser extension for accessibility audit
- **WAVE**: Web accessibility evaluation tool
- **Contrast Checker**: For color contrast verification
- **VoiceOver**: Built-in screen reader on macOS/iOS

#### Required Attributes

```html
<!-- All buttons must have accessible names -->
<button aria-label="Play visualization">
  <svg>...</svg>
</button>

<!-- All form inputs must have labels -->
<label for="speed">Playback Speed</label>
<input id="speed" type="range" />

<!-- All icons must have text alternatives -->
<span class="icon" role="img" aria-label="Settings">...</span>
```

---

### 5. Documentation Gate

**Requirement**: All changes must be documented appropriately.

#### Documentation Matrix

| Change Type | Required Documentation |
|-------------|----------------------|
| Performance optimization | CHRONOLOGY.md, BENCHMARKS.md |
| UI/UX improvement | MOBILE_UX_ROADMAP.md |
| New feature | README.md, API docs |
| Bug fix | Commit message (root cause) |
| Configuration change | README.md, CLAUDE.md |
| Architecture change | docs/ARCHITECTURE.md |

#### Commit Message Format

Use [Conventional Commits](https://www.conventionalcommits.org/):

```
<type>(<scope>): <description>

<body with context and metrics>

<footer with references>
```

**Types**: `feat`, `fix`, `perf`, `docs`, `style`, `refactor`, `test`, `chore`

**Examples**:

```
perf(phase65): implement label collision detection

- Label overlap: 100% -> 0% (collision-free)
- Performance: 847µs for 1000 labels
- Algorithm: Spatial hash with greedy placement

Addresses: T1, T5 in MOBILE_UX_ROADMAP.md
```

```
fix(L1): collapse stats panel by default on mobile

- Visualization area: 20% -> 85% of viewport
- Touch target: Play button now 48x48px
- Implements iOS-style swipe-to-dismiss

Before: Stats panel covers 40% of visualization
After: Stats panel collapsed, tap to expand

Addresses: L1, L7, L8 in MOBILE_UX_ROADMAP.md
```

---

### 6. Security Gate

**Requirement**: No new security vulnerabilities.

#### Automated Checks

```bash
# Run before every PR
cargo audit
```

#### Manual Review

| Check | Requirement |
|-------|-------------|
| New dependencies | Must be audited, necessary, minimal |
| Unsafe code | Requires SAFETY comment |
| External input | Must be validated |
| Error messages | No sensitive info leaked |
| CORS/CSP | Properly configured |

#### Unsafe Code Standard

Every `unsafe` block must have a `// SAFETY:` comment:

```rust
// SAFETY: We have verified that:
// 1. The slice has exactly the right length (checked above)
// 2. The data is properly aligned for f32 (guaranteed by Vec<f32>)
// 3. No aliasing occurs (we have exclusive access to the buffer)
unsafe {
    std::slice::from_raw_parts(ptr, len)
}
```

---

## Review Workflow

### For Contributors

1. **Before Starting**
   - Read relevant roadmap docs (FUTURE_WORK.md, MOBILE_UX_ROADMAP.md)
   - Understand success criteria before coding
   - Create benchmarks/screenshots BEFORE making changes

2. **During Development**
   - Run `cargo test` frequently
   - Run `cargo clippy` before committing
   - Test on mobile Safari if making UI changes
   - Update documentation as you go

3. **Before PR Submission**
   - Complete ALL applicable checklists above
   - Include before/after metrics in PR description
   - Reference relevant issue IDs (L1, T5, etc.)
   - Self-review your own code

4. **PR Description Template**
   ```markdown
   ## Summary
   [1-2 sentences describing the change]

   ## Type of Change
   - [ ] Bug fix
   - [ ] New feature
   - [ ] Performance improvement
   - [ ] UI/UX improvement
   - [ ] Documentation
   - [ ] Refactoring

   ## Checklist
   - [ ] cargo test passes
   - [ ] cargo clippy passes
   - [ ] cargo fmt applied
   - [ ] Documentation updated
   - [ ] [If UI] Mobile Safari tested
   - [ ] [If perf] Benchmarks included

   ## Metrics
   [Include before/after measurements]

   ## Screenshots
   [If UI change, include before/after mobile screenshots]

   ## References
   [Link to relevant issue IDs from roadmap docs]
   ```

### For Reviewers

1. **First Pass: Automated Checks**
   - CI pipeline green?
   - All required checks passing?

2. **Second Pass: Code Quality**
   - Code readable and maintainable?
   - No obvious bugs or edge cases?
   - Tests adequate?

3. **Third Pass: Domain-Specific**
   - Performance: Benchmarks provided? No regressions?
   - UI/UX: Mobile tested? Touch targets OK?
   - Accessibility: WCAG compliant?

4. **Review Decision Matrix**

| Condition | Decision |
|-----------|----------|
| CI fails | Request changes |
| Missing tests | Request changes |
| Missing mobile test (UI change) | Request changes |
| Missing benchmarks (perf change) | Request changes |
| Regression >5% without justification | Request changes |
| Touch targets <44px | Request changes |
| All checks pass | Approve |

---

## Enforcement

### Blocking Merge

PRs are **blocked from merge** if:

1. CI pipeline fails
2. Clippy warnings present
3. Tests fail
4. Mobile Safari not tested (for UI changes)
5. Benchmarks not provided (for performance changes)
6. Performance regression >5% without justification
7. Touch targets below 44px (for UI changes)
8. Contrast ratio below 4.5:1 (for UI changes)
9. Documentation not updated

### Appeals Process

If you believe a standard should be waived:

1. Explain why in the PR description
2. Reference the specific standard
3. Provide alternative mitigation
4. Get explicit approval from maintainer

Example:

```markdown
## Standard Waiver Request

**Standard**: Touch targets >=44px
**Current value**: 36px for timeline ticks
**Justification**: Timeline ticks are decorative, not interactive.
The draggable thumb is 48px.
**Mitigation**: Added tap area expansion using padding.
```

---

## Metrics Dashboard

Track progress toward Expert+ across all domains:

| Domain | Current | Target | Gap | Primary Checklist |
|--------|---------|--------|-----|-------------------|
| Technical Excellence | 9.5/10 | 10/10 | Minor | Universal |
| Performance Engineering | Expert+ | Expert+ | None | Performance |
| UI/UX Design | 3/10 | 9/10 | Critical | Mobile UX |
| Testing Maturity | 8/10 | 10/10 | Moderate | Universal |
| Security Posture | 7/10 | 10/10 | Major | Security |
| Accessibility | Not Rated | 10/10 | Critical | Accessibility |
| Documentation | 9.5/10 | 10/10 | Minor | Documentation |

---

## Quick Commands

Copy-paste these for common review tasks:

```bash
# Full pre-PR verification
cargo fmt && cargo clippy --all-targets --all-features -- -D warnings && cargo test --all && cargo doc --no-deps

# Build and serve WASM for mobile testing
./scripts/build-wasm.sh && cd rource-wasm/www && python3 -m http.server 8080

# Run benchmarks
cargo bench --bench scene_perf

# Security audit
cargo audit
```

---

## Related Documents

| Document | Purpose |
|----------|---------|
| `CLAUDE.md` | Project standards and guidelines |
| `CONTRIBUTING.md` | Contribution workflow |
| `docs/performance/FUTURE_WORK.md` | Technical roadmap (25 tasks) |
| `docs/ux/MOBILE_UX_ROADMAP.md` | UX roadmap (46 issues) |
| `docs/performance/CHRONOLOGY.md` | Optimization history |
| `docs/performance/BENCHMARKS.md` | Benchmark data |

---

## Summary: The Expert+ Review Standard

Every review should answer:

> "Would this pass review by a principal engineer at a top tech company?"

If the answer is anything other than **"absolutely yes"**, the PR needs more work.

**Remember:**
- If it cannot be measured, it did not happen.
- If it was not tested, it does not work.
- If it was not documented, it does not exist.

---

*Last updated: 2026-01-26*
*Standard: Expert+ Excellence (Zero Compromises)*
