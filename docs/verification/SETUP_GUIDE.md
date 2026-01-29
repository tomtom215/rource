# Formal Verification Environment Setup Guide

This guide documents the complete setup procedure for all formal verification
tools used in the Rource project. The setup is automated via
`scripts/setup-formal-verification.sh`.

**Standard**: PEER REVIEWED PUBLISHED ACADEMIC (Zero Compromises)

---

## Table of Contents

1. [Quick Start](#quick-start)
2. [Tool Overview](#tool-overview)
3. [Verus Setup](#verus-setup)
4. [Coq Setup](#coq-setup)
5. [MetaCoq Setup](#metacoq-setup)
6. [wasm_of_ocaml Setup](#wasm_of_ocaml-setup)
7. [Verification Commands](#verification-commands)
8. [Troubleshooting](#troubleshooting)
9. [Architecture Reference](#architecture-reference)

---

## Quick Start

```bash
# Automated setup (installs everything)
./scripts/setup-formal-verification.sh

# Check installation status only
./scripts/setup-formal-verification.sh --check

# Run all proofs after setup
./scripts/setup-formal-verification.sh --verify
```

After setup, verify the environment:

```bash
# Verus
/tmp/verus/verus --version

# Coq
coqc --version   # Should be 8.18.x

# opam environment (for MetaCoq and wasm_of_ocaml)
eval $(opam env)

# MetaCoq (if installed)
coqc -Q . MetaCoq.Erasure -where 2>/dev/null

# wasm_of_ocaml
which wasm_of_ocaml 2>/dev/null
```

---

## Tool Overview

| Tool | Version | Purpose | Install Location |
|------|---------|---------|------------------|
| **Verus** | Latest | Rust formal verification (105 theorems) | `/tmp/verus/` |
| **Coq** | 8.18.0 | Proof assistant (347 theorems) | System (`apt`) + opam (see Rocq migration) |
| **coq-equations** | 1.3+8.18 | Dependent pattern matching for Coq | opam |
| **MetaCoq** | 8.18.dev | Verified erasure/extraction (Path 2) | `/tmp/metacoq/` + opam |
| **wasm_of_ocaml** | 6.2.0+ | OCaml-to-WASM compiler (Path 1) | opam |
| **OCaml** | 4.14.x | Required by Coq and extraction pipeline | opam |
| **opam** | 2.x | OCaml package manager | System |

### Verification Architecture

```
Layer 1: Abstract Proofs (R-based, full real arithmetic)
  Vec2.v, Vec3.v, Vec4.v, Mat3.v, Mat4.v
  Vec2_Proofs.v, Vec3_Proofs.v, Vec4_Proofs.v
  Mat3_Proofs.v, Mat4_Proofs.v, Complexity.v
        |
Layer 2: Computational Bridge (Z-based, extractable)
  Vec2_Compute.v, Vec3_Compute.v, Vec4_Compute.v
  Mat3_Compute.v, Mat4_Compute.v
        |
Layer 3: Extraction to OCaml
  RourceMath_Extract.v -> rource_math_extracted.ml
        |
Layer 4: OCaml to WASM
  Path 1: wasm_of_ocaml (production, 6.8 KB)
  Path 2: MetaCoq verified extraction (academic)
```

---

## Verus Setup

### Prerequisites

- Linux x86_64
- `curl`, `unzip`
- `rustup` with Rust 1.92.0 toolchain

### Installation

```bash
# Automated
./scripts/setup-formal-verification.sh --verus

# Manual
mkdir -p /tmp/verus
curl -L -o /tmp/verus/verus.zip \
  https://github.com/verus-lang/verus/releases/latest/download/verus-x86_64-linux.zip
unzip -o /tmp/verus/verus.zip -d /tmp/verus/
chmod +x /tmp/verus/verus

# Install required Rust toolchain
rustup install 1.92.0
```

### Verification

```bash
/tmp/verus/verus crates/rource-math/proofs/vec2_proofs.rs
/tmp/verus/verus crates/rource-math/proofs/vec3_proofs.rs
/tmp/verus/verus crates/rource-math/proofs/vec4_proofs.rs
/tmp/verus/verus crates/rource-math/proofs/mat3_proofs.rs
/tmp/verus/verus crates/rource-math/proofs/mat4_proofs.rs
```

**Expected output**: Each file reports "0 errors" and verification conditions pass.

### Verus Proof Files

| File | Theorems | VCs | Types Verified |
|------|----------|-----|----------------|
| `vec2_proofs.rs` | 23 | 53 | Vec2 |
| `vec3_proofs.rs` | 24 | 68 | Vec3 |
| `vec4_proofs.rs` | 22 | 68 | Vec4 |
| `mat3_proofs.rs` | 18 | 26 | Mat3 |
| `mat4_proofs.rs` | 18 | 27 | Mat4 |
| **Total** | **105** | **242** | **5 types** |

---

## Coq Setup

### Prerequisites

- `apt-get` (Debian/Ubuntu) or `opam` 2.x
- For MetaCoq: `libgmp-dev` (GMP development library)

### Installation (apt + opam hybrid)

The recommended approach uses `apt` for the base Coq installation and `opam`
for additional packages (coq-equations, MetaCoq, wasm_of_ocaml).

```bash
# Automated
./scripts/setup-formal-verification.sh --coq

# Manual Step 1: Install Coq via apt
sudo apt-get update
sudo apt-get install -y coq coq-theories

# Manual Step 2: Install opam and initialize
sudo apt-get install -y opam libgmp-dev
opam init --auto-setup --yes
eval $(opam env)

# Manual Step 3: Install coq-equations (required by MetaCoq)
# IMPORTANT: The Coq opam repos (coq.inria.fr) may be down (HTTP 503).
# Pin directly from GitHub source to bypass:
opam pin add coq-equations \
  "git+https://github.com/mattam82/Coq-Equations.git#v1.3-8.18" --yes

# Manual Step 4: Verify
coqc --version    # Should show 8.18.x
opam list coq-equations  # Should show 1.3+8.18
```

### CRITICAL: coq-theories Package

The `coq-theories` package provides the Coq standard library including:
- `Reals` (real number theory, used in abstract proofs)
- `ZArith` (integer arithmetic, used in computational bridge)
- `Lra` (linear real arithmetic tactic)
- `Lia` (linear integer arithmetic tactic)
- `Ring` (polynomial ring tactic)

**Without `coq-theories`, proofs will fail with "Cannot find library" errors.**

### Coq Opam Repository Workaround

The official Coq opam repositories (`coq.inria.fr/opam/released`,
`rocq-prover.org/opam/released`) frequently return HTTP 503 errors.

**Workaround**: Pin packages directly from GitHub source repositories:

```bash
# Instead of: opam repo add coq-released https://coq.inria.fr/opam/released
# Use direct GitHub pins:

opam pin add coq-equations \
  "git+https://github.com/mattam82/Coq-Equations.git#v1.3-8.18" --yes
```

### Verification

```bash
cd crates/rource-math/proofs/coq

# Layer 1: Abstract specifications
coqc -Q . RourceMath Vec2.v Vec3.v Vec4.v Mat3.v Mat4.v

# Layer 1: Abstract proofs
coqc -Q . RourceMath Vec2_Proofs.v Vec3_Proofs.v Vec4_Proofs.v
coqc -Q . RourceMath Mat3_Proofs.v Mat4_Proofs.v

# Complexity proofs
coqc -Q . RourceMath Complexity.v

# Layer 2: Computational bridge
coqc -Q . RourceMath Vec2_Compute.v Vec3_Compute.v Vec4_Compute.v
coqc -Q . RourceMath Mat3_Compute.v Mat4_Compute.v

# Layer 3: Extraction
coqc -Q . RourceMath Vec2_Extract.v Vec3_Extract.v Vec4_Extract.v
coqc -Q . RourceMath Mat3_Extract.v Mat4_Extract.v
coqc -Q . RourceMath RourceMath_Extract.v
```

**Expected output**: All files compile with zero errors.

### Coq Proof Files

| Layer | File | Theorems | Description |
|-------|------|----------|-------------|
| 1 (Spec) | `Vec2.v` | 3 | R-based Vec2 specification |
| 1 (Spec) | `Vec3.v` | 1 | R-based Vec3 specification |
| 1 (Spec) | `Vec4.v` | 1 | R-based Vec4 specification |
| 1 (Spec) | `Mat3.v` | 0 | R-based Mat3 specification |
| 1 (Spec) | `Mat4.v` | 0 | R-based Mat4 specification |
| 1 (Proof) | `Vec2_Proofs.v` | 25 | Vec2 algebraic properties |
| 1 (Proof) | `Vec3_Proofs.v` | 37 | Vec3 algebraic properties |
| 1 (Proof) | `Vec4_Proofs.v` | 24 | Vec4 algebraic properties |
| 1 (Proof) | `Mat3_Proofs.v` | 21 | Mat3 algebraic properties |
| 1 (Proof) | `Mat4_Proofs.v` | 21 | Mat4 algebraic properties |
| 1 (Proof) | `Complexity.v` | 60 | O(1) complexity bounds |
| 2 (Compute) | `Vec2_Compute.v` | 25 | Z-based Vec2 (extractable) |
| 2 (Compute) | `Vec3_Compute.v` | 37 | Z-based Vec3 (extractable) |
| 2 (Compute) | `Vec4_Compute.v` | 24 | Z-based Vec4 (extractable) |
| 2 (Compute) | `Mat3_Compute.v` | 21 | Z-based Mat3 (extractable) |
| 2 (Compute) | `Mat4_Compute.v` | 21 | Z-based Mat4 (extractable) |
| 3 (Extract) | `RourceMath_Extract.v` | 0 | Unified OCaml extraction |
| **Total** | **22 files** | **347** | **Zero admits** |

---

## MetaCoq Setup

MetaCoq provides verified extraction (erasure) from Coq to OCaml. This is
Path 2 of the Coq-to-WASM pipeline, providing academic-grade assurance that
the extraction preserves semantics.

### Prerequisites

- Coq 8.18.x (installed via Coq Setup above)
- `coq-equations` 1.3+8.18 (installed via Coq Setup above)
- `stdlib-shims` (opam package)
- `libgmp-dev` (for zarith)
- `git` (to clone MetaCoq source)

### Version Compatibility

| MetaCoq Branch | Coq Version | Status |
|----------------|-------------|--------|
| `coq-8.18` | 8.18.x | Compatible (our target) |
| `coq-8.19` | 8.19.x | Not compatible |
| MetaRocq (renamed) | 9.0+ | Not compatible |

**Key distinction**: MetaCoq was renamed to MetaRocq for Rocq (Coq 9.0+).
For Coq 8.18, use the original `MetaCoq/metacoq` repository on the
`coq-8.18` branch.

The `MetaRocq/rocq-verified-extraction` repo (PLDI'24 Distinguished Paper)
requires Coq 8.19+ minimum and is NOT compatible with our Coq 8.18 setup.

### Installation (from source)

```bash
# Automated
./scripts/setup-formal-verification.sh --metacoq

# Manual Step 1: Ensure prerequisites
eval $(opam env)
opam install stdlib-shims --yes

# Manual Step 2: Clone MetaCoq coq-8.18 branch
git clone --branch coq-8.18 --depth 1 \
  https://github.com/MetaCoq/metacoq.git /tmp/metacoq

# Manual Step 3: Configure for local build
cd /tmp/metacoq
bash ./configure.sh local

# Manual Step 4: Build (order matters)
make utils          # Utility library
make common         # Common definitions
make template-coq   # Template Monad + plugin
make pcuic          # PCUIC metatheory
make template-pcuic # Template <-> PCUIC translations
make safechecker    # Verified type checker
make erasure        # Verified erasure
make erasure-plugin # Erasure plugin (our target)

# Manual Step 5: Install into Coq's user-contrib
make install
```

### Build Order and Dependencies

```
utils
  |
common
  |
template-coq (includes OCaml plugin)
  |
  +--- pcuic
  |      |
  +------+--- template-pcuic
  |                |
  +--- safechecker-+
  |                |
  +--- erasure ----+
         |
  erasure-plugin (our target)
```

### MetaCoq Usage

After installation, MetaCoq's erasure plugin can be loaded in Coq:

```coq
From MetaCoq.ErasurePlugin Require Import Loader.
From MetaCoq.Erasure Require Import Extraction.

(* Use MetaCoq's verified erasure instead of standard Extraction *)
MetaCoq Run (erase_and_print_template_program <term>).
```

---

## wasm_of_ocaml Setup

`wasm_of_ocaml` compiles OCaml bytecode to WebAssembly. This is Path 1 of
the Coq-to-WASM pipeline (production-ready, unverified extraction step).

### Prerequisites

- opam 2.x with OCaml 4.14.x or 5.x
- Coq 8.18.x (for the extraction step)

### Installation

```bash
# Automated
./scripts/setup-formal-verification.sh --wasm-of-ocaml

# Manual
eval $(opam env)
opam install wasm_of_ocaml --yes
```

### Usage (Coq -> OCaml -> WASM pipeline)

```bash
cd crates/rource-math/proofs/coq

# Step 1: Extract Coq to OCaml (produces rource_math_extracted.ml)
coqc -Q . RourceMath RourceMath_Extract.v

# Step 2: Compile OCaml to bytecode
ocamlfind ocamlc -package zarith -linkpkg \
  rource_math_extracted.ml -o rource_math.byte

# Step 3: Compile bytecode to WASM
wasm_of_ocaml rource_math.byte -o rource_math.wasm

# Verify output
ls -la rource_math.wasm  # Should be ~6.8 KB
```

---

## Verification Commands

### Quick Verification (all proofs)

```bash
./scripts/setup-formal-verification.sh --verify
```

### Manual Verification

```bash
# Verus (105 theorems, ~seconds)
for f in crates/rource-math/proofs/*_proofs.rs; do
  /tmp/verus/verus "$f"
done

# Coq (347 theorems, ~40 seconds)
cd crates/rource-math/proofs/coq
for f in Vec2.v Vec3.v Vec4.v Mat3.v Mat4.v; do
  coqc -Q . RourceMath "$f"
done
for f in Vec2_Proofs.v Vec3_Proofs.v Vec4_Proofs.v Mat3_Proofs.v Mat4_Proofs.v; do
  coqc -Q . RourceMath "$f"
done
coqc -Q . RourceMath Complexity.v
for f in Vec2_Compute.v Vec3_Compute.v Vec4_Compute.v Mat3_Compute.v Mat4_Compute.v; do
  coqc -Q . RourceMath "$f"
done
```

### Expected Results

| Tool | Theorems | VCs | Errors | Admits |
|------|----------|-----|--------|--------|
| Verus | 105 | 242 | 0 | 0 |
| Coq | 347 | N/A | 0 | 0 |
| **Combined** | **452** | **242** | **0** | **0** |

---

## Coq → Rocq Rebranding

The Coq Proof Assistant was officially renamed to **The Rocq Prover** with
version 9.0 (March 2025). This affects tooling, package names, and namespaces.

### Current Status (January 2026)

| Package Source | Coq 8.18 | Rocq 9.0 | Rocq 9.1 | Status |
|----------------|----------|----------|----------|--------|
| `opam.ocaml.org` (default) | `coq.8.18.0` ✅ | `rocq-core.9.0.0` ✅ | `rocq-core.9.1.0` ✅ | Working |
| `coq.inria.fr/opam/released` | N/A | N/A | N/A | **HTTP 503** |
| `rocq-prover.org/opam/released` | N/A | N/A | N/A | **HTTP 503** |

**Key Finding**: Both the old Coq and new Rocq dedicated opam repos return
HTTP 503 errors. However, core packages (`coq`, `rocq-core`, `rocq-stdlib`)
are available from the default `opam.ocaml.org` repo. MetaCoq/MetaRocq and
coq-equations are NOT available there, requiring GitHub source pins or builds.

### Migration Path

When migrating from Coq 8.18 to Rocq 9.x, the following changes are required:

| Area | Coq 8.18 (Current) | Rocq 9.x (Future) |
|------|--------------------|--------------------|
| Install command | `apt-get install coq coq-theories` | `opam pin add rocq-prover 9.0.0` |
| Standard library | `From Coq Require Import Reals.` | `From Stdlib Require Import Reals.` |
| MetaCoq import | `From MetaCoq.Erasure ...` | `From MetaRocq.Erasure ...` |
| Build command | `coq_makefile` | `rocq makefile` (compat shim available) |
| Binary | `coqc` | `rocq` (coqc compat shim via `coq-core`) |
| MetaCoq package | `MetaCoq/metacoq` (coq-8.18 branch) | `MetaRocq/metarocq` (9.0/9.1 branch) |
| MetaCoq opam | Build from source | `opam install rocq-metarocq` (when repo stable) |

### When to Migrate

**Migrate to Rocq 9.x when ALL conditions are met:**
1. `rocq-prover.org/opam/released` repo is stable (no HTTP 503)
2. `rocq-metarocq` opam package is available for target version
3. `rocq-equations` opam package is available for target version
4. All 452 theorems verified to compile with Rocq 9.x

**Until then**: Continue using Coq 8.18 with MetaCoq built from source.

---

## Troubleshooting

### Coq opam repository HTTP 503

**Symptom**: `opam repo add coq-released https://coq.inria.fr/opam/released`
returns HTTP 503 or connection timeout.

**Cause**: Both old (`coq.inria.fr`) and new (`rocq-prover.org`) Coq/Rocq opam
repos are periodically unavailable. This is an infrastructure issue affecting
the entire Coq/Rocq ecosystem, not specific to any version.

**Solution**: Pin packages directly from GitHub:

```bash
# coq-equations
opam pin add coq-equations \
  "git+https://github.com/mattam82/Coq-Equations.git#v1.3-8.18" --yes

# MetaCoq (build from source instead)
git clone --branch coq-8.18 https://github.com/MetaCoq/metacoq.git /tmp/metacoq
```

### Missing coq-theories

**Symptom**: `Error: Cannot find library Reals in loadpath`

**Cause**: `apt-get install coq` does not include the standard library.

**Solution**: `sudo apt-get install -y coq-theories`

### libgmp-dev missing

**Symptom**: `zarith` installation fails during MetaCoq build.

**Cause**: GMP development headers not installed.

**Solution**: `sudo apt-get install -y libgmp-dev`

### Coq `by` keyword conflict

**Symptom**: `Syntax error: [constr:operconstr] expected` in proof scripts
using variable name `by`.

**Cause**: `by` is a reserved keyword in Coq 8.18.

**Solution**: Use `by0` or `b_y` as variable name instead.

### MetaCoq "not found" after build

**Symptom**: `Error: Cannot find library MetaCoq.ErasurePlugin in loadpath`

**Cause**: MetaCoq was built but not installed.

**Solution**: Run `make install` in the MetaCoq directory, or add the local
build paths:

```bash
coqc -R /tmp/metacoq/erasure-plugin/theories MetaCoq.ErasurePlugin \
     -R /tmp/metacoq/erasure/theories MetaCoq.Erasure \
     -R /tmp/metacoq/template-pcuic/theories MetaCoq.TemplatePCUIC \
     -R /tmp/metacoq/pcuic/theories MetaCoq.PCUIC \
     -R /tmp/metacoq/template-coq/theories MetaCoq.Template \
     -R /tmp/metacoq/common/theories MetaCoq.Common \
     -R /tmp/metacoq/utils/theories MetaCoq.Utils \
     -I /tmp/metacoq/template-coq \
     your_file.v
```

### f_equal causes exponential blowup on large records

**Symptom**: `f_equal` on 16-field Mat4 creates nested terms causing
`lra`/`ring` to time out (30+ minutes).

**Solution**: Use `apply mat4_eq` instead of `f_equal`; this processes
fields independently. See Mat4_Proofs.v for examples.

### `ring` times out on 16 simultaneous polynomial identities

**Symptom**: A single `ring` invocation on a 16-field record equality
times out.

**Solution**: Decompose into 16 component lemmas, each proven with `ring`
separately, then combine. See Mat4_Compute.v for the pattern.

### Never use `simpl` before `ring` on Z multiplication

**Symptom**: `ring` fails after `simpl` on expressions like `1 * x`.

**Cause**: `simpl` reduces Z constants to match expressions that `ring`
cannot handle.

**Solution**: Use `Z.mul_1_l` or `Z.mul_0_l` directly; omit `simpl` before
`ring` proofs.

---

## Architecture Reference

### File Organization

```
crates/rource-math/proofs/
  |-- vec2_proofs.rs          # Verus: Vec2 (23 theorems, 53 VCs)
  |-- vec3_proofs.rs          # Verus: Vec3 (24 theorems, 68 VCs)
  |-- vec4_proofs.rs          # Verus: Vec4 (22 theorems, 68 VCs)
  |-- mat3_proofs.rs          # Verus: Mat3 (18 theorems, 26 VCs)
  |-- mat4_proofs.rs          # Verus: Mat4 (18 theorems, 27 VCs)
  |
  +-- coq/
       |-- Vec2.v             # Layer 1: R-based specification
       |-- Vec3.v             # Layer 1: R-based specification
       |-- Vec4.v             # Layer 1: R-based specification
       |-- Mat3.v             # Layer 1: R-based specification
       |-- Mat4.v             # Layer 1: R-based specification
       |-- Vec2_Proofs.v      # Layer 1: Algebraic proofs (R)
       |-- Vec3_Proofs.v      # Layer 1: Algebraic proofs (R)
       |-- Vec4_Proofs.v      # Layer 1: Algebraic proofs (R)
       |-- Mat3_Proofs.v      # Layer 1: Algebraic proofs (R)
       |-- Mat4_Proofs.v      # Layer 1: Algebraic proofs (R)
       |-- Complexity.v       # Layer 1: O(1) complexity bounds
       |-- Vec2_Compute.v     # Layer 2: Z-based (extractable)
       |-- Vec3_Compute.v     # Layer 2: Z-based (extractable)
       |-- Vec4_Compute.v     # Layer 2: Z-based (extractable)
       |-- Mat3_Compute.v     # Layer 2: Z-based (extractable)
       |-- Mat4_Compute.v     # Layer 2: Z-based (extractable)
       |-- Vec2_Extract.v     # Layer 3: Individual extraction
       |-- Vec3_Extract.v     # Layer 3: Individual extraction
       |-- Vec4_Extract.v     # Layer 3: Individual extraction
       |-- Mat3_Extract.v     # Layer 3: Individual extraction
       |-- Mat4_Extract.v     # Layer 3: Individual extraction
       |-- RourceMath_Extract.v  # Layer 3: Unified extraction
       |
       |-- vec2_extracted.ml  # Generated: individual OCaml
       |-- vec3_extracted.ml  # Generated: individual OCaml
       |-- vec4_extracted.ml  # Generated: individual OCaml
       |-- mat3_extracted.ml  # Generated: individual OCaml
       |-- mat4_extracted.ml  # Generated: individual OCaml
       |-- rource_math_extracted.ml  # Generated: unified OCaml
       |-- test_extracted.ml  # Test driver for extracted code
```

### Tactic Selection Guide (Coq)

| Tactic | Use Case | Example |
|--------|----------|---------|
| `ring` | Polynomial identities (commutativity, associativity, distributivity) | `a * b = b * a` |
| `lra` | Linear real arithmetic (inequalities, non-negative squares) | `0 <= x * x` |
| `lia` | Linear integer arithmetic (Z bounds, complexity proofs) | `n >= 0` |
| `reflexivity` | Structural equality (identity proofs) | `id + v = v` |
| `apply XY_eq` | Record equality decomposition (Mat3, Mat4) | 9 or 16 fields |
| `f_equal` | Small records only (Vec2, Vec3, Vec4) | 2-4 fields |

**Never**: Use `f_equal` on Mat4 (16 fields = exponential blowup).
**Never**: Use `simpl` before `ring` on Z multiplication.
**Always**: Decompose Mat4 proofs into per-component lemmas.

---

*Last updated: 2026-01-29*
*Standard: PEER REVIEWED PUBLISHED ACADEMIC*
*452 formally verified theorems (Verus: 105, Coq: 347)*
*Current: Coq 8.18 + MetaCoq (from source) | Future: Rocq 9.x + MetaRocq (when opam repos stabilize)*
