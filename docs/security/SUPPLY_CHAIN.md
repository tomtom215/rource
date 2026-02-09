# Supply Chain Security

**Status**: Active
**Task ID**: SEC-3
**Last Updated**: 2026-01-26

---

## Overview

This document describes the supply chain security measures implemented in Rource to ensure build integrity and artifact authenticity.

## SLSA Compliance

Rource is configured for [SLSA (Supply-chain Levels for Software Artifacts)](https://slsa.dev/) Level 3 provenance (pending first release). The release workflow (`.github/workflows/release.yml`) includes SLSA provenance generation, but no releases have been published yet, so provenance has not been produced or verified in practice.

### SLSA Level 3 Requirements

| Requirement | Implementation | Configured | Executed |
|-------------|----------------|------------|----------|
| Build as code | GitHub Actions workflows | Yes | Pending first release |
| Signed provenance | slsa-github-generator | Yes | Pending first release |
| Provenance from build | Automatic attestation | Yes | Pending first release |
| Non-falsifiable provenance | Sigstore signing | Yes | Pending first release |
| Isolated build | GitHub-hosted runners | Yes | Pending first release |

### What SLSA Provenance Provides

1. **Build Integrity**: Cryptographic proof that artifacts were built from the stated source
2. **Tamper Evidence**: Detection of unauthorized modifications
3. **Reproducibility**: Information to recreate the build
4. **Audit Trail**: Complete build metadata

## Verifying Release Artifacts

### Verify SLSA Provenance

```bash
# Install slsa-verifier
go install github.com/slsa-framework/slsa-verifier/v2/cli/slsa-verifier@latest

# Download artifact and provenance
curl -LO https://github.com/tomtom215/rource/releases/download/v1.0.0/rource-linux-x86_64.tar.gz
curl -LO https://github.com/tomtom215/rource/releases/download/v1.0.0/rource-linux-x86_64.tar.gz.intoto.jsonl

# Verify provenance
slsa-verifier verify-artifact rource-linux-x86_64.tar.gz \
  --provenance-path rource-linux-x86_64.tar.gz.intoto.jsonl \
  --source-uri github.com/tomtom215/rource \
  --source-tag v1.0.0
```

### Verify GPG Signatures

> **Note**: GPG signing is conditional on the `GPG_PRIVATE_KEY` secret being
> configured in the repository. If the secret is not set, release artifacts
> will be published without GPG signatures. Check whether `.asc` files are
> present in the release assets before attempting verification.

```bash
# Import the Rource signing key
curl -sL https://github.com/tomtom215.gpg | gpg --import

# Download artifact and signature
curl -LO https://github.com/tomtom215/rource/releases/download/v1.0.0/rource-linux-x86_64.tar.gz
curl -LO https://github.com/tomtom215/rource/releases/download/v1.0.0/rource-linux-x86_64.tar.gz.asc

# Verify signature
gpg --verify rource-linux-x86_64.tar.gz.asc rource-linux-x86_64.tar.gz
```

### Verify SHA256 Checksums

```bash
# Download checksums file
curl -LO https://github.com/tomtom215/rource/releases/download/v1.0.0/checksums.txt

# Verify artifact
sha256sum -c checksums.txt --ignore-missing
```

## Build Provenance

### Provenance Contents

Each release includes an in-toto attestation with:

```json
{
  "_type": "https://in-toto.io/Statement/v0.1",
  "predicateType": "https://slsa.dev/provenance/v0.2",
  "subject": [
    {
      "name": "rource-linux-x86_64.tar.gz",
      "digest": {
        "sha256": "abc123..."
      }
    }
  ],
  "predicate": {
    "builder": {
      "id": "https://github.com/slsa-framework/slsa-github-generator/.github/workflows/generator_generic_slsa3.yml@refs/tags/v2.1.0"
    },
    "buildType": "https://github.com/slsa-framework/slsa-github-generator/generic@v1",
    "invocation": {
      "configSource": {
        "uri": "git+https://github.com/tomtom215/rource@refs/tags/v1.0.0",
        "digest": {
          "sha1": "..."
        },
        "entryPoint": ".github/workflows/release.yml"
      }
    }
  }
}
```

### Build Environment

| Property | Value |
|----------|-------|
| Builder | GitHub Actions |
| Runner | GitHub-hosted (ubuntu-latest, macos-*, windows-latest) |
| Signing | Sigstore Fulcio + Rekor |
| Provenance Format | in-toto SLSA v0.2 |

## Software Bill of Materials (SBOM)

Each release includes SBOMs in two formats:

### SPDX Format

```bash
# Download SBOM
curl -LO https://github.com/tomtom215/rource/releases/download/v1.0.0/sbom-spdx.json

# View with spdx-tools
spdx-tool verify sbom-spdx.json
```

### CycloneDX Format

```bash
# Download SBOM
curl -LO https://github.com/tomtom215/rource/releases/download/v1.0.0/sbom-cyclonedx.json

# Scan for vulnerabilities
cyclonedx-cli analyze --input-file sbom-cyclonedx.json
```

## Dependency Management

### Audit Process

```bash
# Weekly automated audit
cargo audit

# Manual security review
cargo deny check
```

### Dependency Policy

| Policy | Requirement |
|--------|-------------|
| Minimal dependencies | Only include necessary crates |
| Security audit | Weekly `cargo audit` in CI |
| License review | All dependencies must have OSI-approved licenses |
| MSRV | Maintain Minimum Supported Rust Version |

### Current Dependencies

Core dependencies are checked via `cargo audit` (automated CVE scanning) and kept minimal. Note: "cargo-audit checked" means no known CVEs were found by the automated advisory database scan; it does not indicate a manual source-level security audit.

| Dependency | Purpose | Audit Status |
|------------|---------|--------------|
| fontdue | Font rendering | cargo-audit checked (no known CVEs) |
| regex-lite | Log parsing | cargo-audit checked (no known CVEs) |
| chrono | Date handling | cargo-audit checked (no known CVEs) |
| wasm-bindgen | WASM bindings | cargo-audit checked (no known CVEs) |

## Security Contacts

For security vulnerabilities, see [SECURITY.md](../../SECURITY.md).

## References

- [SLSA Framework](https://slsa.dev/)
- [in-toto Attestation](https://in-toto.io/)
- [Sigstore](https://sigstore.dev/)
- [SPDX Specification](https://spdx.dev/)
- [CycloneDX Specification](https://cyclonedx.org/)

---

*Last updated: 2026-01-27*
*Task: SEC-3 Supply Chain Security (SLSA)*
