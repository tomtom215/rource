# Security Policy

## Supported Versions

| Version | Supported          |
|---------|--------------------|
| 1.x.x   | :white_check_mark: |
| < 1.0   | :x:                |

## Reporting a Vulnerability

**Please do NOT report security vulnerabilities through public GitHub issues.**

Instead, please report security vulnerabilities via GitHub Security Advisories:

https://github.com/tomtom215/rource/security/advisories/new

### What to Include

When reporting a vulnerability, please include:

1. **Description**: A clear description of the vulnerability
2. **Impact**: What an attacker could achieve by exploiting it
3. **Reproduction Steps**: Step-by-step instructions to reproduce the issue
4. **Affected Versions**: Which versions are affected (if known)
5. **Suggested Fix**: If you have ideas for how to fix it (optional)

### Response Timeline

| Stage | Timeline |
|-------|----------|
| Acknowledgment | Within 48 hours |
| Initial Assessment | Within 7 days |
| Fix for Critical | Within 7 days |
| Fix for High | Within 30 days |
| Fix for Medium/Low | Within 90 days |

We will keep you informed of progress toward resolving the issue.

## Security Measures

Rource employs multiple security measures to protect users:

### Dependency Security

- **Weekly Audits**: Automated `cargo audit` runs weekly via CI
- **Dependabot**: Automatic dependency updates for security patches
- **Minimal Dependencies**: We minimize external dependencies to reduce attack surface

### Code Security

- **Minimal Unsafe Code**: Only 1 unsafe block in the entire codebase, with documented safety invariants
- **Fuzzing**: VCS parsers are fuzzed to catch parsing vulnerabilities
- **Static Analysis**: All code passes `cargo clippy` with `-D warnings`

### Build Security

- **Reproducible Builds**: Release builds are reproducible
- **CI/CD Only**: All releases are built through GitHub Actions, not local machines
- **Checksum Verification**: Release artifacts include SHA256 checksums

### WASM Security

- **Sandboxed Execution**: WASM runs in browser sandbox with no filesystem access
- **No Network Access**: WASM module cannot make network requests directly
- **Memory Safe**: Rust's memory safety guarantees apply to WASM builds

## Security-Relevant Configuration

### Environment Variables

No security-sensitive environment variables are used. All configuration is optional and non-sensitive.

### File Permissions

Rource only reads files explicitly provided by the user:
- Git log files (read-only)
- Repository directories (read-only, for git log generation)
- Avatar images (read-only, optional)

Rource writes files only when explicitly requested:
- Screenshot exports (user-specified path)
- Video frame exports (user-specified directory)

## Known Limitations

### Input Parsing

VCS log parsers handle untrusted input. While we fuzz these parsers, extremely malformed input could potentially cause:
- High memory usage (for pathological inputs)
- High CPU usage (for deeply nested paths)

**Mitigation**: Use `--max-commits` to limit input size when visualizing untrusted repositories.

### WebGL/WebGPU

Browser rendering backends execute shader code. Rource only uses standard, well-tested shader operations, but browser bugs could theoretically affect rendering.

**Mitigation**: Rource includes a software rendering fallback that doesn't use GPU shaders.

## Security Contacts

For security issues, use GitHub Security Advisories (preferred) or contact the maintainers through GitHub.

## Acknowledgments

We appreciate responsible disclosure of security vulnerabilities. Contributors who report valid security issues will be acknowledged in release notes (unless they prefer to remain anonymous).

---

*Last updated: 2026-01-26*
