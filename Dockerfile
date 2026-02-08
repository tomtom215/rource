# Rource - Software Version Control Visualization
# Multi-stage build with musl static linking for zero OS-level CVEs

# =============================================================================
# Build stage - Compile a fully static Rust binary using musl
# =============================================================================
# Alpine provides musl libc by default, producing fully static binaries
# that require NO shared libraries at runtime.
FROM rust:1.93-alpine AS builder

# Install build dependencies:
#   musl-dev   - musl C library headers (required for libc crate)
#   pkgconf    - pkg-config implementation (for crates using pkg-config)
RUN apk add --no-cache musl-dev pkgconf

WORKDIR /build

# Copy manifests first for better layer caching
COPY Cargo.toml Cargo.lock ./
COPY crates/rource-math/Cargo.toml crates/rource-math/
COPY crates/rource-core/Cargo.toml crates/rource-core/
COPY crates/rource-vcs/Cargo.toml crates/rource-vcs/
COPY crates/rource-render/Cargo.toml crates/rource-render/
COPY rource-cli/Cargo.toml rource-cli/
COPY rource-wasm/Cargo.toml rource-wasm/

# Create dummy source files for dependency compilation
RUN mkdir -p crates/rource-math/src && echo "pub fn dummy() {}" > crates/rource-math/src/lib.rs && \
    mkdir -p crates/rource-core/src && echo "pub fn dummy() {}" > crates/rource-core/src/lib.rs && \
    mkdir -p crates/rource-vcs/src && echo "pub fn dummy() {}" > crates/rource-vcs/src/lib.rs && \
    mkdir -p crates/rource-render/src && echo "pub fn dummy() {}" > crates/rource-render/src/lib.rs && \
    mkdir -p rource-cli/src && echo "fn main() {}" > rource-cli/src/main.rs && \
    mkdir -p rource-wasm/src && echo "pub fn dummy() {}" > rource-wasm/src/lib.rs

# Build dependencies only (this layer is cached)
# Note: Package name is "rource", not "rource-cli" (directory name)
# This step may fail due to dummy source files not satisfying all constraints,
# but it pre-compiles dependencies for faster subsequent builds.
RUN cargo build --release --package rource 2>&1 || echo "Dependency pre-build completed (errors expected with dummy sources)"

# Copy actual source code
COPY crates/ crates/
COPY rource-cli/ rource-cli/
COPY rource-wasm/ rource-wasm/

# Touch source files to invalidate the build cache for actual code
RUN touch crates/*/src/*.rs rource-cli/src/*.rs

# Build the actual application with optimizations
# Note: Package name is "rource", not "rource-cli" (directory name)
# On Alpine, cargo builds with musl by default, producing a static binary.
RUN cargo build --release --package rource && \
    strip /build/target/release/rource

# Verify the binary is statically linked (no shared library dependencies)
# ldd returns non-zero for static binaries ("not a dynamic executable")
RUN ! ldd /build/target/release/rource 2>&1 | grep -q "=>" && \
    echo "OK: Binary is statically linked (no dynamic library dependencies)" || \
    { echo "WARNING: Binary has dynamic dependencies:"; ldd /build/target/release/rource; }

# =============================================================================
# Runtime stage - Minimal static image (ZERO OS package CVEs)
# =============================================================================
# Using Google's static distroless base which contains NO C library at all.
# The musl-linked binary is fully self-contained and needs no shared libraries.
#
# static-debian13 contains ONLY:
#   - ca-certificates, tzdata, base-files, netbase
#   - NO glibc, NO libgcc, NO libstdc++, NO package manager, NO shell
#
# This eliminates ALL OS-level CVEs from C libraries (glibc, openssl, zlib,
# openldap, curl, pam, ncurses, util-linux, libtasn1, expat, git).
FROM gcr.io/distroless/static-debian13:nonroot AS runtime-static

# Copy the statically linked binary
COPY --from=builder /build/target/release/rource /usr/local/bin/rource

# Run as non-root user (distroless:nonroot already sets this up)
USER nonroot:nonroot
WORKDIR /home/nonroot

# Default command shows help
ENTRYPOINT ["/usr/local/bin/rource"]
CMD ["--help"]

# =============================================================================
# Alternative runtime stage - With git support (for repository analysis)
# =============================================================================
# Use Debian 13 Trixie (released August 2025, LTS until 2030)
# This variant has a larger attack surface due to OS packages.
# Only use when git CLI access is required inside the container.
FROM debian:trixie-slim AS runtime-with-git

# Security: Apply all available security updates
# Install only essential runtime dependencies with --no-install-recommends
RUN apt-get update && \
    apt-get upgrade -y && \
    apt-get install -y --no-install-recommends \
        ca-certificates \
        git \
    && rm -rf /var/lib/apt/lists/* \
    && apt-get clean \
    && rm -rf /var/cache/apt/archives/* \
    && rm -rf /tmp/* /var/tmp/*

# Create non-root user for security
RUN useradd --create-home --shell /bin/false --uid 1000 rource

# Copy the binary (musl static binary runs on any Linux)
COPY --from=builder /build/target/release/rource /usr/local/bin/rource

# Set ownership and permissions
RUN chmod 755 /usr/local/bin/rource && \
    chown root:root /usr/local/bin/rource

# Switch to non-root user
USER rource
WORKDIR /home/rource

# Default command shows help
ENTRYPOINT ["rource"]
CMD ["--help"]

# =============================================================================
# Default target - Static distroless for zero OS-level CVEs
# =============================================================================
# The default image uses static distroless with a musl-linked binary.
# This image contains ZERO C library packages and therefore has effectively
# ZERO OS-level CVEs. The musl-linked binary is fully self-contained.
#
# For git support, build with: --target runtime-with-git
#
# Usage:
#   Default (static):     docker build -t rource .
#   With git support:     docker build --target runtime-with-git -t rource:git .
FROM runtime-static AS runtime

# Metadata labels
LABEL org.opencontainers.image.title="Rource"
LABEL org.opencontainers.image.description="Software version control visualization tool"
LABEL org.opencontainers.image.url="https://github.com/tomtom215/rource"
LABEL org.opencontainers.image.source="https://github.com/tomtom215/rource"
LABEL org.opencontainers.image.licenses="GPL-3.0"
LABEL org.opencontainers.image.authors="Rource Contributors"
LABEL org.opencontainers.image.base.name="gcr.io/distroless/static-debian13"
LABEL org.opencontainers.image.version="0.1.0"
