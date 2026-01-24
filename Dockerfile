# Rource - Software Version Control Visualization
# Multi-stage build for minimal image size with security hardening

# =============================================================================
# Build stage - Compile the Rust binary
# =============================================================================
FROM rust:1.82-slim-bookworm AS builder

# Install build dependencies with security updates
RUN apt-get update && \
    apt-get upgrade -y && \
    apt-get install -y --no-install-recommends \
        pkg-config \
        libssl-dev \
    && rm -rf /var/lib/apt/lists/* \
    && apt-get clean

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
RUN cargo build --release --package rource && \
    strip /build/target/release/rource

# =============================================================================
# Runtime stage - Minimal secure image
# =============================================================================
# Using Google's distroless base with glibc for maximum security
# Only contains the runtime libraries needed to run the binary
FROM gcr.io/distroless/cc-debian12:nonroot AS runtime-distroless

# Copy the binary (distroless has no shell, so we use COPY directly)
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

# Copy the binary
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
# Default target - Use the version with git support
# =============================================================================
FROM runtime-with-git AS runtime

# Metadata labels
LABEL org.opencontainers.image.title="Rource"
LABEL org.opencontainers.image.description="Software version control visualization tool"
LABEL org.opencontainers.image.url="https://github.com/tomtom215/rource"
LABEL org.opencontainers.image.source="https://github.com/tomtom215/rource"
LABEL org.opencontainers.image.licenses="GPL-3.0"
LABEL org.opencontainers.image.authors="Rource Contributors"
LABEL org.opencontainers.image.base.name="debian:trixie-slim"
LABEL org.opencontainers.image.version="0.1.0"
