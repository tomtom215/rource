# Rource - Software Version Control Visualization
# Multi-stage build for minimal image size

# Build stage
FROM rust:1.82-slim-bookworm AS builder

# Install build dependencies
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

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
# Using explicit exit 0 instead of || true to be clear about intent.
RUN cargo build --release --package rource 2>&1 || echo "Dependency pre-build completed (errors expected with dummy sources)"

# Copy actual source code
COPY crates/ crates/
COPY rource-cli/ rource-cli/
COPY rource-wasm/ rource-wasm/

# Touch source files to invalidate the build cache for actual code
RUN touch crates/*/src/*.rs rource-cli/src/*.rs

# Build the actual application
# Note: Package name is "rource", not "rource-cli" (directory name)
RUN cargo build --release --package rource && \
    strip /build/target/release/rource

# Runtime stage - minimal image
FROM debian:bookworm-slim AS runtime

# Install runtime dependencies
RUN apt-get update && apt-get install -y \
    ca-certificates \
    git \
    && rm -rf /var/lib/apt/lists/*

# Create non-root user for security
RUN useradd --create-home --shell /bin/bash rource

# Copy the binary
COPY --from=builder /build/target/release/rource /usr/local/bin/rource

# Set ownership and permissions
RUN chmod 755 /usr/local/bin/rource

# Switch to non-root user
USER rource
WORKDIR /home/rource

# Default command shows help
ENTRYPOINT ["rource"]
CMD ["--help"]

# Metadata labels
LABEL org.opencontainers.image.title="Rource"
LABEL org.opencontainers.image.description="Software version control visualization tool"
LABEL org.opencontainers.image.url="https://github.com/tomtom215/rource"
LABEL org.opencontainers.image.source="https://github.com/tomtom215/rource"
LABEL org.opencontainers.image.licenses="GPL-3.0"
LABEL org.opencontainers.image.authors="Rource Contributors"
