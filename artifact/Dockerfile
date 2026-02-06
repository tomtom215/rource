# Dockerfile for CPP 2027 Artifact Evaluation
#
# Reproduces all verification results for:
#   "Triple-Verified: Hybrid Formal Verification of a Production Rust Math
#    Library using Verus, Coq, and Kani"
#
# Usage:
#   docker build -t rource-artifact -f artifact/Dockerfile .
#   docker run --rm rource-artifact            # Run all verification
#   docker run --rm rource-artifact --quick    # Quick subset (~10 min)
#   docker run --rm rource-artifact --tests    # Rust tests only (~2 min)
#   docker run --rm rource-artifact --coq      # Coq proofs only (~2 min)
#   docker run --rm rource-artifact --verus    # Verus proofs only (~1 min)
#
# Expected output: All tools report zero errors/admits/failures.
# Expected time:   ~30 minutes full, ~10 minutes quick subset.
#
# Tool versions pinned for reproducibility:
#   Rust:  1.93 (MSRV)
#   Coq:   8.18.0
#   Flocq: 4.1.3
#   Verus: 0.2026.01.23+
#   Kani:  0.67.0

FROM rust:1.93-slim-trixie

# Metadata
LABEL org.opencontainers.image.title="rource-math Artifact Evaluation"
LABEL org.opencontainers.image.description="Reproducibility artifact for CPP 2027"
LABEL org.opencontainers.image.source="https://github.com/tomtom215/rource"

# Install system dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    pkg-config \
    libssl-dev \
    opam \
    m4 \
    git \
    curl \
    wget \
    unzip \
    python3 \
    time \
    && rm -rf /var/lib/apt/lists/*

# ============================================================================
# Stage 1: Coq + Flocq (opam-based)
# ============================================================================
RUN opam init --disable-sandboxing --auto-setup -y && \
    eval $(opam env) && \
    opam install -y coq.8.18.0 && \
    opam install -y coq-flocq.4.1.3

# ============================================================================
# Stage 2: Verus (pre-built binary)
# ============================================================================
RUN mkdir -p /tmp/verus && \
    cd /tmp/verus && \
    VERUS_URL="https://github.com/verus-lang/verus/releases/latest/download/verus-x86_64-unknown-linux-gnu.tar.gz" && \
    curl -fsSL "$VERUS_URL" -o verus.tar.gz && \
    tar xzf verus.tar.gz && \
    chmod +x verus && \
    rm verus.tar.gz

# ============================================================================
# Stage 3: Kani (cargo install)
# ============================================================================
RUN cargo install --locked kani-verifier && \
    cargo kani setup

# ============================================================================
# Stage 4: Copy project source
# ============================================================================
WORKDIR /workspace
COPY . /workspace/

RUN chmod +x /workspace/artifact/reproduce-all.sh

# Set up opam environment in shell
RUN echo 'eval $(opam env)' >> /root/.bashrc

ENTRYPOINT ["/workspace/artifact/reproduce-all.sh"]
CMD []
