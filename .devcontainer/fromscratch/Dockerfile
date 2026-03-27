FROM ubuntu:22.04

# Prevent interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# Set timezone to avoid /etc/localtime errors with Lean server
ENV TZ=UTC

# Install system dependencies
RUN apt-get update && apt-get install -y \
    git \
    curl \
    wget \
    ca-certificates \
    build-essential \
    python3 \
    python3-pip \
    libgmp-dev \
    tzdata \
    && ln -snf /usr/share/zoneinfo/$TZ /etc/localtime \
    && echo $TZ > /etc/timezone \
    && rm -rf /var/lib/apt/lists/*

# Create a non-root user for development
RUN useradd -m -s /bin/bash lean

# Switch to lean user for elan installation
USER lean
WORKDIR /home/lean

# Install elan with the specific Lean toolchain version
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:v4.26.0

# Add elan to PATH for the lean user
ENV PATH="/home/lean/.elan/bin:${PATH}"

# Verify installation
RUN lean --version && lake --version

# Set up workspace directory
WORKDIR /workspace

# Copy project files including .lake directory
# Context is set to ".." in devcontainer.json, so this copies from project root
COPY --chown=lean:lean . /workspace

CMD ["/bin/bash"]
