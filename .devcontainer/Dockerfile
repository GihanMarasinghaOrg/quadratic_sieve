# .devcontainer/Dockerfile
FROM debian:bookworm-slim

# Install dependencies
RUN apt-get update && apt-get install -y \
    curl git unzip wget build-essential \
    && apt-get clean && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# Ensure the path includes elan binaries
ENV PATH="/root/.elan/bin:${PATH}"

# Preinstall Lean dependencies (optional but useful)
COPY . /workspaces/project
WORKDIR /workspaces/project
RUN lake exe cache get || true && lake build || true