FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y \
    curl git cmake gcc g++ python3 python3-pip \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

# Copy Lean project
WORKDIR /app/lean
COPY lean/lean-toolchain .
COPY lean/lakefile.lean .
COPY lean/HybridVerify/ HybridVerify/

# Build and cache Mathlib
RUN lake update && lake exe cache get && lake build

# Copy Python code
WORKDIR /app
COPY python/ python/
COPY pyproject.toml .
COPY requirements.txt .

RUN pip3 install --break-system-packages -r requirements.txt

ENTRYPOINT ["python3", "-m", "python.cli"]
