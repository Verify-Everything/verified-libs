# Dev container with every prover pinned by pipeline/toolchain/versions.toml.
# Works on macOS (Apple silicon runs it under emulation; Aeneas ships x86_64/aarch64 Linux only).
FROM ubuntu:24.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git python3 python3-pip build-essential zstd xz-utils sudo \
    && rm -rf /var/lib/apt/lists/*
RUN useradd -m -s /bin/bash dev && echo 'dev ALL=(ALL) NOPASSWD:ALL' > /etc/sudoers.d/dev
USER dev
RUN curl -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain none \
 && curl -sSfL https://releases.nixos.org/nix/nix-2.31.2/install | sh -s -- --no-daemon
ENV PATH=/home/dev/.vpipe/bin:/home/dev/.vpipe/aeneas:/home/dev/.elan/bin:/home/dev/.cargo/bin:/home/dev/.nix-profile/bin:$PATH
WORKDIR /workspaces
