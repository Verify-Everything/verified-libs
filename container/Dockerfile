# Pinned toolchain image for admission gate 9 (STANDARDS.md): CI re-checks every entry from clean
# inside this image, pinned by digest in toolchain/versions.toml [container].
# It holds the tools only (Aeneas, Charon, Rust nightly, Lean, mathlib, Frama-C, Why3, Z3, CVC5,
# CBMC, plus qemu and an aarch64 cross gcc for crosscheck models); the repo is mounted at /work at run time. About 19 GB unpacked. Build from the repo root:
#   docker build -f container/Dockerfile -t verified-libs-toolchain .
# Behind a TLS-intercepting proxy, pass its CA as a build secret (not baked into the image):
#   docker build --secret id=ca,src=/path/to/ca.pem --build-arg HTTPS_PROXY ...
FROM ubuntu:24.04@sha256:68ee22004a9109b44973313b02ff7b1de250f1de0f5ecb628d73f579aaff33ac
LABEL org.opencontainers.image.source="https://github.com/Verify-Everything/verified-libs" \
      org.opencontainers.image.description="Pinned verification toolchain for verified-libs (gate 9)"
ARG DEBIAN_FRONTEND=noninteractive
# APT_HTTPS=1 fetches Ubuntu packages over https (for proxies that refuse plain http).
ARG APT_HTTPS=0
RUN --mount=type=secret,id=ca,required=false,mode=0444 \
    if [ -s /run/secrets/ca ]; then \
      printf 'Acquire::https::CAInfo "/run/secrets/ca";\n' > /etc/apt/apt.conf.d/99ca; fi; \
    if [ "$APT_HTTPS" = 1 ]; then sed -i 's#http://#https://#' /etc/apt/sources.list.d/ubuntu.sources; fi; \
    apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git python3 build-essential zstd xz-utils bash-completion \
      qemu-user-static gcc-aarch64-linux-gnu libc6-dev-arm64-cross \
    && rm -rf /var/lib/apt/lists/* /etc/apt/apt.conf.d/99ca
# uid 1001 matches the GitHub runner user, so the mounted checkout stays writable.
RUN useradd -m -u 1001 -s /bin/bash vpipe && mkdir -m 0755 /nix && chown vpipe /nix /home/vpipe
USER vpipe
ENV HOME=/home/vpipe USER=vpipe \
    VPIPE_HOME=/home/vpipe/.vpipe VPIPE_WORK=/home/vpipe/vpipe-work \
    PATH=/home/vpipe/.vpipe/bin:/home/vpipe/.vpipe/aeneas:/home/vpipe/.elan/bin:/home/vpipe/.cargo/bin:/home/vpipe/.nix-profile/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
COPY --chown=vpipe container/with-ca.sh /usr/local/bin/with-ca
RUN --mount=type=secret,id=ca,required=false,uid=1001 with-ca bash -c '\
    curl -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain none --profile minimal \
 && curl -sSfL https://releases.nixos.org/nix/nix-2.31.2/install | sh -s -- --no-daemon \
 && mkdir -p ~/.config/nix && echo "experimental-features = nix-command flakes" > ~/.config/nix/nix.conf'
# The engine is needed only to install and self-test the tools; it is removed afterwards.
COPY --chown=vpipe . /home/vpipe/src
RUN --mount=type=secret,id=ca,required=false,uid=1001 with-ca bash -c '\
    cd ~/src && bash install.sh --yes --agents none --tools lean,framac,cbmc --no-path \
 && { python3 bin/vkit.py doctor --json > ~/toolchain.json || true; } \
 && python3 self/gate.py --full \
 && cd ~ && rm -rf ~/src ~/vpipe-work ~/.cargo/registry ~/.vpipe/bin/vkit ~/.vpipe/bin/vpipe ~/.cache \
      ~/.rustup/toolchains/*/share/doc \
 && for d in ~/.vpipe/aeneas-*; do [ "$d" -ef ~/.vpipe/aeneas ] || rm -rf "$d"; done \
 && nix store gc' \
 && git config --global --add safe.directory '*'
WORKDIR /work
