# Recheck every Clazel proof on Linux x86-64, from a clean machine:
#
#   docker build --platform linux/amd64 -t clazel-verify .
#   docker run --rm --platform linux/amd64 clazel-verify
#
# The build installs the pinned toolchain with scripts/setup.sh; the run
# executes scripts/verify.sh (exit 0 = every check passed). On Apple Silicon
# this runs under emulation and is slow; Verus publishes no Linux arm64
# build, so linux/amd64 is required.

# Debian 13 (trixie), pinned by digest.
FROM debian:trixie-slim@sha256:a29215f6a35e51e22adffa17f89e9d2ef06214e64a2bad10d765c46aea49f11f

# setup.sh needs curl, unzip and tar; cargo needs a C toolchain to link, and
# libvulkan, which `clazel-sys` links (phase-5.md item 5.17b). The GPU tests draw
# on lavapipe (mesa-vulkan-drivers), Mesa's software Vulkan driver.
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl unzip gcc libc6-dev \
      libvulkan-dev mesa-vulkan-drivers \
 && rm -rf /var/lib/apt/lists/*

RUN useradd --create-home builder
USER builder
WORKDIR /home/builder/clazel

# rustup, at the pinned version, checked against scripts/checksums.txt.
COPY --chown=builder scripts/toolchains.env scripts/checksums.txt scripts/
RUN . scripts/toolchains.env \
 && name="rustup-init-$RUSTUP_VERSION-x86_64-unknown-linux-gnu" \
 && curl -fsSL -o /tmp/rustup-init \
      "https://static.rust-lang.org/rustup/archive/$RUSTUP_VERSION/x86_64-unknown-linux-gnu/rustup-init" \
 && want=$(awk -v f="$name" '$2 == f { print $1 }' scripts/checksums.txt) \
 && got=$(sha256sum /tmp/rustup-init | cut -d' ' -f1) \
 && [ -n "$want" ] && [ "$got" = "$want" ] \
 || { echo "rustup-init checksum mismatch: expected '$want', got '$got'" >&2; exit 1; } \
 ; chmod +x /tmp/rustup-init \
 && /tmp/rustup-init -y --no-modify-path --profile minimal --default-toolchain none \
 && rm /tmp/rustup-init
ENV PATH=/home/builder/.cargo/bin:$PATH

# The repository, then the pinned, checksummed proof toolchain.
COPY --chown=builder . .
# setup.sh also prebuilds Miri's sysroot, but a sysroot baked into an image
# layer is judged stale in a later container, and Miri then cannot replace it
# ("detected a concurrent sysroot build with different settings"). Drop it;
# each run builds its own (about a minute under emulation).
RUN scripts/setup.sh && rm -rf "$HOME/.cache/miri"

CMD ["scripts/verify.sh"]
