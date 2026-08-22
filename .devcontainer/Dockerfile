FROM qmcgaw/latexdevcontainer:latest-full@sha256:4211ea058ce0215c441597670d2c7c80cc395d03c09466b340125032cf1da27d

LABEL org.opencontainers.image.description="Mathematics textbook toolchain (TeX Live 2026)"

ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.19.0
ARG ELAN_VERSION=4.2.3
ARG RUFF_VERSION=0.12.10

ENV ELAN_HOME=/usr/local/elan
ENV PATH="${ELAN_HOME}/bin:${PATH}"

RUN apt-get update && \
  DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
  curl \
  ghostscript \
  libgl1-mesa-glx \
  make \
  patch \
  python3 \
  python3-yaml \
  ripgrep \
  tree \
  && rm -rf /var/lib/apt/lists/*

RUN architecture="$(dpkg --print-architecture)" && \
  case "$architecture" in \
    amd64) elan_target=x86_64-unknown-linux-gnu ;; \
    arm64) elan_target=aarch64-unknown-linux-gnu ;; \
    *) echo "Unsupported architecture: $architecture" >&2; exit 1 ;; \
  esac && \
  elan_release="https://github.com/leanprover/elan/releases/download/v${ELAN_VERSION}" && \
  curl -fsSL \
    "${elan_release}/elan-${elan_target}.tar.gz" \
    | tar -xz -C /tmp elan-init && \
  /tmp/elan-init -y --no-modify-path --default-toolchain none && \
  rm /tmp/elan-init

RUN architecture="$(dpkg --print-architecture)" && \
  case "$architecture" in \
    amd64) ruff_target=x86_64-unknown-linux-gnu ;; \
    arm64) ruff_target=aarch64-unknown-linux-gnu ;; \
    *) echo "Unsupported architecture: $architecture" >&2; exit 1 ;; \
  esac && \
  ruff_release="https://github.com/astral-sh/ruff/releases/download/${RUFF_VERSION}" && \
  mkdir /tmp/ruff && \
  curl -fsSL "${ruff_release}/ruff-${ruff_target}.tar.gz" \
    | tar -xz -C /tmp/ruff --strip-components=1 && \
  install /tmp/ruff/ruff /usr/local/bin/ruff && \
  rm -rf /tmp/ruff

RUN elan toolchain install "$LEAN_TOOLCHAIN" && \
  elan default "$LEAN_TOOLCHAIN"

COPY scripts/check-toolchain.sh /workspace/scripts/check-toolchain.sh
WORKDIR /workspace
RUN lualatex --version | head -n1 | grep -F 'TeX Live 2026' && \
  ./scripts/check-toolchain.sh

ENTRYPOINT []
