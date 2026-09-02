FROM debian:bookworm-slim@sha256:88200866dfff7ea7f5cbcb6ec7c8a701889efe6fe859fe64d6990e4b07ea4171 AS python-builder

COPY config/toolchain.env /tmp/toolchain.env
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    build-essential ca-certificates curl libbz2-dev libffi-dev libgdbm-dev \
    liblzma-dev libncursesw5-dev libreadline-dev libsqlite3-dev libssl-dev \
    tk-dev uuid-dev xz-utils zlib1g-dev \
  && set -a && . /tmp/toolchain.env && set +a \
  && curl -fsSL -o /tmp/python.tar.xz \
    "https://www.python.org/ftp/python/${PYTHON_VERSION}/Python-${PYTHON_VERSION}.tar.xz" \
  && echo "${PYTHON_SHA256}  /tmp/python.tar.xz" | sha256sum --check - \
  && mkdir /tmp/python \
  && tar -xJf /tmp/python.tar.xz -C /tmp/python --strip-components=1 \
  && cd /tmp/python \
  && ./configure --prefix=/opt/python --enable-optimizations --with-lto --with-ensurepip=install \
  && make -j2 && make install \
  && /opt/python/bin/python3 -m pip install --disable-pip-version-check \
    --no-cache-dir "PyYAML==${PYYAML_VERSION}"

FROM debian:bookworm-slim@sha256:88200866dfff7ea7f5cbcb6ec7c8a701889efe6fe859fe64d6990e4b07ea4171 AS tool-downloader

COPY config/toolchain.env /tmp/toolchain.env
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y \
    --no-install-recommends ca-certificates curl \
  && set -a && . /tmp/toolchain.env && set +a \
  && architecture="$(dpkg --print-architecture)" \
  && case "$architecture" in \
    amd64) elan_target=x86_64-unknown-linux-gnu; elan_sha256="$ELAN_SHA256_AMD64"; \
      ruff_target=x86_64-unknown-linux-gnu; ruff_sha256="$RUFF_SHA256_AMD64"; \
      shfmt_sha256="$SHFMT_SHA256_AMD64"; latexindent_asset=latexindent-linux; \
      latexindent_sha256="$LATEXINDENT_SHA256_AMD64"; docker_target=x86_64; \
      docker_sha256="$DOCKER_SHA256_AMD64"; buildx_target=amd64; \
      buildx_sha256="$BUILDX_SHA256_AMD64"; compose_target=x86_64; \
      compose_sha256="$COMPOSE_SHA256_AMD64"; gh_target=amd64; \
      gh_sha256="$GH_SHA256_AMD64" ;; \
    arm64) elan_target=aarch64-unknown-linux-gnu; elan_sha256="$ELAN_SHA256_ARM64"; \
      ruff_target=aarch64-unknown-linux-gnu; ruff_sha256="$RUFF_SHA256_ARM64"; \
      shfmt_sha256="$SHFMT_SHA256_ARM64"; latexindent_asset=latexindent-linux-arm64; \
      latexindent_sha256="$LATEXINDENT_SHA256_ARM64"; docker_target=aarch64; \
      docker_sha256="$DOCKER_SHA256_ARM64"; buildx_target=arm64; \
      buildx_sha256="$BUILDX_SHA256_ARM64"; compose_target=aarch64; \
      compose_sha256="$COMPOSE_SHA256_ARM64"; gh_target=arm64; \
      gh_sha256="$GH_SHA256_ARM64" ;; \
    *) echo "Unsupported architecture: $architecture" >&2; exit 1 ;; esac \
  && mkdir -p /out/bin /out/lib/docker/cli-plugins /tmp/ruff /tmp/gh \
  && curl -fsSL -o /tmp/elan.tgz "https://github.com/leanprover/elan/releases/download/v${ELAN_VERSION}/elan-${elan_target}.tar.gz" \
  && echo "${elan_sha256}  /tmp/elan.tgz" | sha256sum --check - \
  && tar -xzf /tmp/elan.tgz -C /out/bin elan-init \
  && curl -fsSL -o /tmp/ruff.tgz "https://github.com/astral-sh/ruff/releases/download/${RUFF_VERSION}/ruff-${ruff_target}.tar.gz" \
  && echo "${ruff_sha256}  /tmp/ruff.tgz" | sha256sum --check - \
  && tar -xzf /tmp/ruff.tgz -C /tmp/ruff --strip-components=1 \
  && install /tmp/ruff/ruff /out/bin/ruff \
  && curl -fsSL -o /tmp/shfmt "https://github.com/mvdan/sh/releases/download/v${SHFMT_VERSION}/shfmt_v${SHFMT_VERSION}_linux_${architecture}" \
  && echo "${shfmt_sha256}  /tmp/shfmt" | sha256sum --check - \
  && install /tmp/shfmt /out/bin/shfmt \
  && curl -fsSL -o /tmp/latexindent "https://github.com/cmhughes/latexindent.pl/releases/download/V${LATEXINDENT_VERSION}/${latexindent_asset}" \
  && echo "${latexindent_sha256}  /tmp/latexindent" | sha256sum --check - \
  && install /tmp/latexindent /out/bin/latexindent \
  && curl -fsSL -o /tmp/docker.tgz "https://download.docker.com/linux/static/stable/${docker_target}/docker-${DOCKER_VERSION}.tgz" \
  && echo "${docker_sha256}  /tmp/docker.tgz" | sha256sum --check - \
  && tar -xzf /tmp/docker.tgz -C /tmp docker/docker --strip-components=1 \
  && install /tmp/docker /out/bin/docker \
  && curl -fsSL -o /tmp/buildx "https://github.com/docker/buildx/releases/download/v${BUILDX_VERSION}/buildx-v${BUILDX_VERSION}.linux-${buildx_target}" \
  && echo "${buildx_sha256}  /tmp/buildx" | sha256sum --check - \
  && install /tmp/buildx /out/lib/docker/cli-plugins/docker-buildx \
  && curl -fsSL -o /tmp/compose "https://github.com/docker/compose/releases/download/v${COMPOSE_VERSION}/docker-compose-linux-${compose_target}" \
  && echo "${compose_sha256}  /tmp/compose" | sha256sum --check - \
  && install /tmp/compose /out/lib/docker/cli-plugins/docker-compose \
  && curl -fsSL -o /tmp/gh.tgz "https://github.com/cli/cli/releases/download/v${GH_VERSION}/gh_${GH_VERSION}_linux_${gh_target}.tar.gz" \
  && echo "${gh_sha256}  /tmp/gh.tgz" | sha256sum --check - \
  && tar -xzf /tmp/gh.tgz -C /tmp/gh --strip-components=1 \
  && install /tmp/gh/bin/gh /out/bin/gh

FROM debian:bookworm-slim@sha256:88200866dfff7ea7f5cbcb6ec7c8a701889efe6fe859fe64d6990e4b07ea4171
LABEL org.opencontainers.image.description="Mathematics textbook toolchain"
ENV DEBIAN_FRONTEND=noninteractive
ENV ELAN_HOME=/usr/local/elan
ENV PATH="/opt/python/bin:/usr/local/elan/bin:/usr/local/bin:/usr/local/texlive/2026/bin/x86_64-linux:/usr/local/texlive/2026/bin/aarch64-linux:${PATH}"
WORKDIR /workspace
COPY config/toolchain.env /workspace/config/toolchain.env
RUN apt-get update && apt-get install -y --no-install-recommends \
    bash build-essential ca-certificates curl ghostscript git git-man less libbz2-1.0 \
    libffi8 libgdbm-compat4 libgdbm6 libgl1-mesa-glx liblzma5 libncursesw6 \
    libreadline8 libsqlite3-0 libssl3 libtcl8.6 libtk8.6 libuuid1 locales \
    man-db nano openssh-client patch perl ripgrep shellcheck tk tree tzdata \
    xz-utils zlib1g zsh \
  && echo 'en_US.UTF-8 UTF-8' > /etc/locale.gen \
  && locale-gen \
  && rm -rf /var/lib/apt/lists/*
ENV LANG=en_US.UTF-8
ENV LC_ALL=en_US.UTF-8
ENV SHELL=/bin/zsh
ENV EDITOR=nano
ENV TZ=Etc/UTC
ARG BASEDEVCONTAINER_SHELL_COMMIT=eed51b33f4fc5bcb6be2ee566402afeb7be47375
ARG OH_MY_ZSH_COMMIT=146461f7c6d95f4ba1220559d66eb113418b40a8
ARG POWERLEVEL10K_COMMIT=8a676a9157d2b0e00e88d06456ac7317f11c0317
RUN curl -fsSL -o /root/.zshrc \
      "https://raw.githubusercontent.com/qdm12/basedevcontainer/${BASEDEVCONTAINER_SHELL_COMMIT}/shell/.zshrc" \
  && echo 'fd04e2d7c6d9367b2b34d023a335dec44f2fe7b25d0997bbc8bfd0345f26c191  /root/.zshrc' \
    | sha256sum --check - \
  && sed -i -e '10,35d' -e 's|source ~/.zshrc-specific$|source ~/.zshrc-specific.sh|' /root/.zshrc \
  && curl -fsSL -o /root/.p10k.zsh \
      "https://raw.githubusercontent.com/qdm12/basedevcontainer/${BASEDEVCONTAINER_SHELL_COMMIT}/shell/.p10k.zsh" \
  && echo 'ba3e6c86226936f49a08f395fa585f54015958c3fa730fd7a79434b52c2bb724  /root/.p10k.zsh' \
    | sha256sum --check - \
  && git clone --filter=blob:none --no-checkout \
      https://github.com/ohmyzsh/ohmyzsh.git /root/.oh-my-zsh \
  && git -C /root/.oh-my-zsh checkout "$OH_MY_ZSH_COMMIT" \
  && git clone --filter=blob:none --no-checkout \
      https://github.com/romkatv/powerlevel10k.git \
      /root/.oh-my-zsh/custom/themes/powerlevel10k \
  && git -C /root/.oh-my-zsh/custom/themes/powerlevel10k \
      checkout "$POWERLEVEL10K_COMMIT" \
  && rm -rf /root/.oh-my-zsh/.git \
      /root/.oh-my-zsh/custom/themes/powerlevel10k/.git \
  && usermod --shell /bin/zsh root
COPY --from=python-builder /opt/python /opt/python
COPY --from=tool-downloader /out/bin/ /usr/local/bin/
COPY --from=tool-downloader /out/lib/docker/cli-plugins/ /usr/local/lib/docker/cli-plugins/
RUN set -a && . /workspace/config/toolchain.env && set +a \
  && repository="https://texlive.info/tlnet-archive/${TEXLIVE_ARCHIVE_DATE}/tlnet" \
  && curl -fsSL -o /tmp/install-tl.tgz "$repository/install-tl-unx.tar.gz" \
  && echo "${TEXLIVE_INSTALLER_SHA256}  /tmp/install-tl.tgz" | sha256sum --check - \
  && mkdir /tmp/install-tl \
  && tar -xzf /tmp/install-tl.tgz -C /tmp/install-tl --strip-components=1 \
  && printf '%s\n' 'selected_scheme scheme-full' 'instopt_letter 0' \
    'tlpdbopt_autobackup 0' 'tlpdbopt_desktop_integration 0' \
    'tlpdbopt_file_assocs 0' 'tlpdbopt_install_docfiles 0' \
    'tlpdbopt_install_srcfiles 0' > /tmp/install-tl/profile \
  && TEXLIVE_INSTALL_NO_CONTEXT_CACHE=1 TEXLIVE_INSTALL_NO_WELCOME=1 \
    perl /tmp/install-tl/install-tl -profile /tmp/install-tl/profile -repository "$repository" \
  && tlmgr remove --force aliascnt \
  && rm -rf /tmp/install-tl /tmp/install-tl.tgz "/usr/local/texlive/${TEXLIVE_YEAR}"/*.log
RUN set -a && . /workspace/config/toolchain.env && set +a \
  && /usr/local/bin/elan-init -y --no-modify-path --default-toolchain none \
  && rm /usr/local/bin/elan-init \
  && elan toolchain install "$LEAN_TOOLCHAIN" \
  && elan default "$LEAN_TOOLCHAIN"
COPY scripts/check-toolchain.sh /workspace/scripts/check-toolchain.sh
RUN set -a && . /workspace/config/toolchain.env && set +a \
  && lualatex --version | head -n1 | grep -F "TeX Live ${TEXLIVE_YEAR}" \
  && ./scripts/check-toolchain.sh
ENTRYPOINT []
CMD ["/bin/zsh"]
