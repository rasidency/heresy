FROM docker.io/library/haskell@sha256:fc26eac070b263900bc1d80f85118b4681fd964ffa6c29299d594933cb7650f1 AS haskell

FROM docker.io/library/debian@sha256:c67e92c8099ba22853ab4cfda7cfb494d253d6012ca82dee98ba8976772af018 AS toolchain

COPY --from=haskell /etc/ssl/certs /etc/ssl/certs
RUN rm -f /etc/apt/sources.list.d/* && \
    printf '%s\n' \
      'deb [check-valid-until=no] https://snapshot.debian.org/archive/debian/20261101T000000Z bookworm main' \
      'deb [check-valid-until=no] https://snapshot.debian.org/archive/debian-security/20261101T000000Z bookworm-security main' \
      > /etc/apt/sources.list && \
    apt-get update && \
    apt-get install -y --no-install-recommends build-essential ca-certificates curl bzip2 xz-utils patchelf pkg-config libgmp-dev libnuma1 libtinfo5 && \
    rm -rf /var/lib/apt/lists/*

COPY --from=haskell /opt/ghc /opt/ghc
COPY --from=haskell /usr/lib/x86_64-linux-gnu/libffi.so.7* /usr/lib/x86_64-linux-gnu/
COPY --from=haskell /usr/share/doc/libffi7/copyright /usr/share/doc/libffi7/copyright

ENV PATH=/opt/ocaml/bin:/opt/ghc/9.6.7/bin:$PATH
ENV FILCC=/opt/filc/build/bin/clang

RUN curl -fL https://github.com/ocaml/ocaml/archive/refs/tags/5.5.0.tar.gz -o /tmp/ocaml.tar.gz && \
    printf '%s\n' 'c018052c8264a3791a8f54f84179e6bcc78ed82eb889bacc2773df445259aed3  /tmp/ocaml.tar.gz' | sha256sum -c - && \
    tar -xzf /tmp/ocaml.tar.gz -C /tmp && \
    cd /tmp/ocaml-5.5.0 && \
    ./configure --prefix=/opt/ocaml --disable-ocamldoc && \
    make -j2 world.opt && make install && \
    rm -rf /tmp/ocaml-5.5.0 /tmp/ocaml.tar.gz

RUN curl -fL https://github.com/ocaml/dune/releases/download/3.24.2/dune-3.24.2.tbz -o /tmp/dune.tbz && \
    printf '%s\n' '472798691b0216daf538709f0f4703b3617ef24ad0866c9096068baaba4d762a  /tmp/dune.tbz' | sha256sum -c - && \
    tar -xjf /tmp/dune.tbz -C /tmp && \
    cd /tmp/dune-3.24.2 && \
    ocaml boot/bootstrap.ml && \
    install -m755 _boot/dune.exe /opt/ocaml/bin/dune && \
    rm -rf /tmp/dune-3.24.2 /tmp/dune.tbz

RUN curl -fL https://github.com/pizlonator/fil-c/releases/download/v0.687/filc-0.687-linux-x86_64.tar.xz -o /tmp/filc.tar.xz && \
    printf '%s\n' 'aab538401f78a47ab261ee79afed8c6b99e1d4848e263ae159a75b03c1288da1  /tmp/filc.tar.xz' | sha256sum -c - && \
    mkdir /opt/filc && tar -xJf /tmp/filc.tar.xz -C /opt/filc --strip-components=1 && \
    cd /opt/filc && ./setup.sh && rm /tmp/filc.tar.xz && \
    ghc --numeric-version && ocamlopt -version && dune --version && "$FILCC" --version

RUN useradd --uid 10001 --create-home heresy && mkdir /workspace && chown heresy:heresy /workspace
WORKDIR /workspace
USER heresy

FROM toolchain AS proofchain
USER root
RUN apt-get update && apt-get install -y --no-install-recommends zstd && rm -rf /var/lib/apt/lists/* && \
    curl -fL https://github.com/leanprover/lean4/releases/download/v4.24.0/lean-4.24.0-linux.tar.zst -o /tmp/lean.tar.zst && \
    printf '%s\n' 'b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec  /tmp/lean.tar.zst' | sha256sum -c - && \
    mkdir /opt/lean && tar --zstd -xf /tmp/lean.tar.zst -C /opt/lean --strip-components=1 && rm /tmp/lean.tar.zst
ENV PATH=/opt/lean/bin:$PATH
USER heresy

FROM proofchain AS build
COPY --chown=10001:10001 . .
RUN dune build --profile release @all && lake build
CMD ["sh", "-c", "lake build && dune runtest --profile release && dune build --profile release @integration"]
