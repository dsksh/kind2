# Cf. https://github.com/kind2-mc/kind2/blob/develop/docker/Dockerfile
#
FROM ocaml/opam:debian-12-ocaml-4.14-flambda as builder

USER root

RUN apt-get update && apt-get install -y --no-install-recommends \
    make m4 g++ musl-dev git \
    libzmq3-dev libsodium-dev \
    curl pkg-config \
    swi-prolog-core libffi-dev && \
    rm -rf /var/lib/apt/lists/* 

USER opam

# Build Kind 2
WORKDIR kind2-build

RUN curl -sSL https://github.com/dsksh/kind2/archive/refs/tags/v2.1.1.hd.tar.gz | tar xz

RUN git clone https://github.com/dsksh/SWIPL-OCaml.git && \
    cd SWIPL-OCaml && \
    eval $(opam env) && \
    #opam repo set-url default https://opam.ocaml.org && \
    opam update && \
    opam install -y dune ctypes-foreign dune-configurator stdio && \
    dune build swipl.opam && \
    opam install -y . --deps-only && \
    opam pin add .

RUN curl -sSL https://github.com/kind2-mc/kind2/archive/refs/tags/v1.6.0.tar.gz | tar xz && \
    cd kind2-1.6.0 && \
    eval $(opam env) && \
    opam update && opam install -y . --deps-only

RUN curl -sSL https://github.com/kind2-mc/kind2/archive/refs/tags/v1.6.0.tar.gz | tar xz && \
    cd kind2-1.6.0 && \
    eval $(opam env) && \
    opam update && opam install -y . --deps-only && \
    #make static && \
    #strip bin/kind2
    make build

RUN curl -sSL https://github.com/dsksh/kind2/archive/refs/tags/v2.1.1.hd.tar.gz | tar xz && \
    cd kind2-2.1.1.hd && \
    eval $(opam env) && \
    opam update && opam install -y . --deps-only && \
    #make static && \
    #strip bin/kind2
    make build

FROM debian:bookworm-slim

USER root

RUN apt-get update && apt-get install -y --no-install-recommends \
    curl bash git \
    libzmq5 libsodium23 \
    swi-prolog-core z3 && \
    rm -rf /var/lib/apt/lists/* 

RUN adduser --disabled-password --gecos KIND2 kind2

COPY --chown=kind2:kind2 --from=builder /home/opam/kind2-build/kind2-1.6.0/bin/kind2 /usr/local/bin/kind2-1.6.0
COPY --chown=kind2:kind2 --from=builder /home/opam/kind2-build/kind2-2.1.1.hd/bin/kind2 /usr/local/bin/kind2-2.1.1
RUN ln -s /usr/local/bin/kind2-2.1.1 /usr/local/bin/kind2

COPY --chown=kind2:kind2 --from=builder /home/opam/kind2-build/kind2-2.1.1.hd/hd/examples/ /work/examples/

COPY demo.sh /work

USER kind2
WORKDIR work
ENTRYPOINT ["./demo.sh"]
#CMD ["./demo.sh"]