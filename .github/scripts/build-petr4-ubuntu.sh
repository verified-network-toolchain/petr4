#!/bin/bash

# petr4 build script for ubuntu

set -e  # Exit on error.
set -x  # Make command execution verbose


export PETR4_DEPS="m4 \
                   libgmp-dev"

export PETR4_DEPS_OPAM="ANSITerminal \
                        alcotest \
                        bignum \
                        cstruct-sexp \
                        pp \
                        ppx_deriving \
                        ppx_deriving_yojson \
                        yojson \
                        js_of_ocaml \
                        js_of_ocaml-lwt \
                        js_of_ocaml-ppx"

# install deps
sudo apt-get update
sudo apt-get install -y --no-install-recommends \
  ${PETR4_DEPS}
opam update
opam upgrade
# opam uninstall menhir
opam install menhir.20211128
# opam install menhir.20211230
# install p4pp
# opam switch create 4.09.1
opam pin add p4pp https://github.com/cornell-netlab/p4pp.git
eval $(opam env)
#export PATH="/usr/local/opt/dune/bin:$PATH"
#dune external-lib-deps --missing @install
opam install \
  ${PETR4_DEPS_OPAM}

# build petr4
dune build --profile release
dune install
