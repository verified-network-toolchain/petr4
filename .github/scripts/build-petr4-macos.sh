#!/bin/bash

# petr4 build script for macos

set -e  # Exit on error.
set -x  # Make command execution verbose

export PETR4_DEPS="m4 \
                   gmp"

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

# install dependencies
brew update
brew install \
  ${PETR4_DEPS}
opam update
opam upgrade
opam uninstall menhir
opam install menhir.20211128
# install p4pp
# opam switch create 4.09.1
opam pin add p4pp 0.1.7
# opam pin add p4pp https://github.com/cornell-netlab/p4pp.git
eval $(opam env)
#dune external-lib-deps --missing @install
opam install \
  ${PETR4_DEPS_OPAM}

# build petr4
dune build --profile release
dune install
make test


