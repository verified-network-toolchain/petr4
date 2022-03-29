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
                        p4pp \
                        pp \
                        ppx_deriving \
                        ppx_import \
                        ppx_deriving_yojson \
                        yojson \
                        js_of_ocaml \
                        js_of_ocaml-lwt \
                        js_of_ocaml-ppx"

export POULET4_DEPS="coq \
                     coq-equations \
                     coq-record-update \
                     coq-compcert "

export POULET4_CCOMP_DEPS="zarith"

# install deps
sudo apt-get update
sudo apt-get install -y --no-install-recommends \
  ${PETR4_DEPS}
opam update
# install p4pp
opam switch 4.14.0
#opam install menhir.20211128
opam pin add --no-action p4pp https://github.com/cornell-netlab/p4pp.git
opam pin add --no-action coq-vst-zlist https://github.com/PrincetonUniversity/VST.git
eval $(opam env)

# install deps for poulet4
#opam pin add coq 8.13.2
opam repo add coq-released https://coq.inria.fr/opam/released
# install dependencies for petr4, poulet4, poulet4_ccomp
opam install . deps/poulet4 deps/poulet4_Ccomp/extraction --deps-only
#opam install coq-equations coq-record-update coq-compcert 
# install deps for poulet4_ccomp
#opam install zarith

#dune external-lib-deps --missing @install
#opam install ppx_import

make
make install

