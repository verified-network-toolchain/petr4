#!/bin/bash

# petr4 build script for ubuntu

set -e  # Exit on error.
set -x  # Make command execution verbose


export PETR4_DEPS="m4 \
                   libgmp-dev"

# install deps
sudo apt-get update
sudo apt-get install -y --no-install-recommends \
  ${PETR4_DEPS}
opam update
opam upgrade
# install p4pp
#opam switch 4.09.1
opam pin add p4pp https://github.com/cornell-netlab/p4pp.git
eval $(opam env)
#install dune
#opam install dune
#export PATH="/usr/local/opt/dune/bin:$PATH"
#cd ../..
#dune external-lib-deps --missing @install
opam install ANSITerminal alcotest bignum cstruct-sexp pp ppx_deriving ppx_deriving_yojson yojson js_of_ocaml js_of_ocaml-lwt js_of_ocaml-ppx
#dune external-lib-deps --missing @@default

make
make install