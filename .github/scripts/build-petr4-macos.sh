#!/bin/bash

# petr4 build script for macos

set -e  # Exit on error.
set -x  # Make command execution verbose

export PETR4_DEPS="m4 \
                   gmp"


# install dependencies
brew update
brew install \
  ${PETR4_DEPS}
opam update
opam upgrade
# install p4pp
#opam switch 4.09.1
opam pin add p4pp https://github.com/cornell-netlab/p4pp.git
#install dune
#opam install dune
cd ../..
#opam external-lib-deps --missing @install

# build petr4
dune build
dune install


