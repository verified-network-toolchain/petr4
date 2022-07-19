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
eval $(opam env)
opam install . --deps-only

# build petr4
dune build --profile release
dune install
make ci-test


