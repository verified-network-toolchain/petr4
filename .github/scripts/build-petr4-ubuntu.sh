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
eval $(opam env)
opam install . --deps-only

# build petr4
dune build --profile release
dune install
make ci-test
