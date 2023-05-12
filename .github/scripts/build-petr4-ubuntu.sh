#!/bin/bash

# petr4 build script for ubuntu

set -e  # Exit on error.
set -x  # Make command execution verbose

export PETR4_DEPS="m4 \
                   libgmp-dev"

# install dependencies
sudo apt-get update
sudo apt-get install -y --no-install-recommends ${PETR4_DEPS}

opam pin add --no-action p4pp https://github.com/cornell-netlab/p4pp.git
opam pin add --no-action coq-vst-zlist https://github.com/PrincetonUniversity/VST.git

opam install . --deps-only --no-checksums

dune build --profile release
make ci-test
