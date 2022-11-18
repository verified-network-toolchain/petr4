#!/bin/bash

# petr4 build script for macos

set -e  # Exit on error.
set -x  # Make command execution verbose

export PETR4_DEPS="m4 \
                   gmp"

pwd
# install dependencies
brew update
brew install ${PETR4_DEPS}
opam switch 4.14.0
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam update

opam pin add --no-action p4pp https://github.com/cornell-netlab/p4pp.git
opam pin add --no-action coq-vst-zlist https://github.com/PrincetonUniversity/VST.git

opam install . deps/poulet4 deps/poulet4_Ccomp/extraction --deps-only --no-checksums

make
make install

