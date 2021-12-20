FROM p4lang/p4c:latest
LABEL maintainer="Nate Foster <jnfoster@cs.cornell.edu>"
LABEL description="This docker image extends p4c with petr4."

# Select the type of image we're building. Use `build` for a normal build, which
# is optimized for image size. Use `test` if this image will be used for
# testing; in this case, the source code and build-only dependencies will not be
# removed from the image.
ARG IMAGE_TYPE=build

ENV PETR4_DEPS pkg-config \
               git \
               m4 \
               libgmp-dev \
               software-properties-common \
               ocaml 
               #\
               #sudo \
               #build-essential \
               #aspcud \
               #unzip \
               #curl \
               #libx11-dev \
               #ocaml-native-compilers \
               #camlp4-extra

ENV PETR4_DEPS_OPAM ANSITerminal \
                    alcotest \
                    bignum \
                    cstruct-sexp \
                    pp \
                    ppx_deriving \
                    ppx_deriving_yojson \
                    yojson \
                    js_of_ocaml \
                    js_of_ocaml-lwt \
                    js_of_ocaml-ppx

COPY . /petr4/
WORKDIR /petr4/

##note on opam init:##
#Sandboxing is a security mechanism to prevent source builds from doing writes outside of their build areas. We use bubblewrap (cgroups) for this on Linux, but it doesn't nest cleanly. You can either run your container as --privileged, in which case you can create namespaces and sandboxing will work.
#You probably just want to run with --disable-sandboxing, as you already have container-level protection in place.
####
#install opam and deps
RUN apt-get update && \
    apt-get install -y --no-install-recommends $PETR4_DEPS && \
    add-apt-repository ppa:avsm/ppa && \
    apt update -y && \
    apt install -y opam && \
    eval $(opam env) && \
    opam init --disable-sandboxing -y && \
    opam switch create 4.09.1 && \
    opam update -y && \
    opam upgrade -y && \
    eval $(opam env)

#pin p4pp and install its deps 
RUN opam pin -y add p4pp https://github.com/cornell-netlab/p4pp.git && \
    eval $(opam env) 

#install opam deps for petr4
RUN opam install -y $PETR4_DEPS_OPAM 

#build and install petr4
RUN dune build --profile release 
#&& \
RUN dune install

