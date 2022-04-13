FROM p4lang/p4c:stable
LABEL maintainer="Nate Foster <jnfoster@cs.cornell.edu>"
LABEL description="This docker image extends p4c with petr4."

# Select the type of image we're building. Use `build` for a normal build, which
# is optimized for image size. Use `test` if this image will be used for
# testing; in this case, the source code and build-only dependencies will not be
# removed from the image.
ARG IMAGE_TYPE=build

ENV PETR4_DEPS pkg-config \
               sudo \
               git \
               m4 \
               libgmp-dev \
               ocaml \
               curl \
               build-essential \
               zlib1g-dev \
               libssl-dev \ 
               ocaml-native-compilers \
               apt-utils \
               opam
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
    apt-get install -y software-properties-common && \
    apt-get update && \
    add-apt-repository ppa:avsm/ppa && \
    apt-get update -y && \
    apt-get upgrade -y && \
    apt-get dist-upgrade -y && \
    apt-get install -y --no-install-recommends $PETR4_DEPS && \
    opam init --disable-sandboxing -y && \
    eval $(opam env) && \
    opam update && \
    opam switch list-available && \
    opam switch create 4.12.0 && \
    opam init --disable-sandboxing -y && \
    eval $(opam env) && \
    opam update

#pin p4pp and install its deps 
RUN opam uninstall menhir && \
    opam install menhir.20211128 -y && \ 
    opam pin add p4pp 0.1.7 -y && \
    eval $(opam env)

#opam pin -y add p4pp https://github.com/cornell-netlab/p4pp.git && \

#install opam deps for petr4
RUN opam install -y $PETR4_DEPS_OPAM && \
    eval $(opam env)


#RUN opam config env
ENV PATH "/root/.opam/4.12.0/bin:${PATH}"
RUN echo "export PATH=/root/.opam/4.12.0/bin:${PATH}" >> /etc/environment && \
    . /etc/environment

#build and install petr4
RUN dune build --profile release && \
    dune install
