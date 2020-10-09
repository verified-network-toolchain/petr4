+++
title = "Installing Petr4"
description = ""
weight = 1
+++

{{< lead >}}

Petr4 is available pre-built in a VM or as an OPAM package. The OPAM package can
be built from the version published on
[opam.ocaml.org/packages](https://opam.ocaml.org/packages) or it can be built
from the Petr4 git repository directly.

## Installing the VM

1. Install [VirtualBox](https://virtualbox.org/) or your preferred
   virtualization software capable of running .ova files.
1. Download the VM image from Zenodo [TODO:link when VM is ready and
   uploaded].
1. Boot the VM image. The username is petr4 and the password is petr4. There
   should be a prebuilt version of petr4 installed and the source code is
   checked out in the VM user's home directory.

## Installing the OPAM package

1. Install OPAM 2 following the official [OPAM installation
   instructions](https://opam.ocaml.org/doc/Install.html). Make sure `opam
   --version` reports version 2 or later.

1. Check the installed version of OCaml:
    ```
    ocamlc -v
    ```
    If the version is less than 4.09.0, upgrade:
    ```
    opam switch create 4.09.0 ocaml-base-compiler.4.09.0
    ```

1. Install external dependencies:
   ```
   sudo apt-get install m4 libgmp-dev
   ```

### Installing from source
1. Install [p4pp](https://github.com/cornell-netlab/p4pp) from source.

1. Use OPAM to install dependencies. 
   ```
   opam install . --deps-only
   ```

1. Build binaries using the supplied `Makefile`
   ```
   make
   ```

1. Install binaries in local OPAM directory
   ```
   make install
   ``` 

1. [Optional] Run tests
   ``` 
   make test
   ```

### Installing from OPAM
1. Install petr4 from the opam repository.
   ```
   opam install petr4
   ```

{{< /lead >}}

