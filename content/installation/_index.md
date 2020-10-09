+++
title = "Installing Petr4"
description = ""
weight = 1
+++

{{< lead >}}

Petr4 is available pre-built in a VM or it may be built from source.

## Installing the VM

1. Install [VirtualBox](https://virtualbox.org/) or your preferred
   virtualization software capable of running .ova files.
1. [Download the VM image from
   Box](https://cornell.box.com/s/xcvswidhg5rn6wq2q8lbbso6bk719kr6). It is
   a 1.4GB file and should not take too long to download.
1. Boot the VM image. The username is petr4 and the password is petr4. There
   is a prebuilt version of petr4 installed and the source code is
   checked out in `~/petr4`.

## Installing from source

Make sure you have a local copy of the Petr4 and P4pp (P4 Preprocessor)
repositories.
```
git clone git://github.com/cornell-netlab/petr4
git clone git://github.com/cornell-netlab/p4pp
```

### Installing dependences

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

### Building Petr4
Run the following steps first for p4pp and then for petr4. The p4pp package is
a dependency of petr4.

1. Use OPAM to install OCaml library dependencies. 
   ```
   opam install . --deps-only
   ```

1. Build binaries using the supplied `Makefile`.
   ```
   make
   ```

1. Install the binaries in your local OPAM directory.
   ```
   make install
   ``` 

{{< /lead >}}

