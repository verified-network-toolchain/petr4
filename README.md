[![Build Status](https://travis-ci.org/cornell-netlab/petr4.svg?branch=use-poulet4)](https://travis-ci.org/cornell-netlab/petr4)

# Petr4
The Petr4 project is developing the formal semantics of the [P4
Language](https://p4.org) backed by an independent reference implementation.

# POPL'21 artifact
See https://cornell-netlab.github.io/petr4/ or check out the `gh-pages` branch
for information on the Petr4 artifact.

## Getting Started

### Installing Petr4

1. Install OPAM 2 following the official [OPAM installation
   instructions](https://opam.ocaml.org/doc/Install.html). Make sure `opam
   --version` reports version 2 or later.

1. Install external dependencies:
   ```
   sudo apt-get install m4 libgmp-dev
   ```

#### Installing from OPAM
1. Install petr4 from the opam repository. This will take a while the first time
   because it installs OPAM dependencies.
   ```
   opam install petr4
   ```

#### Installing from source
1. Check the installed version of OCaml:
    ```
    ocamlc -v
    ```
    If the version is less than 4.09.1, upgrade:
    ```
    opam switch 4.09.1
    ```

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

### Running Petr4

Currently `petr4` is merely a P4 front-end. By default, it will parse
a source program to an abstract syntax tree and print it out, either
as P4 or encoded into JSON.

Run `petr4 -help` to see the list of currently-supported options.

### Web user interface

`petr4` uses `js_of_ocaml` to provide a web interface. To compile to javascript,
run `make web`. Then open `index.html` in `html_build` in a browser.

## Contributing

Petr4 is an open-source project. We encourage contributions!
Please file issues on
[Github](https://github.com/cornell-netlab/petr4/issues).

## Credits

See the list of [contributors](CONTRIBUTORS).

## License

Petr4 is released under the [Apache2 License](LICENSE).
