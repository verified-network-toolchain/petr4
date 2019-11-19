# Welcome to Petr4

The Petr4 project is developing the formal semantics of the [P4
Language](https://p4.org), backed by an independent referene
implementation.

## Getting Started

### Installing Petr4

The Petr4 reference implementation is implemented in OCaml. To install
from source, perform the following steps.

1. Install [OPAM](https://opam.ocaml.org/)

1. Install external dependencies:
   ```
   sudo apt-get install m4 libgmp-dev
   ```

1. Check the installed version of OCaml:
    ```
    ocamlc -v
    ```
    If the version is less than 4.08.0, upgrade:
    ```
    opam switch 4.08.0
    ```        

1. Use OPAM to build and install Petr4. This will take a while the first time
   because it installs OPAM dependencies.
    ```
    opam pin add petr4 .
    ```

### Running Petr4

Currently `petr4` is merely a P4 front-end. By default, it will parse
a source program to an abstract syntax tree and print it out, either
as P4 or encoded into JSON. 

Run `petr4 -help` to see the list of currently-supported options.
            
## Contributing

Petr4 is an open-source project. We encourage contributions!
Please file issues on
[Github](https://github.com/cornell-netlab/petr4/issues)

## Credits

See the list of [contributors](CONTRIBUTORS).

## License

Petr4 is released under the [Apache2 License](LICENSE).
