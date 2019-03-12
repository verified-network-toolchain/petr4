# Welcome to Petr4

The Petr4 project is developing the formal semantics of the [P4
Language](https://p4.org), backed by an independent referene
implementation.

## Getting Started

### Installing Petr4

The Petr4 reference implementation is implemented in OCaml. To install
from source, perform the following steps.

1. Install [OPAM](https://opam.ocaml.org/)

1. Switch to OCaml version 4.06.0 or greater:
    ```
    opam switch 4.06.0    
    ```        

1. Install required OCaml dependencies. Note that JBuilder can compute the list of dependencies, 
    ```
    jbuilder external-lib-deps --missing @install
    ```
    and you can install each using OPAM---for example:
    ```
    opam install menhir    
    ```
    
1. Build Petr4
    ```
    make && make install
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

See the list of [contributors](CONTRIBUTORS.md).

## License

Petr4 is released under the [Apache2 License](LICENSE).
