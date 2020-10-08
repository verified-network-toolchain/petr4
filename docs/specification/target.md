# Adding a Target to Petr4

Our reference implementation of P4 makes use of an abstract barrier between the features of the language which are target specific and those which are universal to every P4 program. This design has two key purposes: the help distinguish between these two parts of P4 throughout the process of semantics engineering, and to provide an easy-to-use method for our users to supplement our code with an implementation of their own P4 architecture. This may be useful for those interested in using Petr4 to test P4 code written in an architecture we don't support, or for those who wish to design their own custom P4 architecture. Regardless, this document explains the process of adding an implementation of a P4 arhcitecture to our interpreter.

## What is a P4 Architecture?

On a surface level, an architecture in P4 consists of a collection of `extern` functions/datatypes along with a description of the componenets of the packet-processing pipeline. However, a closer examination of the finer points of the P4 semantics reveals that there are many components in the P4 semantics which may be defined by the target rather than the language. In addition to defining externs and pipeline structure, the architecture's responsibilities include but are not limited to:

* provide static analysis for enforcing target-dependent well-formedness rules

* define semantics for initializing metadata

* provide semantics for threading the packet and other metadata through the pipeline

* define the behavior of reading from uninitialized/invalid headers

* provide custom table attributes

* define custom semantics for the invocation/execution of tables

Therefore, an architecture consists of definitions for all of these semantic concerns. Indeed, many of these components correspond directly to values required by our signature for a target implementation.

## Adding to our Code

The signature for the module `Target` is given in `lib/target.mli`. It is worth noting that there is a rather large collection of useful functions also provided by `target.mli` which will be in the scope of the newly implemented target. Our own implementations of `V1 Model` and `eBPF Filter` make use of many of these. Also provided by `target.mli` is the abstract type for the state of the program. An implementer will be primarily concerned with the functions `insert_extern` and `find_extern`, as they deal with the part of the state which contains all of the target-provided stateful objects.

We now step through the process of implementing this signature using the example architecture `Very Simple Switch`, a toy architecture that the P4 language specification uses to illustrate the oddities of target-dependent semantics in P4. For reference, the target description file in the P4 code is given below:

```
# include <core.p4>

typedef bit<4> PortId;

const PortId REAL_PORT_COUNT = 4w8;

struct InControl {
    PortId inputPort;
}

const PortId RECIRCULATE_IN_PORT = 0xD;
const PortId CPU_IN_PORT = 0xE;

struct OutControl {
    PortId outputPort;
}

const PortId DROP_PORT = 0xF;
const PortId CPU_OUT_PORT = 0xE;
const PortId RECIRCULATE_OUT_PORT = 0xD;

parser Parser<H>(packet_in b, out H parsedHeaders);

control Pipe<H>(inout H headers,
                in error parseError,
                in InControl inCtrl,
                out OutControl outCtrl);

control Deparser<H>(inout H outputHeaders, packet_out b);

package VSS<H>(Parser<H> p,
               Pipe<H> map,
               Deparser<H> d);
               
extern Checksum16 {
    Checksum16();
    void clear();
    void update<T>(in T data);
    void remove<T>(in T data);
    bit<16> get();
}
```

First, the user must provide the type `obj`, which will be used to represent target-provided stateful value. In the case of `VSS`, only one such data structure is needed -- the underlying value of the `Checksum16` extern. Some other commonly used externs include counter and register arrays, as in `V1 Model`. The types `state` and `extern` are parameterized on the type `obj` and should be copied into the implementation as they appear in the signature.

The user must also provide the functions `write_header_field` and `read_header_field`. These functions will be called by the main interpreter when reading and writing to headers, and they are intended to capture the fact that the semantics in these cases is left target-dependent by the P4 specification. However, the abstraction in its current form is not necessarily expressive enough to capture all possible decisions for header reads and writes. The average user will likely want to reuse our implementations of these functions in `v1model.ml` and `ebpf.ml`.

The next required value is the `eval_extern` function.

Paragraph about metadata initialization.

Paragraph about pipeline evaluation.

Paragraph about post-processing metadata.

Cleanup paragraph: mention something about Core, other ambiguities in our design?

## Supported Architectures

Petr4's implementation currently supports the V1 Model architecture, which is perhaps the most widely used architecture in P4. It is standard to `bmv2`, and much of the benchmark suite from `P4c` is written in the V1 model. Many of the standard operations we may expect a network device to perform are expressed in the V1 model's `extern` library, and it's pipeline is representative of the structure of a standard packet-processing pipeline.

We also support the eBPF Filter architecture. This is a much smaller architecture, with a minimal collection of externs and a pipeline consisting of only two components. This is supported primarily for proof-of-concept that our abstraction over targets is powerful enough to describe more than only the V1 model.

The code that implements the externs and the pipelines of the V1 model and the eBPF filter can be found in `lib/v1model.ml` and `lib/ebpf.ml` respectively. The implementation of `ebpf.ml` in particular may be a good reference point for someone seeking to implement their own target.

## Limitations

There are two main ways in which our current implementation fails to capture the full expressivity of the P4 abstract machine. First, our implementation has no support for concurrency, and we only consider single-packet execution with a mostly static control-plane configuration. Many of the important externs from the V1 model library that have to do with concurrency and multiple packets (such as `clone` and `resubmit`) are unimplemented in `v1model.ml`. Second, our abstraction excludes from consideration many important concerns about target-dependent semantics in P4. While we provide minimal support for target-dependent decisions about invalid headers, our abstraction is not expressive enough to describe all possible decisions a target may make about accessing invalid header fields, header union, uninitialized stack accesses, etc. We also omit target-dependent table behaviors such as certain table annotations or custom table attributes. 