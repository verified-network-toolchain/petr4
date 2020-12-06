# Adding a Target to Petr4

Our reference implementation of P4 makes use of an abstract barrier between the features of the language which are target specific and those which are universal to every P4 program. This design has two key purposes: the help distinguish between these two parts of P4 throughout the process of semantics engineering, and to provide an easy-to-use method for our users to supplement our code with an implementation of their own P4 architecture. This may be useful for those interested in using Petr4 to test P4 code written in an architecture we don't support, or for those who wish to design their own custom P4 architecture. Regardless, this document explains the process of adding an implementation of a P4 arhcitecture to our interpreter.

## What is a P4 Architecture?

On a surface level, an architecture in P4 consists of a collection of `extern` functions/datatypes along with a description of the componenets of the packet-processing pipeline. A close examination of the finer points of the P4 semantics reveals that there are many components in the P4 semantics which may be defined by the target rather than the language itself. In addition to defining externs and pipeline structure, the architecture's may also:

* provide static analysis for enforcing target-dependent well-formedness rules

* define semantics for initializing metadata.

* provide semantics for threading the packet and other metadata through the pipeline.

* define the behavior of reading from uninitialized/invalid headers.

* provide custom table attributes.

* define custom semantics for the invocation/execution of tables.

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

The next required value is the `eval_extern` function. This function takes as its arguments the name of the extern to evaluate, the envrionment and state, the type arguments of the extern call (e.g. a concrete value for `T` in the case of `update` and `remove` in `VSS` provided by the type checker), and the arguments paired with their types. For implementation, we may assume that the arguments are provided in the correct order and that the list is the proper length. The is also the place where we use the number and types of the arguments to distinguish between different externs of the same name, as permitted by the P4 specification. Note that in the case of an invocation of an extern function using dot-notation, e.g. `checksum.clear()`, the value of `checksum` will be available as the additional first argument in the list of arguments. The extern evaluation should then return as a tuple the updated environment (though most externs do not change the environment), the update state, a signal (almost always `Continue`), and the return value. Implementing the externs will require some degree of familiarity with our types for values, environments, and states. Also, note that any mutation of an extern object should be done by updating the mapping in the state via `insert_extern`.

The target must also define what meta-data to initialize. Most targets initialize metadata upon packet ingress for each individual packet, consisting at least of the port number. The current version of our interpreter takes as input this port number, and it is provided as an argument to `initialize_metadata`. Note that the current architecture is not expressive enough to capture all values one may wish to include in the metadata, such as time stamps.

We also include a post-processing step, `get_outport`, which is intended to examine the state and environment for the metadata at the end of the packet-processing pipeline in order to decide on which port number the P4 program has determined the packet should be emitted.

Lastly, the target implementation should provide the function `eval_pipeline`, which determines how the components of the main P4 package should interact in order to process a given packet. The pipeline evaluator takes as inputs the control-plane configuration, initial environment and state, and the packet, outputting the updated state, environment, and optional packet (no packet corresponds to the packet having been dropped). The astute reader will notice the mysterious final argument of type `state apply`. This function is the only piece of the interpreter which we were unable to move into `target.ml` due to a circular dependency, so the interpreter passes it to the pipeline evaluator as an argument. A typical implementation of a pipeline will normally invoke this apply function on the packet and the other required arguments to the parser(s) and control(s). Because the target is responsible for providing arguments to its P4-programmable blocks, this will involve constructing values of our `value` type explicitly and loading them into the environment and state. The user should be careful to chose variable names that will not result in naming conflicts. In the case of `VSS`, an implementation will need to pass a packet value and an uninitialized header to the parser, pass the resulting headers, error, and metadata to the control, and finally pass the updated packet and metadata to the deparser, returning the updated state, environment and packet.

The final step is to apply the `Corize` functor from `lib/p4core.ml` to your new target to ensure that it provides the standard operations on packets provided by the core library in addition to its own externs (this is a single line at the bottom of your newly implemented target). Then, apply the `MakeInterpreter` functor from `lib/eval.mli` to your corized target in a new line at the bottom of `eval.ml(i)` to instantiate the semantics of P4 on your custom interpreter! This provides you with the library of evaluation functions given in `lib/eval.mli` which you may use to process individual packets on custom control-plane configurations.

## Supported Architectures

Petr4's implementation currently supports the V1 Model architecture, which is perhaps the most widely used architecture in P4. It is standard to `bmv2`, and much of the benchmark suite from `P4c` is written in the V1 model. Many of the standard operations we may expect a network device to perform are expressed in the V1 model's `extern` library, and it's pipeline is representative of the structure of a standard packet-processing pipeline.

We also support the eBPF Filter architecture. This is a much smaller architecture, with a minimal collection of externs and a pipeline consisting of only two components. This is supported primarily for proof-of-concept that our abstraction over targets is powerful enough to describe more than only the V1 model.

The code that implements the externs and the pipelines of the V1 model and the eBPF filter can be found in `lib/v1model.ml` and `lib/ebpf.ml` respectively. The implementation of `ebpf.ml` in particular may be a good reference point for someone seeking to implement their own target.

## Limitations

There are two main ways in which our current implementation fails to capture the full expressivity of the P4 abstract machine. First, our implementation has no support for concurrency, and we only consider single-packet execution with a mostly static control-plane configuration. Many of the important externs from the V1 model library that have to do with concurrency and multiple packets (such as `clone` and `resubmit`) are unimplemented in `v1model.ml`. Second, our abstraction excludes from consideration many important concerns about target-dependent semantics in P4. While we provide minimal support for target-dependent decisions about invalid headers, our abstraction is not expressive enough to describe all possible decisions a target may make about accessing invalid header fields, header union, uninitialized stack accesses, etc. We also omit target-dependent table behaviors such as certain table annotations or custom table attributes.
