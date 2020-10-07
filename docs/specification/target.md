# Adding a Target to Petr4

Our reference implementation of P4 makes use of an abstract barrier between the features of the language which are target specific and those which are universal to every P4 program. This design has two key purposes: the help distinguish between these two parts of P4 throughout the process of semantics engineering, and to provide an easy-to-use method for our users to supplement our code with an implementation of their own P4 architecture. This may be useful for those interested in using Petr4 to test P4 code written in an architecture we don't support, or for those who wish to design their own custom P4 architecture. Regardless, this document explains the process of adding an implementation of a P4 arhcitecture to our interpreter.

## What is a P4 Architecture?

Describe the componenets of an architecture.

## Adding to our Code

We step through the process using the example architecture `Simple Switch`, a toy generic architecture that the P4 language specification uses to illustrate the many oddities of 

Some text about the functor, modules, and what pieces need implementing.

## Supported Architectures

Petr4's implementation currently supports the V1 Model architecture, which is perhaps the most widely used architecture in P4. It is standard to `bmv2`, and much of the benchmark suite from `P4c` is written in the V1 model. Many of the standard operations we may expect a network device to perform are expressed in the V1 model's `extern` library, and it's pipeline is representative of the structure of a standard packet-processing pipeline.

We also support the eBPF Filter architecture. This is a much smaller architecture, with a minimal collection of externs and a pipeline consisting of only two components. This is supported primarily for proof-of-concept that our abstraction over targets is powerful enough to describe more than only the V1 model.

The code that implements the externs and the pipelines of the V1 model and the eBPF filter can be found in `lib/v1model.ml` and `lib/ebpf.ml` respectively. The implementation of `ebpf.ml` in particular may be a good reference point for someone seeking to implement their own target.

## Limitations

There are two main ways in which our current implementation fails to capture the full expressivity of the P4 abstract machine. First, our implementation has no support for concurrency, and we only consider single-packet execution with a mostly static control-plane configuration. Many of the important externs from the V1 model library that have to do with concurrency and multiple packets (such as `clone` and `resubmit`) are unimplemented in `v1model.ml`. Second, our abstraction excludes from consideration many important concerns about target-dependent semantics in P4. While we provide minimal support for target-dependent decisions about invalid headers, our abstraction is not expressive enough to describe all possible decisions a target may make about accessing invalid header fields, header union, uninitialized stack accesses, etc. We also omit target-dependent table behaviors such as certain table annotations or custom table attributes. 