+++
title = "Claims made in POPL'21 paper"
description = ""
weight = 1
+++

{{< lead >}}

## Claims
The following claims from the paper should be verifiable using the artifact.

1. We run a test suite totaling 792 tests from p4c (line 1153 in section 5.1).
1. All 792 of the tests pass the parser. (line 1155)
1. Only 782 pass the typechecker. (line 1156)
1. The 10 typechecker failures may be attributed to the following limitations
   (line 1156-67)
   1. A lexer bug regarding casts applied to function calls.
   1. The use of @optional argument annotations.
   1. Tests expecting certain numeric casts to fail, rather than only
      issue a warning. (The spec only requires implementations to issue
      warnings for these casts.)
   1. p4c rejects programs that shadow names, while the petr4 implementation
      allows shadowing.
   1. Petr4's implicit cast insertion algorithm may turn a bad divisor (a
      negative signed integer) into one that typechecks (an unsigned, hence
      positive integer) where p4c's implicit cast machinery would not.
   1. p4c goes beyond the standard P4 type system to enforce special typing
      constraints for some V1Model constructs, while Petr4 currently provides
      a target-agnostic type system.
1. There are 110 other tests left off for their use of the following unsupported
   features or disagreements with the specification.
   1. Lack of concurrency
   1. Ignores annotations of all types
   1. No abstract externs or user-defined initialization blocks for externs
   1. (not in paper explicitly?) Parser value sets.
   1. (not in paper explicitly?) Struct flattening in key contexts
   1. (not in paper explicitly?) Generic control and parser declarations (not in
      spec)
   1. (not in paper explicitly?) casting int to bool not allowed (not in spec)
   1. (not in paper explicitly?) byte alignment of header fields
   1. (not in paper explicitly?) Petr4 does not (and cannot) implement the
      p4c/bmv2 C++ extension API.
   1. (not in paper explicitly?) overly permissive tests which pass only for
      p4c's spec violating behavior
      1. could make a list here but it may not be worth it, as there's significant
         overlap with the discussion of bugs
   1. (not in paper explicitly?) overly strict tests which fail despite
      spec-compliant behavior from petr4
      1. as above, could make a list here but it may not be worth it, as there's
         significant overlap with the discussion of bugs
1. There are 121 tests from p4c including STF so they can be used to test the
   Petr4 interpreter. Of these, 26 fail, for the following reasons.
   1. Unimplemented architectures like PSA and ubpf.
   1. Some v1model and ebpf externs omitted: meters, direct-mapped objects,
      multicast, CRC16 checksums...
1. There are 40 additional custom tests we wrote, all of which pass.

## Checking the claims
The provenance of the tests is not evident. Some of them are tests we wrote,
others are tests from p4c. So I think the paper's top level sentence ``We have
imported 792 test cases from p4c for ...'' is maybe not exactly right.

To run the test suite, open a terminal in the root of the petr4 repository and
run the following commands.
```
cd ~/petr4
. ./triage/util.sh
chknow && stfnow
```
They should produce no output on the terminal. Instead test information will be
recorded in several files under `~/petr4/testruns/`.

{{< /lead >}}


