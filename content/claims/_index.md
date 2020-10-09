+++
title = "Verifying claims from the POPL'21 paper"
description = ""
weight = 1
+++

{{< lead >}}

## Claims
The following claims from section 5 ("Evaluation") should be verifiable using
the artifact.

1. We run a test suite totaling 792 tests from p4c.
1. All 792 of the tests pass the parser.
1. Only 782 pass the typechecker.
1. The 10 typechecker failures may be attributed to the following limitations.
   * A lexer bug regarding casts applied to function calls.
   * The use of @optional argument annotations.
   * Tests expecting certain numeric casts to fail, rather than only
     issue a warning. (The spec only requires implementations to issue
     warnings for these casts.)
   * p4c rejects programs that shadow names, while the petr4 implementation
     allows shadowing.
   * Petr4's implicit cast insertion algorithm may turn a bad divisor (a
     negative signed integer) into one that typechecks (an unsigned, hence
     positive integer) where p4c's implicit cast machinery would not.
   * p4c goes beyond the standard P4 type system to enforce special typing
     constraints for some V1Model constructs, while Petr4 currently provides
     a target-agnostic type system.
1. There are 110 other tests left off for their use of the following unsupported
   features or disagreements with the specification. Some of these are not
   enumerated in the paper.
   * Ignores annotations of all types
   * No abstract externs or user-defined initialization blocks for externs
   * Parser value sets
   * Struct flattening in key contexts (not in spec)
   * Generic control and parser declarations (not in spec)
   * Casting int to bool not allowed (not in spec)
   * Enforcing byte alignment of header fields
   * Petr4 does not (and cannot) implement the p4c/bmv2 C++ extension API.
   * Other overly permissive tests which pass only for p4c's spec violating behavior
   * Other overly strict tests which fail despite spec-compliant behavior from petr4
1. There are 121 tests from p4c including STF so they can be used to test the
   Petr4 interpreter. Of these, 26 are excluded, for the following reasons.
   * Unimplemented architectures like PSA and ubpf.
   * Some unimplemented v*odel and ebpf externs: meters, direct-mapped
     objects, multicast, CRC16 checksums, and others.
   * Empty STF files that do nothing.
1. There are 40 additional custom tests we wrote, all of which pass.

## Checking the claims
To run the test suite, open a terminal in the root of the petr4 repository and
run the following command.
```
make claims
```

It should produce this output.

```
Running test suite. This will take a few minutes...

792 parser tests
    792 passed
    0 failed
792 typechecker tests
    782 passed
    10 failed [Run `grep -R FAIL /home/ryan/dev/petr4-aux/test/_build/_tests/4BC654C2-965B-45E1-83A6-E5EEF138A21D` to see which.]
95 p4c STF tests
    95 passed
    0 failed
40 custom STF tests
    40 passed
    0 failed
91 excluded [See examples/checker_tests/excluded.]
    27 with STF
```

The tally of excluded checker tests (91) differs from the paper's claim (110)
because the paper counted individual files as test. There is a single test case
`fabric.p4` which uses 18 additional P4 files under the directory
`examples/checker_tests/excluded/good/include`, but is counted as a single test
by the test framework because the support files cannot be run on their own.

The tally of excluded STF tests (27) differs from the paper's claim (26). This
seems to be an error and will be corrected in the camera-ready version.

{{< /lead >}}


