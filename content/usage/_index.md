+++
title = "Using Petr4"
description = ""
weight = 2
+++

{{< lead >}}

## Functionality: Reproducing Results from POPL '21 paper
Oops, the stuff in "Claims" should go here.

## Reusability:
Petr4 provides a reference interpreter that runs P4 programs but can also serve
as a useful frontend for P4 tools or as a testbed for new features. 

### Running P4 programs with Petr4

Before Petr4 can run a P4 program you have to provide it a control plane
configuration and a packet in the STF (Simple Test Framework) format, which is
described in the next section. Assuming you have a program `file.p4` and STF
configuration `file.stf`, you can run it as follows.
```
petr4 run --stf file.stf file.p4
```

#### Writing STF
Here is
a brief example adapted from `examples/checker_tests/good/issue2153-bmv2.stf`,
a test case from the P4C test suite.

```
add simple_table hdr.h.b:0x55 do_something()

packet 0 11 11 11 11 11 11 22 22 22 22 22 22 33 33 FF EE
expect 0 11 11 11 11 11 11 22 22 22 22 22 22 33 33 FF EE
```

This STF file adds a rule to the table `simple_table`, sends a 16-byte packet to
the program on port 0, and checks that the same packet is emitted unchanged on
port 0.

The format of an add command is `add table_name key:match`...`key:match action`.
The `table_name` should refer to a table in the P4 program being tested or run.
STF permits writing a list of matches in an add command without the `key:` parts
because the list of keys can be determined from the table declaration in P4. The
P4 table declaration will contain a list of keys marked with match kinds (e.g.,
`exact` or `ternary`). There should be one `key:match` expression in an `add`
rule for each key in the table's keys property. Each `match` should be formatted
appropriately for the given match kind.

#### Match kinds
There are three match kinds: `exact`, `ternary`, and `lpm` (longest prefix
match). Each has an associated format for writing matches in STF.

For an `exact` key, the match should be an integer constant in hexadecimal. In
our example above, the key is an exact key and the match is `0x55`.

For a `ternary` key, the match can also include asterisks `*` to indicate bits
that can match anything. For example, `0xFF**` will match any two-byte key with
FF in the first byte.

For an `lpm` key, the match should be two integer constants separated by a slash
`/`. The constant after the slash is the mask, which may be familiar from IP
subnetting: a mask 0xFFFFFF00 corresponds to the IP subnet 255.255.255.0. The
semantics of LPM is, as the name suggests, to follow the match-action rule which
matches the longest prefix of the key.

### Understanding the architecture of Petr4
[Nate: describe ASTs in here]

{{< /lead >}}


<!-- {{< childpages >}} -->
