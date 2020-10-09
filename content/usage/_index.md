+++
title = "Using Petr4"
description = ""
weight = 2
+++

{{< lead >}}

Petr4 provides a reference interpreter that runs P4 programs but can also serve
as a useful frontend for P4 tools or as a testbed for new features. 

Before Petr4 can run a P4 program you have to provide it a control plane
configuration and a packet in the STF (Simple Test Framework) format, which is
described in the next section. Assuming you have a program `file.p4` and STF
configuration `file.stf`, you can run it as follows.
```
petr4 stf -I examples -stf file.stf file.p4
```
The -I command sets the include path for `petr4` to the examples directory in
the Petr4 repository, which is where the standard library headers are kept.

## Writing STF

Here are the first few lines of the `examples/lpm-example-for-artifact-eval.stf`
STF script, which is representative of the form of most STF files: a prelude
adding rules to tables followed by some test packets.
```
add t_lpm h.h.key:0x11/0xf0 set_port(x:1)
add t_lpm h.h.key:0x12/0xff set_port(x:2)
packet 0 0b 11 00 b0
expect 1 0b 11 ** ** $
```
It adds a rule to the table `simple_table`, sends a 4-byte packet to the program
on port 0, and checks that the packet is emitted on port 1 with its first two
bytes unchanged.

To run this STF script, use `petr4 stf` from the root of the petr4 repo.
```
petr4 stf -I examples -stf examples/lpm-example-for-artifact-eval.stf examples/lpm-example-for-artifact-eval.p4
```

## STF commands

The packet command takes a port number and then a packet. Spaces in
packets are ignored and should be used to group bytes or headers for legibility.

The `expect` command takes a port and then a packet pattern. Spaces in
packet patterns are ignored. Asterisks match anything. By default pattern
matching just checks prefixes, so a pattern `FF` would match a packet `FFFF`.
Adding a `$` at the end of the packet will restrict the match to the entire
packet.

The format of an add command is `add table_name key:match`...`key:match action`.
The `table_name` should refer to a table in the P4 program being tested or run.
STF permits writing a list of matches in an add command without the `key:` parts
because the list of keys can be determined from the table declaration in P4. The
P4 table declaration will contain a list of keys marked with match kinds (e.g.,
`exact` or `ternary`). There should be one `key:match` expression in an `add`
rule for each key in the table's keys property. Each `match` should be formatted
appropriately for the given match kind.

## Match kinds
There are three match kinds: `exact`, `ternary`, and `lpm` (longest prefix
match). Each has an associated format for writing matches in STF.

For an `exact` key, the match should be an integer constant in hexadecimal. In
our example above, the key is an exact key and the match is `0x55`.

For a `ternary` key, the match can also include asterisks `*` to indicate bits
that can match anything. For example, `0xFF**` will match any two-byte key with
FF in the first byte.

For an `lpm` key, the match should be two integer constants separated by a slash
`/`. The constant after the slash is the mask, which may be familiar from IPv4
configuration: a mask 0xFFFFFF00 corresponds to setting your IPv4 subnet to
255.255.255.0. The semantics of LPM is, as the name suggests, to follow the
match-action rule which matches the longest prefix of the key. So if several
value-mask pairs match the key but one has a longer mask, that'll be the
preferred rule (with ties broken by rule insertion order).
{{< /lead >}}


<!-- {{< childpages >}} -->
