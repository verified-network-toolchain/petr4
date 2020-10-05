+++
title = "Using Petr4"
description = ""
weight = 2
+++

{{< lead >}}

[TODO: update for Petr4]
## Functionality: Examples from SIGCOMM '20 paper
To reproduce the examples from our SIGCOMM '20 paper, see the code and
instructions here:
[extensions/csa/msa-examples](https://github.com/cornell-netlab/MicroP4/tree/master/extensions/csa/msa-examples).
In short, there are 7 composed programs mentioned in the paper. All of them can
be compiler using a single Makefile as mentioned in the [README](https://github.com/cornell-netlab/MicroP4/tree/master/extensions/csa/msa-examples/README.md).

| Program in paper | Composed μP4 program source | Functions composed        |
|------------------|-----------------------------|---------------------------|
| P1 | main-programs/routerv6_main.up4           | Eth + IPv6                |
| P2 | main-programs/routerv46lrx_main.up4       | Eth + IPv4 + IPv6 + MPLS  |
| P3 | main-programs/router_ipv4v6srv6_main.up4  | Eth + IPv4 + IPv6 + SRv6  |
| P4 | main-programs/routerv46_main.up4          | Eth + IPv4 + IPv6         |
| P5 | main-programs/routerv4_main.up4           | Eth + IPv4                |
| P6 | main-programs/router_ipv4v6_nat_acl.up4   | Eth + IPv4 + IPv6 + NAT + NPT6 + ACL |
| P7 | main-programs/router_ipv4srv4ipv6_main.up4 | Eth + IPv4 + IPv6 + SRv4 |

The videos from the installation step also show the usage: https://www.youtube.com/watch?v=ZtmLH0UFeqw&t=77s

## Reusability:
The framework can be used to write, compose and build new dataplane programs. We are working on a [step-by-step tutorial](https://github.com/cornell-netlab/MicroP4/tree/master/extensions/csa/tutorials) to get you started with programming with μP4.
At a high-level, There are two steps in using μP4:

1. Writing μP4 programs: See [this page](https://github.com/cornell-netlab/MicroP4#4-how-to-write-%CE%BCp4-programs) for instructions on writing new programs.
2. Compiling μP4 programs: See [this page](https://github.com/cornell-netlab/MicroP4#5-how-to-use-%CE%BCp4c) for instructions on compiling μP4 programs with μP4C.


{{< /lead >}}


<!-- {{< childpages >}} -->
