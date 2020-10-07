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

A P4 program requires several pieces of input before it can be run. The STF
testing framework provides a file format for providing control and data plane
input to your P4 program and checking that it produces the outputs you expect. 

```
```

If you are coming to Petr4 from another P4 system like BMv2, be aware that Petr4
is currently limited to programs with their tables populated by `const entries`
declarations or STF tests and does not expose a runtime control plane interface.


### Understanding the architecture of Petr4

{{< /lead >}}


<!-- {{< childpages >}} -->
