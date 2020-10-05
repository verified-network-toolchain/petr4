+++
title = "Claims made in POPL'21 paper"
description = ""
weight = 1
+++

{{< lead >}}

## Claims
The following claims from the paper should be verifiable using the artifact.

1. We pass XX of the YY p4c tests.
1. The remaining YY-XX fail due to the following features.
   1. Value sets in parsers
   1. todo todo

## Checking the claims

To run the test suite, open a terminal in the root of the petr4 repository and
run the following commands.
```
cd ~/petr4
. ./triage/util.sh
chknow && stfnow
```
They should produce no output on the terminal. Instead test information will be
recorded in several files under `~/petr4/testruns/`.

Run through the claims one by one here...


{{< /lead >}}


