// modified enum-bmv2.p4

#include <core.p4>
#include <v1model.p4>

header hdr {
    bit<32> a;
    bit<32> b;
    bit<32> c;
}

enum Choice {
    First,
    Second
}

control compute(inout hdr h)
{
    apply {
        // Test enum lowering
        Choice c = Choice.First;

        if (c == Choice.Second)
            h.c = h.a; // + compute
        else
            h.c = h.b; // + compute
    }
}

#include "arith-inline-skeleton.p4"
