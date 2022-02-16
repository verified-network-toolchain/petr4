/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1386.p4
\n
#include <core.p4>
#include <v1model.p4>

header hdr {
  bit<32> a;
}

control compute(inout hdr h) {
    bit<8> n = 0;
    apply {
        if (!h.isValid()) {
            return;
        }

        if (n > 0) {
            h.setValid();
        }
    }
}

#include "arith-inline-skeleton.p4"
************************\n******** petr4 type checking result: ********\n************************\n
