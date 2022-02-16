/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2795.p4
\n
#include <core.p4>

header H {
    bit<32> a;
    bit<32> b;
}

control c(packet_out p) {
    apply {
        p.emit((H){0, 1});
        p.emit<H>({0,1});
    }
}

control ctr(packet_out p);
package top(ctr _c);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
