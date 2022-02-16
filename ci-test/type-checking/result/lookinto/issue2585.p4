/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2585.p4
\n
#include <core.p4>

header Header {
    bit<32> data;
    bit<32> data2;
}

parser p0(packet_in p, out Header h) {
    state start {
        p.extract(h);
        h.data = h.data2 - 8 - 8 - 2 - 16;
        transition accept;
    }
}

parser proto(packet_in p, out Header h);
package top(proto _p);

top(p0()) main;
************************\n******** petr4 type checking result: ********\n************************\n
