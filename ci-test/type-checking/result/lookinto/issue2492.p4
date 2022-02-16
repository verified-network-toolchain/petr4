/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2492.p4
\n
#include <core.p4>

header data_t {
    bit<16> h1;
}

struct headers {
    data_t data;
}

control ingress(inout headers hdr) {
    apply {
        hdr.data.h1 = 1;
    }
}

control ctr<H>(inout H hdr);
package top<H1, H2, H3>(ctr<H1> ctrl1, @optional ctr<H2> ctrl2, @optional ctr<H3> ctrl3);

top(ingress()) main;
************************\n******** petr4 type checking result: ********\n************************\n
