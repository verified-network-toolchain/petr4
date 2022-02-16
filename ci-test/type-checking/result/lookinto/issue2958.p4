/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2958.p4
\n
#include <core.p4>

header ethernet_t {
    bit<48> dst_addr;
}

struct G {
    ethernet_t eth;
}

struct H {
    G g;
}

struct Headers {
    ethernet_t eth_hdr;
}

control ingress(inout Headers h) {
    H tmp = { { { 1 } } };

    apply {
        tmp.g.eth.dst_addr = 1;
    }
}

control Ingress(inout Headers hdr);
package top(Ingress ig);
top(ingress()) main;
************************\n******** petr4 type checking result: ********\n************************\n
