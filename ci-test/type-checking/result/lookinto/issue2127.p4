/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2127.p4
\n
#include <core.p4>

header H {
    bit<32> b;
}

parser p(packet_in packet, out H h) {
    state start {
        packet.extract(h);
        ;
        transition accept;
    }
}

parser proto<T>(packet_in p, out T t);
package top<T>(proto<T> p);
top(p()) main;
************************\n******** petr4 type checking result: ********\n************************\n
