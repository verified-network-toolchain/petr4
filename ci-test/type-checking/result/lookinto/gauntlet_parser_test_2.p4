/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_parser_test_2.p4
\n
#include <core.p4>

header Hdr {
    bit<8> x;
}

struct Headers {
    Hdr[2] h1;
}


parser P(packet_in p, out Headers h) {
    state start {
        p.extract(h.h1.next);
        transition select(h.h1.last.x) {
            0: start;
            _: accept;
        }
    }
}

parser Simple<T>(packet_in p, out T t);
package top<T>(Simple<T> prs);
top(P()) main;
************************\n******** petr4 type checking result: ********\n************************\n
