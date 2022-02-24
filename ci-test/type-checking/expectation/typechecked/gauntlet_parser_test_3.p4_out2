/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_parser_test_3.p4
\n
#include <core.p4>

header Hdr {
    bit<8> x;
}

struct Headers {
    Hdr[2] h1;
    Hdr[2] h2;
}

parser P(packet_in p, out Headers h) {
    state start {
        p.extract(h.h1.next);
        p.extract(h.h1.next);
        if (h.h1[1].x == 1) {
            h.h2[1] = h.h1.next;
        } else {
            h.h2[1] = h.h1.last;
        }
        transition accept;
    }
}

parser Simple<T>(packet_in p, out T t);
package top<T>(Simple<T> prs);
top(P()) main;
************************\n******** petr4 type checking result: ********\n************************\n
File /petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_parser_test_3.p4, line 16, characters 8-10: syntax error
************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_parser_test_3.p4(17): [--Wwarn=uninitialized] warning: h.h1.next: reading uninitialized value
            h.h2[1] = h.h1.next;
                      ^^^^^^^^^
