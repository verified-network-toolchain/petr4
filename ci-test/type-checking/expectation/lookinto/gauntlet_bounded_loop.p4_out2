/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_bounded_loop.p4
\n
#include <core.p4>

header H {
    bit<8> a;
}

header padding {
    bit<8> p;
}

struct headers {
    H nop;
    padding p;
}

parser sub_parser(packet_in b, out headers hdr) {
    bit<8> tracker;

    state start {
        tracker = 0;
        transition next;
    }

    state next {
        if (tracker == 1) {
            b.extract(hdr.p);
            hdr.p.p = 1;
        }
        transition select(hdr.p.p) {
            0: parse_hdr;
            default: accept;
        }
    }
    state parse_hdr {
        tracker = tracker + 1;
        b.extract(hdr.nop);
        transition next;
    }

}

parser p(packet_in packet, out headers hdr) {
    state start {
        sub_parser.apply(packet, hdr);
        transition accept;
    }

}

parser Parser(packet_in b, out headers hdr);
package top(Parser p);
top(p()) main;
************************\n******** petr4 type checking result: ********\n************************\n
File /petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_bounded_loop.p4, line 25, characters 8-10: syntax error
************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_bounded_loop.p4(29): [--Wwarn=uninitialized_use] warning: hdr.p.p may be uninitialized
        transition select(hdr.p.p) {
                          ^^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/gauntlet_bounded_loop.p4(29): [--Wwarn=invalid_header] warning: accessing a field of a potentially invalid header hdr.p
        transition select(hdr.p.p) {
                          ^^^^^
