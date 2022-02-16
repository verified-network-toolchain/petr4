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
error {
  NoError, PacketTooShort, NoMatch, StackOutOfBounds, HeaderTooShort,
  ParserTimeout, ParserInvalidArgument
}
extern packet_in {
  void extract<T>(out T hdr);
  void extract<T0>(out T0 variableSizeHeader,
                   in bit<32> variableFieldSizeInBits);
  T1 lookahead<T1>();
  void advance(in bit<32> sizeInBits);
  bit<32> length();
}

extern packet_out {
  void emit<T2>(in T2 hdr);
}

extern void verify(in bool check, in error toSignal);
@noWarn("unused")
action NoAction() { 
}
match_kind {
  exact, ternary, lpm
}
header Hdr {
  bit<8> x;
}
struct Headers {
  Hdr[2] h1;
}
parser P(packet_in p, out Headers h) {
  state start
    {
    p.extract(h.h1.next);
    transition select(h.h1.last.x) {
      0: start;
      _: accept;
    }
  }
}
parser Simple<T3> (packet_in p, out T3 t);
package top<T4> (Simple<T4> prs);
top(P()) main;

