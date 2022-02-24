/petr4/ci-test/type-checking/testdata/p4_16_samples/pvs.p4
\n
#include <core.p4>

header H {
    bit<32> f;
}

parser p(packet_in pk) {
    value_set<tuple<bit<32>, bit<2>>>(4) vs;
    H h;

    state start {
        pk.extract(h);
        transition select(h.f, 2w2) {
            vs: next;
            default: reject;
        }
    }

    state next {
        transition accept;
    }
}

parser ps(packet_in p);
package top(ps _p);

top(p()) main;
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
header H {
  bit<32> f;
}
parser p(packet_in pk) {
  value_set<tuple<bit<32>, bit<2>>>(4) vs;
  H h;
  state start
    {
    pk.extract(h);
    transition select(h.f, 2w2) {
      vs: next;
      default: reject;
    }
  }
  state next {
    transition accept;
  }
}
parser ps (packet_in p);
package top (ps _p);
top(p()) main;

************************\n******** p4c type checking result: ********\n************************\n
