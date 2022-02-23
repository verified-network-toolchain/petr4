/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2155.p4
\n
#include <core.p4>
#define ISSUE 1

header data {
  bit<8> da;
  bit<8> db;
}

struct headers {
    data hdr;
}

struct metadata {
  bit<32> foo;
}

parser ParserImpl(
    packet_in b,
    out headers p,
    inout metadata m)
{
  state start {
    b.extract(p.hdr);
    m.foo = 32w1;
    transition select(p.hdr.da) {
        0xaa: parse_b;
#ifdef ISSUE
        default: reject;
#else
        default: accept;
#endif
    }
  }

  state parse_b {
      m.foo = 32w2;
      transition accept;
  }
}

parser P<H, M>(packet_in b, out H h, inout M m);
package top<H, M>(P<H, M> p);
top(ParserImpl()) main;************************\n******** petr4 type checking result: ********\n************************\n
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
header data {
  bit<8> da;
  bit<8> db;
}
struct headers {
  data hdr;
}
struct metadata {
  bit<32> foo;
}
parser ParserImpl(packet_in b, out headers p, inout metadata m) {
  state start
    {
    b.extract(p.hdr);
    m.foo = 32w1;
    transition select(p.hdr.da) {
      170: parse_b;
      default: reject;
    }
  }
  state parse_b {
    m.foo = 32w2;
    transition accept;
  }
}
parser P<H, M> (packet_in b, out H h, inout M m);
package top<H3, M4> (P<H3, M4> p);
top(ParserImpl()) main;

************************\n******** p4c type checking result: ********\n************************\n
