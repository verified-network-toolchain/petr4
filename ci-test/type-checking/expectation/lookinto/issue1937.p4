/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1937.p4
\n
#include <core.p4>

header h1_t { bit<8> f1; bit<8> f2; }

parser foo (out bit<8> x, in bit<8> y = 5) {
    state start {
        x = (y >> 2);
        transition accept;
    }
}

parser parserImpl(out h1_t hdr) {
    state start {
        foo.apply(hdr.f1, hdr.f1);
        foo.apply(hdr.f2);
        transition accept;
    }
}

parser p<T>(out T h);
package top<T>(p<T> p);

top(parserImpl()) main;
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
header h1_t {
  bit<8> f1;
  bit<8> f2;
}
parser foo(out bit<8> x, in bit<8> y= 5) {
  state start {
    x = y>>2;
    transition accept;
  }
}
parser parserImpl(out h1_t hdr) {
  state start {
    foo.apply(hdr.f1, hdr.f1);
    foo.apply(hdr.f2);
    transition accept;
  }
}
parser p<T3> (out T3 h);
package top<T4> (p<T4> p);
top(parserImpl()) main;

************************\n******** p4c type checking result: ********\n************************\n
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1937.p4(14): [--Wwarn=uninitialized_use] warning: hdr.f1 may be uninitialized
        foo.apply(hdr.f1, hdr.f1);
                          ^^^^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1937.p4(14): [--Wwarn=invalid_header] warning: accessing a field of an invalid header hdr
        foo.apply(hdr.f1, hdr.f1);
                          ^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1937.p4(14): [--Wwarn=invalid_header] warning: accessing a field of an invalid header hdr
        foo.apply(hdr.f1, hdr.f1);
                  ^^^
/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1937.p4(15): [--Wwarn=invalid_header] warning: accessing a field of an invalid header hdr
        foo.apply(hdr.f2);
                  ^^^
