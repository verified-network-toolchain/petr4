/petr4/ci-test/type-checking/testdata/p4_16_samples/union-key.p4
\n
#include <core.p4>

header H1 {
    bit<32> x;
}

header H2 {
    bit<16> y;
}

header_union U {
    H1 h1;
    H2 h2;
}

struct Headers {
    U u;
}

control c(in Headers h) {
    action a() {}
    table t {
        key = {
            h.u.h1.x: exact;
        }
        actions = { a; }
    }
    apply {
        t.apply();
    }
}

control _c(in Headers h);
package top(_c c);

top(c()) main;
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
header H1 {
  bit<32> x;
}
header H2 {
  bit<16> y;
}
header_union U {
  H1 h1;
  H2 h2;
}
struct Headers {
  U u;
}
control c(in Headers h) {
  action a() { 
  }
  table t {
    key = {
      h.u.h1.x: exact;
    }
    actions = {
      a;
    }
  }
  apply {
    t.apply();
  }
}
control _c (in Headers h);
package top (_c c);
top(c()) main;

************************\n******** p4c type checking result: ********\n************************\n
