/petr4/ci-test/type-checking/testdata/p4_16_samples/control-as-param.p4
\n
#include <core.p4>

control E(out bit b);

control D(out bit b) {
    apply {
        b = 1;
    }
}

control F(out bit b) {
    apply {
        b = 0;
    }
}

control C(out bit b)(E d) {
    apply {
        d.apply(b);
    }
}

control Ingress(out bit b) {
    D() d;
    F() f;
    C(d) c0;
    C(f) c1;
    apply {
        c0.apply(b);
        c1.apply(b);
    }
}

package top(E _e);

top(Ingress()) main;
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
control E (out bit<1> b);
control D(out bit<1> b) {
  apply {
    b = 1;
  }
}
control F(out bit<1> b) {
  apply {
    b = 0;
  }
}
control C(out bit<1> b)(E d) {
  apply {
    d.apply(b);
  }
}
control Ingress(out bit<1> b) {
  D() d;
  F() f;
  C(d) c0;
  C(f) c1;
  apply {
    c0.apply(b);
    c1.apply(b);
  }
}
package top (E _e);
top(Ingress()) main;

************************\n******** p4c type checking result: ********\n************************\n
