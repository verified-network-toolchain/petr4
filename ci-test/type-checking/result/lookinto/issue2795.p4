/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2795.p4
\n
#include <core.p4>

header H {
    bit<32> a;
    bit<32> b;
}

control c(packet_out p) {
    apply {
        p.emit((H){0, 1});
        p.emit<H>({0,1});
    }
}

control ctr(packet_out p);
package top(ctr _c);

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
header H {
  bit<32> a;
  bit<32> b;
}
control c(packet_out p) {
  apply {
    p.emit((H) {0, 1});
    p.emit<H>({0, 1});
  }
}
control ctr (packet_out p);
package top (ctr _c);
top(c()) main;

