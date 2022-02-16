/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1540.p4
\n
#include <core.p4>

control Ingress<H, M>(inout H h, inout M m);
control IngressDeparser<H>(packet_out pkt, inout H h);
package Pipeline<H, M>(Ingress<H, M> g, IngressDeparser<H> _c);
package Top<H1, M1, H2, M2>(Pipeline<H1, M1> p0, Pipeline<H2, M2> p1);

header header_t {}
struct metadata_t {}

control IngressMirror() {
  apply { }
}

control SwitchIngress(inout header_t t, inout metadata_t m) {
  apply { }
}

control SwitchIngressDeparser(packet_out pkt, inout header_t h) {
  IngressMirror() im;
  apply {
    im.apply();
  }
}

Pipeline(SwitchIngress(), SwitchIngressDeparser()) p0;
Pipeline(SwitchIngress(), SwitchIngressDeparser()) p1;

Top(p0, p1) main;
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
control Ingress<H, M> (inout H h, inout M m);
control IngressDeparser<H3> (packet_out pkt, inout H3 h);
package Pipeline<H4, M5> (Ingress<H4, M5> g, IngressDeparser<H4> _c);
package Top<H1, M1, H2, M2> (Pipeline<H1, M1> p0, Pipeline<H2, M2> p1);
header header_t {
  
}
struct metadata_t {
  
}
control IngressMirror() {
  apply { 
  }
}
control SwitchIngress(inout header_t t, inout metadata_t m) {
  apply { 
  }
}
control SwitchIngressDeparser(packet_out pkt, inout header_t h) {
  IngressMirror() im;
  apply {
    im.apply();
  }
}
Pipeline(SwitchIngress(), SwitchIngressDeparser()) p0;
Pipeline(SwitchIngress(), SwitchIngressDeparser()) p1;
Top(p0, p1) main;

