/petr4/ci-test/type-checking/testdata/p4_16_samples/issue933.p4
\n
#include <core.p4>

/* Architecture */
control Deparser<H>(packet_out packet, in H hdr);
package Switch<H>(Deparser<H> d);

/* Program */
struct headers {
  /* empty */
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit<headers>({});
    }
}

Switch(MyDeparser()) main;
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
control Deparser<H> (packet_out packet, in H hdr);
package Switch<H3> (Deparser<H3> d);
struct headers {
  
}
control MyDeparser(packet_out packet, in headers hdr) {
  apply {
    packet.emit<headers>({});
  }
}
Switch(MyDeparser()) main;

