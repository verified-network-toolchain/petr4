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
