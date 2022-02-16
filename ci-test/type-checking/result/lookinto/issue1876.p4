/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1876.p4
\n
#include<core.p4>
#include<v1model.p4>
struct H {}
struct M {}
parser P(packet_in pkt, out H h, inout M m, inout standard_metadata_t meta) { state start { transition accept; } }
control G(inout H h, inout M m, inout standard_metadata_t meta) { apply { } }
control C(inout H h, inout M m) { apply{ } }
control D(packet_out pkt, in H h) { apply { } }
V1Switch(P(), C(), G(), G(), C(), D()) main;
************************\n******** petr4 type checking result: ********\n************************\n
