/petr4/ci-test/type-checking/testdata/p4_16_samples/newtype2.p4
\n
#include <core.p4>

typedef bit<9> PortIdUInt_t;
type bit<9> PortId_t;

struct M {
    PortId_t e;
    PortIdUInt_t es;
}

control Ingress(inout M sm);
package V1Switch(Ingress ig);

control Forwarding (inout M sm) {
    apply {
        sm.es = (PortIdUInt_t)sm.e;
    }
}

control FabricIngress (inout M sm) {
    Forwarding() forwarding;
    apply {
        forwarding.apply(sm);
    }
}

V1Switch(FabricIngress()) main;
************************\n******** petr4 type checking result: ********\n************************\n
