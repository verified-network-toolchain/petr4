/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2797_ebpf.p4
\n
#include <ebpf_model.p4>
#include <core.p4>

header X {
    bit<1>  dc;
    bit<3>  cpd;
    bit<2>  snpadding;
    bit<16> sn;
    bit<2>  e;
}

struct Headers_t {
    X x;
}

parser prs(packet_in p, out Headers_t headers) {
    state start  {
        p.extract(headers.x);
        transition accept;
    }
}

control pipe(inout Headers_t headers, out bool pass) {
    apply {
        pass = true;
        if (!headers.x.isValid()) {
            pass = false;
            return;
        }
    }
}

ebpfFilter(prs(), pipe()) main;************************\n******** petr4 type checking result: ********\n************************\n
