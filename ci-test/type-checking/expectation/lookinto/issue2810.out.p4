/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2810.p4
\n
#include <core.p4>

control HwControl<H>(inout H hdr);

package Switch<H>(HwControl<H> c);

extern void HwSplFunc<T, R>(in T hdr1, @optional in R hdr2);

header eth_t {
    bit<48> sa;
    bit<48> da;
    bit<16> type;
}

struct parsed_header_t {
    eth_t mac;
}

control match_action_unit(inout parsed_header_t hdr) {
    apply {
        HwSplFunc(hdr.mac);
    }
}

Switch(match_action_unit()) main;
************************\n******** petr4 type checking result: ********\n************************\n
************************\n******** p4c type checking result: ********\n************************\n
