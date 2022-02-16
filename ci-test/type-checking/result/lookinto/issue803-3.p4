/petr4/ci-test/type-checking/testdata/p4_16_samples/issue803-3.p4
\n
#include <core.p4>

parser Parser<IH>(out IH parsedHeaders);
package Ingress<IH>(Parser<IH> p);
package Switch<IH>(Ingress<IH> ingress);

struct H {}

parser ing_parse(out H hdr) {
    state start {
        transition accept;
    }
}

Ingress<H>(ing_parse()) ig1;

Switch(ig1) main;
************************\n******** petr4 type checking result: ********\n************************\n
