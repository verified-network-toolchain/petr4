/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2104.p4
\n
#include <core.p4>
#include <v1model.p4>

control c() {
    bit<16> F = 0;
    bit<128> Y = 0;
    action r() {
        Y = (bit<128>) F;
    }
    action v() {
        return; // the return comes before the action call
        r();
        F = (bit<16>)Y;
    }
    apply {
        v();
    }
}

control e();
package top(e e);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
