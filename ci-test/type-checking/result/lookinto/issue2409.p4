/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2409.p4
\n
#include <core.p4>

parser p(out bit<32> z) {
    state start {
        bool b = true;
        if (b) {
            bit<32> x = 1;
            z = x;
        } else {
            bit<32> w = 2;
            z = w;
        }
        transition accept;
    }
}

parser _p(out bit<32> z);
package top(_p _pa);
top(p()) main;
************************\n******** petr4 type checking result: ********\n************************\n
