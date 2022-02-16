/petr4/ci-test/type-checking/testdata/p4_16_samples/stack2.p4
\n
#include <core.p4>
header h { }
control c(out bit<32> x) {
    apply {
        h[4] stack;
        bit<32> sz = stack.size;
        x = sz;
    }
}
control Simpler(out bit<32> x);
package top(Simpler ctr);
top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
