/petr4/ci-test/type-checking/testdata/p4_16_samples/issue933-1.p4
\n
#include <core.p4>

/* Program */
struct headers {
    bit<32> x;
}

extern void f(headers h);

control c() {
    apply {
        headers h;
        f({ 5 });
    }
}

control C();
package top(C _c);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
