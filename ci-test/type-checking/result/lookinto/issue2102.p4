/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2102.p4
\n
#include <core.p4>

header H {
    bit<1> a;
}

struct headers {
    H h;
}

control c(inout headers hdr) {
    apply {
        if (hdr.h.a < 1) {
            hdr = hdr;
        }
    }
}

control e<T>(inout T t);
package top<T>(e<T> e);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
