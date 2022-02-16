/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2105.p4
\n
#include <core.p4>
#include <v1model.p4>

header H {
    bit<8> a;
}

struct Headers {
    H h;
}

control c() {
    apply {
        bit<8> x = 0;
        bit<8> y = 0;
        // the crash happens when reassigning c while referencing b
        // removing either the slice or the bor operation will fix the crash
        y = (x < 4 ? 8w2 : 8w1)[7:0] | 8w8;
    }
}

control e<T>();
package top<T>(e<T> e);

top<_>(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
