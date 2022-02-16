/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2104-1.p4
\n
#include <core.p4>

// adding the inout qualifier leads to a compiler crash
bit<8> test(inout bit<8> x) {
    return x;
}

control c(inout bit<8> a) {
    apply {
        test(a);
    }
}

control E(inout bit<8> t);
package top(E e);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
