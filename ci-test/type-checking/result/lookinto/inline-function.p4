/petr4/ci-test/type-checking/testdata/p4_16_samples/inline-function.p4
\n
bit<32> min(in bit<32> a, in bit<32> b) {
    return a > b ? b : a;
}

bit<32> fun(in bit<32> a, in bit<32> b) {
    return a + min(a, b);
}

control c(inout bit<32> x) {
    apply {
        x = fun(x, x);
    }
}

control ctr(inout bit<32> x);
package top(ctr _c);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
