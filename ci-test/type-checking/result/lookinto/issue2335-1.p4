/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2335-1.p4
\n
control c(inout bit<8> val)(int a) {
    apply {
       val = (bit<8>) a;
    }
}

control ingress(inout bit<8> a) {
    c(0) x;
    apply {
        x.apply(a);
    }
}

control i(inout bit<8> a);
package top(i _i);

top(ingress()) main;
************************\n******** petr4 type checking result: ********\n************************\n
