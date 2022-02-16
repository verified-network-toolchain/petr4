/petr4/ci-test/type-checking/testdata/p4_16_samples/tuple4.p4
\n
control c(out bit<16> r) {
    apply {
        tuple<bit<32>, bit<16>> x = { 10, 12 };
        if (x == { 10, 12 })
           r = x[1];
        else
           r = (bit<16>)x[0];
    }
}

control _c(out bit<16> r);
package top(_c c);

top(c()) main;************************\n******** petr4 type checking result: ********\n************************\n
