/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2175.p4
\n
void do_something(inout bit<8> val) {
    if (val == 0) {
       val = 8w1;
       return;
    }
    val = 8w2;
}

control c(inout bit<8> v) {
    apply {
        do_something(v);

        if (v == 0) {
            v = 8w1;
            return;
        }
        v = 8w2;
    }
}

control e(inout bit<8> _v);
package top(e _e);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
