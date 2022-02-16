/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2175-3.p4
\n
extern X {
    X();
    abstract void a(inout bit<32> arg);
}

control t(inout bit<32> b) {
    X() c1_x = {
        void a(inout bit<32> arg1) {
            arg1 = arg1 + 1;
        }
    };
    X() c2_x = {
        void a(inout bit<32> arg2) {
            arg2 = arg2 + 2;
        }
    };
    apply {
    }
}

control cs(inout bit<32> arg);
package top(cs _ctrl);
top(t()) main;
************************\n******** petr4 type checking result: ********\n************************\n
