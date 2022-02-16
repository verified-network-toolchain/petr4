/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2175-2.p4
\n
extern X {
    X();
    abstract void a(inout bit<32> arg);
}

control t(inout bit<32> b) {
    X() c1_x = {
        void a(inout bit<32> arg) {
            arg = arg + 1;
        }
    };
    apply {
    }
}

control cs(inout bit<32> arg);
package top(cs _ctrl);
top(t()) main;
************************\n******** petr4 type checking result: ********\n************************\n
************************\n******** p4c type checking result: ********\n************************\n
