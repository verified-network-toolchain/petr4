/petr4/ci-test/type-checking/testdata/p4_16_samples/default-switch.p4
\n
control ctrl() {
    action a() {}
    action b() {}

    table t {
        actions = { a; b; }
        default_action = a;
    }

    apply {
        switch (t.apply().action_run) {
            default:
            b: { return; }
        }
    }
}************************\n******** petr4 type checking result: ********\n************************\n
************************\n******** p4c type checking result: ********\n************************\n
