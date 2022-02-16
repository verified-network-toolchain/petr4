/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2905.p4
\n
#include <core.p4>

control c() {
    action a() {}
    table t {
        key = {}
        actions = {
            a;
        }
        const entries = {}
    }

    apply {
    }
}
************************\n******** petr4 type checking result: ********\n************************\n
