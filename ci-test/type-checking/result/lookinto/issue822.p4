/petr4/ci-test/type-checking/testdata/p4_16_samples/issue822.p4
\n
#include <core.p4>

// Architecture
control C();
package S(C c);

extern BoolRegister {
    BoolRegister();
}

extern ActionSelector {
    ActionSelector(BoolRegister reg);
}

// User Program
BoolRegister() r;

control MyC1() {
  ActionSelector(r) action_selector;
  apply {}
}

S(MyC1()) main;
************************\n******** petr4 type checking result: ********\n************************\n
