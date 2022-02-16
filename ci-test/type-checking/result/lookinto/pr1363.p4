/petr4/ci-test/type-checking/testdata/p4_16_samples/pr1363.p4
\n
#include<core.p4>

typedef bit implementation;

extern ActionProfile {
   ActionProfile(bit<32> size); // number of distinct actions expected
}

control c() {
  table t {
    actions = { NoAction; }
    implementation = ActionProfile(32);
  }

  apply {}
}
************************\n******** petr4 type checking result: ********\n************************\n
