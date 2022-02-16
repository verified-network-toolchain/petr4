/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1205-bmv2.p4
\n
#include <core.p4>

parser P();
control C();
package V1Switch(P p, C c);

parser MyP() {
  state start {
    transition accept;
  }
}

control MyC() {
  apply {
  }
}

V1Switch(MyP(), MyC()) main;
************************\n******** petr4 type checking result: ********\n************************\n
