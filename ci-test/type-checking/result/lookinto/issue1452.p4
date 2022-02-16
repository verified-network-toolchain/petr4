/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1452.p4
\n
control c() {
    bit<32> x;

    action a(inout bit<32> arg) {
        arg = 1;
        return;
    }
    apply {
        a(x);
    }
}

control proto();
package top(proto p);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
control c() {
  bit<32> x;
  action a(inout bit<32> arg) {
    arg = 1;
    return;
  }
  apply {
    a(x);
  }
}
control proto ();
package top (proto p);
top(c()) main;

************************\n******** p4c type checking result: ********\n************************\n
