/petr4/ci-test/type-checking/testdata/p4_16_samples/issue754.p4
\n
control c(out bit<3> x)(bit<3> v) { apply { x = v; } }

control ctrl(out bit<3> _x);
package top(ctrl c);

top(c(12345)) main;
************************\n******** petr4 type checking result: ********\n************************\n
control c(out bit<3> x)(bit<3> v) {
  apply {
    x = v;
  }
}
control ctrl (out bit<3> _x);
package top (ctrl c);
top(c(12345)) main;

************************\n******** p4c type checking result: ********\n************************\n
