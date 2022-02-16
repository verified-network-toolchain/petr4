/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1208.p4
\n
control c();
package p(c _c);
package q(p _p);

control empty() {
    apply {}
}

q(p(empty())) main;
************************\n******** petr4 type checking result: ********\n************************\n
control c ();
package p (c _c);
package q (p _p);
control empty() {
  apply { 
  }
}
q(p(empty())) main;

