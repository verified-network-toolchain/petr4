/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1822.p4
\n
control C<X>();
package S<X>(C<X> x1, C<X> x2);
control MyC()() { apply {} }
S<bool>(MyC(), MyC()) main;
************************\n******** petr4 type checking result: ********\n************************\n
control C<X> ();
package S<X0> (C<X0> x1, C<X0> x2);
control MyC() {
  apply { 
  }
}
S<bool>(MyC(), MyC()) main;

************************\n******** p4c type checking result: ********\n************************\n
