/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2480.p4
\n
extern CRCPolynomial<T> {
    CRCPolynomial(T coeff);
}

control IngressT();
package Switch(IngressT i);

control Ingress()
{
    CRCPolynomial(coeff=8w32) poly;
    apply {}
}

Switch(Ingress()) main;
************************\n******** petr4 type checking result: ********\n************************\n
extern CRCPolynomial<T> {
  CRCPolynomial(T coeff);
}

control IngressT ();
package Switch (IngressT i);
control Ingress() {
  CRCPolynomial(coeff=8w32) poly;
  apply { 
  }
}
Switch(Ingress()) main;

************************\n******** p4c type checking result: ********\n************************\n
