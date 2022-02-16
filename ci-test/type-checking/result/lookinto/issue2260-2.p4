/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2260-2.p4
\n
control C();
package S(C c);
T f<T>(T x) {
    return x;
}
control MyC() {
    apply {
        bit<8> y = f((bit<8>)255);
    }
}
S(MyC()) main;
************************\n******** petr4 type checking result: ********\n************************\n
control C ();
package S (C c);
T f<T> (T x) {
  return x;
}
control MyC() {
  apply {
    bit<8> y = f((bit<8>) 255);
  }
}
S(MyC()) main;

