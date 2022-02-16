/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2288-2.p4
\n
struct Headers {
    bit<8> a;
    bit<8> b;
}

bit<8> g(inout bit<8> z) {
    z = 8w3;
    return 8w1;
}

bit<8> f(in bit<8> z, inout bit<8> x) {
    return 8w4;
}

control ingress(inout Headers h) {
    apply {
        f(g(h.a), h.a);
    }
}

control c<T>(inout T d);
package top<T>(c<T> _c);

top(ingress()) main;
************************\n******** petr4 type checking result: ********\n************************\n
struct Headers {
  bit<8> a;
  bit<8> b;
}
bit<8> g (inout bit<8> z) {
  z = 8w3;
  return 8w1;
}
bit<8> f (in bit<8> z, inout bit<8> x) {
  return 8w4;
}
control ingress(inout Headers h) {
  apply {
    f(g(h.a), h.a);
  }
}
control c<T> (inout T d);
package top<T0> (c<T0> _c);
top(ingress()) main;

************************\n******** p4c type checking result: ********\n************************\n
