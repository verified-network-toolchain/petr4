/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2036-3.p4
\n
struct s {
    bit<8> x;
}

extern void f(in tuple<bit<8>> a, in s sarg);

control c() {
    apply {
        f({0}, {0});
    }
}
************************\n******** petr4 type checking result: ********\n************************\n
struct s {
  bit<8> x;
}
extern void f(in tuple<bit<8>> a, in s sarg);
control c() {
  apply {
    f({0}, {0});
  }
}

************************\n******** p4c type checking result: ********\n************************\n
