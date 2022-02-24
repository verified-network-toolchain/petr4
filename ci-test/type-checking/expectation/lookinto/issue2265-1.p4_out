/petr4/ci-test/type-checking/testdata/p4_16_samples/issue2265-1.p4
\n
extern void f<T>(in tuple<T> x);

control c() {
    apply {
        f<bit<32>>({ 32w2 });
    }
}************************\n******** petr4 type checking result: ********\n************************\n
extern void f<T>(in tuple<T> x);
control c() {
  apply {
    f<bit<32>>({32w2});
  }
}

************************\n******** p4c type checking result: ********\n************************\n
[--Wwarn=missing] warning: Program does not contain a `main' module
