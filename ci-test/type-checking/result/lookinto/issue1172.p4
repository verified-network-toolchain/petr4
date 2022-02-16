/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1172.p4
\n
extern T max<T>(T t1, T t2);

extern Register<W> {
    void write(in W max);
}
************************\n******** petr4 type checking result: ********\n************************\n
extern T max<T>(T t1, T t2);
extern Register<W> {
  void write(in W max);
}


************************\n******** p4c type checking result: ********\n************************\n
