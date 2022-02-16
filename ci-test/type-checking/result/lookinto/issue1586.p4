/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1586.p4
\n
extern void random<T>(out T result, in T lo);

control cIngress()
{
    bit<8> rand_val;
    apply {
        random(rand_val, 0);
    }
}
************************\n******** petr4 type checking result: ********\n************************\n
extern void random<T>(out T result, in T lo);
control cIngress() {
  bit<8> rand_val;
  apply {
    random(rand_val, 0);
  }
}

