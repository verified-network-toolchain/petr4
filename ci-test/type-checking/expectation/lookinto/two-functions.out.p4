/petr4/ci-test/type-checking/testdata/p4_16_samples/two-functions.p4
\n
bit<8> test1(inout bit<8> x) {
    return x;
}

bit<8> test2(inout bit<8> x) {
    return x;
}

control c(inout bit<8> a) {
    apply {
        test1(a);
        test2(a);
    }
}

control E(inout bit<8> t);
package top(E e);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
bit<8> test1 (inout bit<8> x) {
  return x;
}
bit<8> test2 (inout bit<8> x) {
  return x;
}
control c(inout bit<8> a) {
  apply {
    test1(a);
    test2(a);
  }
}
control E (inout bit<8> t);
package top (E e);
top(c()) main;

************************\n******** p4c type checking result: ********\n************************\n
