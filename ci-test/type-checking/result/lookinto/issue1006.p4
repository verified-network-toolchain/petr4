/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1006.p4
\n
extern R<T> {
    R(T init);
};

struct foo {
    bit<8>      field1;
}


control c();
package top(c _c);

control c1() {
    R<tuple<bit<8>>>({ 1 }) reg0;
    R<foo>({ 1 }) reg1;
    apply {}
}

top(c1()) main;
************************\n******** petr4 type checking result: ********\n************************\n
extern R<T> {
  R(T init);
}

struct foo {
  bit<8> field1;
}
control c ();
package top (c _c);
control c1() {
  R<tuple<bit<8>>>({1}) reg0;
  R<foo>({1}) reg1;
  apply { 
  }
}
top(c1()) main;

