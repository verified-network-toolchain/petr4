/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1830.p4
\n
void foo<T>(in T x) {}

void bar() {
    foo(true);
}

void main() {
    foo(8w0);
}
************************\n******** petr4 type checking result: ********\n************************\n
void foo<T> (in T x) { 
}
void bar () {
  foo(true);
}
void main () {
  foo(8w0);
}

************************\n******** p4c type checking result: ********\n************************\n
