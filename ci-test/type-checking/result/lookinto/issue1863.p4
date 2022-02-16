/petr4/ci-test/type-checking/testdata/p4_16_samples/issue1863.p4
\n
struct S {
    bit a;
    bit b;
}

control c(out bit b) {
    apply {
        S s = { 0, 1 };
        s = { s.b, s.a };
        b = s.a;
    }
}

control e<T>(out T t);
package top<T>(e<T> e);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
