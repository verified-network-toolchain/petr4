/petr4/ci-test/type-checking/testdata/p4_16_samples/methodArgDontcare.p4
\n
extern E<T> {
    E();
    void f(in T arg);
}

control c() {
    E<_>() e;
    apply {
        e.f(0);
    }
}

control proto();
package top(proto p);

top(c()) main;
************************\n******** petr4 type checking result: ********\n************************\n
************************\n******** p4c type checking result: ********\n************************\n
