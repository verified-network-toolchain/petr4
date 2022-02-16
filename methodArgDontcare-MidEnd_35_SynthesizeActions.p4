extern E<T> {
    E();
    void f(in T arg);
}

control c() {
    @name("c.e") E<_>() e_0;
    @hidden action methodArgDontcare9() {
        e_0.f(0);
    }
    apply {
        methodArgDontcare9();
    }
}

control proto();
package top(proto p);
top(c()) main;

