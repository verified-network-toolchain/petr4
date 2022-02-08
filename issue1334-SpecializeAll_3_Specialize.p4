extern void f();
extern void f(bit<32> a);
extern void f(bit<16> b);
extern void f(bit<32> a, bit<16> b);
extern Overloaded {
    Overloaded();
    void f();
    void f(bit<32> a);
    void f(bit<16> b);
    void f(bit<32> a, bit<16> b);
}

control d(out bit<32> x)(bit<32> b) {
    apply {
        x = -b;
    }
}

control d_0(out bit<32> x) {
    apply {
        x = -32w2;
    }
}

control c() {
    @name("z") bit<32> z_0;
    @name("o") Overloaded() o_0;
    @name("dinst") d_0() dinst_0;
    apply {
        f();
        f(a = 32w2);
        f(b = 16w1);
        f(a = 32w1, b = 16w2);
        f(b = 16w2, a = 32w1);
        o_0.f();
        o_0.f(a = 32w2);
        o_0.f(b = 16w1);
        o_0.f(a = 32w1, b = 16w2);
        o_0.f(b = 16w2, a = 32w1);
        dinst_0.apply(z_0);
    }
}

control proto();
package top(proto p);
top(p = c()) main;

