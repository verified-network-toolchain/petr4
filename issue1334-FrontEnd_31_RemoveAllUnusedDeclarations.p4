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

control c() {
    Overloaded() o;
    d(b = 32w2) dinst;
    apply {
        f();
        f(a = 32w2);
        f(b = 16w1);
        f(a = 32w1, b = 16w2);
        f(b = 16w2, a = 32w1);
        o.f();
        o.f(a = 32w2);
        o.f(b = 16w1);
        o.f(a = 32w1, b = 16w2);
        o.f(b = 16w2, a = 32w1);
        bit<32> z;
        dinst.apply(z);
    }
}

control proto();
package top(proto p);
top(p = c()) main;

