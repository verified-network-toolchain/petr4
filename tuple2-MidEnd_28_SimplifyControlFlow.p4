extern void f<T>(in T data);
control proto();
package top(proto _p);
struct tuple_0 {
    bit<32> f0;
    bool    f1;
}

control c() {
    @name("c.x_0") tuple_0 x;
    apply {
        x.f0 = 32w10;
        x.f1 = false;
        f<tuple_0>(x);
    }
}

top(c()) main;

