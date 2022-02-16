struct T {
    bit<1> f;
}

struct tuple_1 {
    T f0;
    T f1;
}

struct S {
    tuple_1 f1;
    T       f2;
    bit<1>  z;
}

struct tuple_0 {
    T field;
    T field_0;
}

extern void f<T>(in T data);
control c(inout bit<1> r) {
    @name("c.s") S s_0;
    apply {
        {
            {
                {
                    s_0.f1.f0.f = 1w0;
                }
                {
                    s_0.f1.f1.f = 1w1;
                }
            }
            {
                s_0.f2.f = 1w0;
            }
            s_0.z = 1w1;
        }
        f<tuple_1>(s_0.f1);
        f<tuple_0>((tuple_0){field = (T){f = 1w0},field_0 = (T){f = 1w1}});
        r = s_0.f2.f & s_0.z;
    }
}

control simple(inout bit<1> r);
package top(simple e);
top(c()) main;

