struct S {
    bit<1> a;
    bit<1> b;
}

control c(out bit<1> b) {
    S tmp;
    @name("c.s") S s_0;
    apply {
        {
            s_0.a = 1w0;
            s_0.b = 1w1;
        }
        {
            {
                tmp.a = s_0.b;
                tmp.b = s_0.a;
            }
            {
                s_0.a = tmp.a;
                s_0.b = tmp.b;
            }
        }
        b = s_0.a;
    }
}

control e<T>(out T t);
package top<T>(e<T> e);
top<bit<1>>(c()) main;

