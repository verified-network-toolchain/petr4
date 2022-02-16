extern Generic<T> {
    Generic(T sz);
    R get<R>();
    R get1<R, S>(in S value, in R data);
}

extern void f<T>(in T arg);
control c_0() {
    @name("b") bit<5> b_0;
    @name("x") Generic<bit<8>>(8w9) x_0;
    apply {
        x_0.get<bit<32>>();
        b_0 = x_0.get1<bit<5>, bit<10>>(10w0, 5w0);
        f<bit<5>>(b_0);
    }
}

control caller() {
    @name("cinst") c_0() cinst_0;
    @name("cinst.b") bit<5> cinst_b;
    @name("cinst.x") Generic<bit<8>>(8w9) cinst_x;
    apply {
        {
            cinst_x.get<bit<32>>();
            cinst_b = cinst_x.get1<bit<5>, bit<10>>(10w0, 5w0);
            f<bit<5>>(cinst_b);
        }
    }
}

control s();
package p(s parg);
p(caller()) main;

