extern Generic<T> {
    Generic(T sz);
    R get<R>();
    R get1<R, S>(in S value, in R data);
}

extern void f<T>(in T arg);
control caller() {
    @name("cinst.b") bit<5> cinst_b_0;
    @name("cinst.x") Generic<bit<8>>(8w9) cinst_x_0;
    apply {
        {
            cinst_x_0.get<bit<32>>();
            cinst_b_0 = cinst_x_0.get1<bit<5>, bit<10>>(10w0, 5w0);
            f<bit<5>>(cinst_b_0);
        }
    }
}

control s();
package p(s parg);
p(caller()) main;

