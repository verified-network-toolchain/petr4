extern Generic<T> {
    Generic(T sz);
    R get<R>();
    R get1<R, S>(in S value, in R data);
}

extern void f<T>(in T arg);
control c<T>()(T size) {
    Generic<T>(size) x;
    apply {
        bit<32> a = x.get<bit<32>>();
        bit<5> b = x.get1<bit<5>, bit<10>>(10w0, 5w0);
        f<bit<5>>(b);
    }
}

control caller() {
    c<bit<8>>(8w9) cinst;
    apply {
        cinst.apply();
    }
}

control s();
package p(s parg);
p(caller()) main;

