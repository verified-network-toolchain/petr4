extern bit<1> f(inout bit<1> x, in bit<1> y);
extern bit<1> g(inout bit<1> x);
header H {
    bit<1> z;
}

control c<T>(inout T t);
package top<T>(c<T> _c);
control my(inout H[2] s) {
    @name("a") bit<1> a_0;
    apply {
        a_0 = 1w0;
        a_0 = f(a_0, g(a_0));
        a_0 = f(s[a_0].z, g(a_0));
        a_0 = f(s[g(a_0)].z, a_0);
        a_0 = g(a_0);
        a_0 = g(a_0);
        s[a_0].z = g(a_0);
    }
}

top<H[2]>(my()) main;

