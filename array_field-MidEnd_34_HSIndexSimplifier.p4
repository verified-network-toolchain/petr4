header H {
    bit<1> z;
}

extern bit<32> f(inout bit<1> x, in bit<1> b);
control c(out H[2] h);
package top(c _c);
control my(out H[2] s) {
    bit<32> hsVar;
    @name("my.a") bit<32> a_0;
    apply {
        a_0 = 32w0;
        s[32w0].z = 1w1;
        s[32w1].z = 1w0;
        a_0 = f(s[32w0].z, 1w0);
        if (a_0 == 32w0) {
            a_0 = f(s[32w0].z, 1w1);
        } else if (a_0 == 32w1) {
            a_0 = f(s[32w1].z, 1w1);
        } else if (a_0 >= 32w1) {
            a_0 = hsVar;
        }
    }
}

top(my()) main;

