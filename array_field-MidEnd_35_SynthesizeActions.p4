header H {
    bit<1> z;
}

extern bit<32> f(inout bit<1> x, in bit<1> b);
control c(out H[2] h);
package top(c _c);
control my(out H[2] s) {
    bit<32> hsVar;
    @name("my.a") bit<32> a_0;
    @hidden action array_field30() {
        a_0 = f(s[32w0].z, 1w1);
    }
    @hidden action array_field30_0() {
        a_0 = f(s[32w1].z, 1w1);
    }
    @hidden action array_field30_1() {
        a_0 = hsVar;
    }
    @hidden action array_field26() {
        a_0 = 32w0;
        s[32w0].z = 1w1;
        s[32w1].z = 1w0;
        a_0 = f(s[32w0].z, 1w0);
    }
    apply {
        array_field26();
        if (a_0 == 32w0) {
            array_field30();
        } else if (a_0 == 32w1) {
            array_field30_0();
        } else if (a_0 >= 32w1) {
            array_field30_1();
        }
    }
}

top(my()) main;

