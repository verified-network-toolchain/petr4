header H {
    bit<1> z;
}

extern bit<32> f(inout bit<1> x, in bit<1> b);
control c(out H[2] h);
package top(c _c);
control my(out H[2] s) {
    @name("a") bit<32> a;
    @name("tmp") bit<32> tmp_1;
    @name("tmp_0") bit<32> tmp_2;
    apply {
        a = 32w0;
        s[a].z = 1w1;
        s[a + 32w1].z = 1w0;
        tmp_1 = a;
        a = f(s[tmp_1].z, 1w0);
        tmp_2 = a;
        a = f(s[tmp_2].z, 1w1);
    }
}

top(my()) main;

