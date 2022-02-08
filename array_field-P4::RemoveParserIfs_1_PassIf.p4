header H {
    bit<1> z;
}

extern bit<32> f(inout bit<1> x, in bit<1> b);
control c(out H[2] h);
package top(c _c);
control my(out H[2] s) {
    apply {
        bit<32> a = (bit<32>)32w0;
        s[a].z = (bit<1>)1w1;
        s[a + 32w1].z = (bit<1>)1w0;
        a = f(s[a].z, (bit<1>)0);
        a = f(s[a].z, (bit<1>)1);
    }
}

top(my()) main;

