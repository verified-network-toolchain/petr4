extern bit<32> f(in bit<32> x);
header H {
    bit<32> v;
}

control c(inout bit<32> r) {
    @name("c.h") H[2] h_0;
    @name("c.tmp") bit<32> tmp;
    @hidden action complex2l25() {
        h_0[32w0].setValid();
    }
    @hidden action complex2l25_0() {
        h_0[32w1].setValid();
    }
    @hidden action complex2l24() {
        h_0[0].setInvalid();
        h_0[1].setInvalid();
        tmp = f(32w2);
    }
    apply {
        complex2l24();
        if (tmp == 32w0) {
            complex2l25();
        } else if (tmp == 32w1) {
            complex2l25_0();
        }
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

