extern bit<32> f(in bit<32> x);
header H {
    bit<32> v;
}

control c(inout bit<32> r) {
    @name("h") H[2] h;
    @name("tmp") bit<32> tmp_1;
    @name("tmp_0") bit<32> tmp_2;
    apply {
        h[0].setInvalid();
        h[1].setInvalid();
        tmp_1 = f(32w2);
        tmp_2 = tmp_1;
        h[tmp_2].setValid();
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

