extern bit<32> f(in bit<32> x, in bit<32> y);
control c(inout bit<32> r) {
    @name("tmp") bit<32> tmp_2;
    @name("tmp_0") bit<32> tmp_3;
    @name("tmp_1") bit<32> tmp_4;
    apply {
        tmp_2 = f(32w5, 32w2);
        tmp_3 = f(32w2, 32w3);
        tmp_4 = f(32w6, tmp_3);
        r = f(tmp_2, tmp_4);
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

