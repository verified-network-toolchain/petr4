extern bit<32> f(in bit<32> x);
control c(inout bit<32> r) {
    @name("tmp") bit<32> tmp_3;
    @name("tmp_0") bit<32> tmp_4;
    @name("tmp_1") bit<32> tmp_5;
    @name("tmp_2") bit<32> tmp_6;
    apply {
        tmp_4 = f(32w4);
        tmp_3 = tmp_4;
        tmp_5 = f(32w5);
        tmp_6 = tmp_3 + tmp_5;
        r = tmp_6;
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

