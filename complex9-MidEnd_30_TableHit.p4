extern bit<32> f(in bit<32> x);
control c(inout bit<32> r) {
    @name("c.tmp") bit<32> tmp;
    @name("c.tmp_1") bool tmp_1;
    @name("c.tmp_2") bit<32> tmp_2;
    apply {
        tmp = f(32w2);
        if (tmp > 32w0) {
            tmp_2 = f(32w3);
            tmp_1 = tmp_2 < 32w0;
        } else {
            tmp_1 = false;
        }
        if (tmp_1) {
            r = 32w1;
        } else {
            r = 32w2;
        }
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

