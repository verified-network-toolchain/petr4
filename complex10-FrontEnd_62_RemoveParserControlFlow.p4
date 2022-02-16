extern bit<32> f(in bit<32> x);
control c(inout bit<32> r) {
    @name("tmp") bit<32> tmp_7;
    @name("tmp_0") bool tmp_8;
    @name("tmp_1") bool tmp_9;
    @name("tmp_2") bit<32> tmp_10;
    @name("tmp_3") bool tmp_11;
    @name("tmp_4") bool tmp_12;
    @name("tmp_5") bit<32> tmp_13;
    @name("tmp_6") bool tmp_14;
    apply {
        tmp_7 = f(32w2);
        tmp_8 = tmp_7 > 32w0;
        if (tmp_8) {
            tmp_10 = f(32w3);
            tmp_11 = tmp_10 < 32w0;
            tmp_9 = tmp_11;
        } else {
            tmp_9 = false;
        }
        if (tmp_9) {
            tmp_12 = true;
        } else {
            tmp_13 = f(32w5);
            tmp_14 = tmp_13 == 32w2;
            tmp_12 = tmp_14;
        }
        if (tmp_12) {
            r = 32w1;
        } else {
            r = 32w2;
        }
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

