extern bit<32> f(in bit<32> x);
control c(inout bit<32> r) {
    @name("c.tmp") bit<32> tmp;
    @name("c.tmp_1") bool tmp_1;
    @name("c.tmp_2") bit<32> tmp_2;
    @name("c.tmp_4") bool tmp_4;
    @name("c.tmp_5") bit<32> tmp_5;
    @hidden action complex10l21() {
        tmp_2 = f(32w3);
        tmp_1 = tmp_2 < 32w0;
    }
    @hidden action complex10l21_0() {
        tmp_1 = false;
    }
    @hidden action act() {
        tmp = f(32w2);
    }
    @hidden action complex10l21_1() {
        tmp_4 = true;
    }
    @hidden action complex10l21_2() {
        tmp_5 = f(32w5);
        tmp_4 = tmp_5 == 32w2;
    }
    @hidden action complex10l22() {
        r = 32w1;
    }
    @hidden action complex10l24() {
        r = 32w2;
    }
    apply {
        act();
        if (tmp > 32w0) {
            complex10l21();
        } else {
            complex10l21_0();
        }
        if (tmp_1) {
            complex10l21_1();
        } else {
            complex10l21_2();
        }
        if (tmp_4) {
            complex10l22();
        } else {
            complex10l24();
        }
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

