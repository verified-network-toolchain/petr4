control c(inout bit<32> x) {
    @name("c.tmp") bit<32> tmp_1;
    @name("c.tmp") bit<32> tmp_5;
    @name("c.tmp") bit<32> tmp_6;
    @hidden action issue15442l2() {
        tmp_1 = x + 32w1;
    }
    @hidden action issue15442l2_0() {
        tmp_1 = x;
    }
    @hidden action issue15442l2_1() {
        tmp_5 = x + 32w4294967295;
    }
    @hidden action issue15442l2_2() {
        tmp_5 = x;
    }
    @hidden action issue15442l2_3() {
        tmp_6 = tmp_5;
    }
    @hidden action issue15442l2_4() {
        tmp_6 = tmp_1;
    }
    @hidden action issue15442l7() {
        x = tmp_6;
    }
    apply {
        if (x > x + 32w1) {
            issue15442l2();
        } else {
            issue15442l2_0();
        }
        if (x > x + 32w4294967295) {
            issue15442l2_1();
        } else {
            issue15442l2_2();
        }
        if (tmp_1 > tmp_5) {
            issue15442l2_3();
        } else {
            issue15442l2_4();
        }
        issue15442l7();
    }
}

control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;

