control c(inout bit<32> x) {
    @name("c.tmp") bit<32> tmp_1;
    @name("c.tmp") bit<32> tmp_5;
    @name("c.tmp") bit<32> tmp_6;
    apply {
        if (x > x + 32w1) {
            tmp_1 = x + 32w1;
        } else {
            tmp_1 = x;
        }
        if (x > x + 32w4294967295) {
            tmp_5 = x + 32w4294967295;
        } else {
            tmp_5 = x;
        }
        if (tmp_1 > tmp_5) {
            tmp_6 = tmp_5;
        } else {
            tmp_6 = tmp_1;
        }
        x = tmp_6;
    }
}

control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;

