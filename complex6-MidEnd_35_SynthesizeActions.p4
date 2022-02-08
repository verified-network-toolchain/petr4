extern bit<32> f(in bit<32> x);
control c(inout bit<32> r) {
    @name("c.tmp") bit<32> tmp;
    @name("c.tmp_1") bit<32> tmp_1;
    @hidden action complex6l23() {
        r = 32w1;
    }
    @hidden action complex6l25() {
        r = 32w3;
    }
    @hidden action act() {
        tmp_1 = f(32w2);
    }
    @hidden action complex6l27() {
        r = 32w2;
    }
    @hidden action act_0() {
        tmp = f(32w2);
    }
    apply {
        act_0();
        if (tmp > 32w0) {
            act();
            if (tmp_1 < 32w2) {
                complex6l23();
            } else {
                complex6l25();
            }
        } else {
            complex6l27();
        }
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

