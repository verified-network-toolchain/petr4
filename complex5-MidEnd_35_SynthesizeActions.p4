extern bit<32> f(in bit<32> x);
control c(inout bit<32> r) {
    @name("c.tmp") bit<32> tmp;
    @hidden action complex5l22() {
        r = 32w1;
    }
    @hidden action complex5l24() {
        r = 32w2;
    }
    @hidden action act() {
        tmp = f(32w2);
    }
    apply {
        act();
        if (tmp > 32w0) {
            complex5l22();
        } else {
            complex5l24();
        }
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

