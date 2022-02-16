extern bit<32> f(in bit<32> x);
control c(inout bit<32> r) {
    @name("c.tmp") bit<32> tmp;
    apply {
        tmp = f(32w2);
        if (tmp > 32w0) {
            r = 32w1;
        } else {
            r = 32w2;
        }
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

