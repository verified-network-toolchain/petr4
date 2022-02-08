extern bit<32> f(in bit<32> x);
control c(inout bit<32> r) {
    @name("tmp") bit<32> tmp_0;
    apply {
        tmp_0 = f(32w5);
        r = f(tmp_0);
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

