extern bit<32> f(in bit<32> x, in bit<32> y);
control c(inout bit<32> r) {
    apply {
        r = f(f((bit<32>)5, (bit<32>)2), f((bit<32>)6, f((bit<32>)2, (bit<32>)3)));
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

