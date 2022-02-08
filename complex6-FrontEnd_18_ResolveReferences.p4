extern bit<32> f(in bit<32> x);
control c(inout bit<32> r) {
    apply {
        if (f((bit<32>)2) > 32w0) {
            if (f((bit<32>)2) < 32w2) {
                r = (bit<32>)32w1;
            } else {
                r = (bit<32>)32w3;
            }
        } else {
            r = (bit<32>)32w2;
        }
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

