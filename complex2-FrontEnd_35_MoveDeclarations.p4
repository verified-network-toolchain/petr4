extern bit<32> f(in bit<32> x);
header H {
    bit<32> v;
}

control c(inout bit<32> r) {
    @name("h") H[2] h_0;
    apply {
        h_0[0].setInvalid();
        h_0[1].setInvalid();
        h_0[f(32w2)].setValid();
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

