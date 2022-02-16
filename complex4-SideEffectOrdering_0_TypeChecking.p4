extern E {
    E();
    bit<32> f(in bit<32> x);
}

control c(inout bit<32> r) {
    @name("e") E() e_0;
    apply {
        r = e_0.f(32w4) + e_0.f(32w5);
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

