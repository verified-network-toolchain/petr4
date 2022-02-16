extern E {
    E();
    bit<32> f(in bit<32> x);
}

control c(inout bit<32> r) {
    E() e;
    apply {
        r = e.f((bit<32>)4) + e.f((bit<32>)5);
    }
}

control simple(inout bit<32> r);
package top(simple e);
top(c()) main;

