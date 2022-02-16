struct S {
    bit<32> l;
    bit<32> r;
}

control c(out bool z);
package top(c _c);
struct tuple_0 {
    bit<32> f0;
    bit<32> f1;
}

control test(out bool zout) {
    @hidden action listcompare22() {
        zout = true;
        zout = true;
    }
    apply {
        listcompare22();
    }
}

top(test()) main;

