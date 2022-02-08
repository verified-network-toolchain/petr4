struct tuple_0 {
    bit<32> f0;
    bit<16> f1;
}

control c(out bit<16> r) {
    apply {
        r = 16w12;
    }
}

control _c(out bit<16> r);
package top(_c c);
top(c()) main;

