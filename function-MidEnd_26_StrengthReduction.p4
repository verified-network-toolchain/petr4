control c(out bit<16> b) {
    apply {
        ;
        b = 16w12;
    }
}

control ctr(out bit<16> b);
package top(ctr _c);
top(c()) main;

