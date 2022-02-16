control c(out bit<16> b) {
    @hidden action function9() {
        b = 16w12;
    }
    apply {
        function9();
    }
}

control ctr(out bit<16> b);
package top(ctr _c);
top(c()) main;

