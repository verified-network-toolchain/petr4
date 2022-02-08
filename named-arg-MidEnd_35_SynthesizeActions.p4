extern void f(in bit<16> x, in bool y);
control c() {
    @hidden action namedarg8() {
        f(y = true, x = 16w0);
    }
    apply {
        namedarg8();
    }
}

control empty();
package top(empty _e);
top(c()) main;

