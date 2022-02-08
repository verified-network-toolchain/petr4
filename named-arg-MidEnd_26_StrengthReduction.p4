extern void f(in bit<16> x, in bool y);
control c() {
    apply {
        f(y = true, x = 16w0);
    }
}

control empty();
package top(empty _e);
top(c()) main;

