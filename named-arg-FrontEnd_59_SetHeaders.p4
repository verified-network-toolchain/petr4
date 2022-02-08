extern void f(in bit<16> x, in bool y);
control c() {
    @name("xv") bit<16> xv;
    @name("b") bool b;
    apply {
        xv = 16w0;
        b = true;
        f(y = b, x = xv);
    }
}

control empty();
package top(empty _e);
top(c()) main;

