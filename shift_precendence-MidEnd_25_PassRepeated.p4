control i(out bit<4> a, out bit<16> x) {
    apply {
        a = 4w0;
        x = 16w0xfff;
    }
}

control c(out bit<4> a, out bit<16> x);
package top(c _c);
top(i()) main;

