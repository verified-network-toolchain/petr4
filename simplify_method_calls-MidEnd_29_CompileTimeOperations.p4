header hdr {
    bit<32> a;
}

control ct(out bit<32> x, out bit<32> y);
package top(ct _ct);
control c(out bit<32> x, out bit<32> y) {
    @name("c.h") hdr h_0;
    @name("c.b") bool b_0;
    @name("c.simple_action") action simple_action() {
        y = x;
        x = 32w0;
    }
    apply {
        h_0.setValid();
        h_0.a = 32w0;
        b_0 = h_0.isValid();
        h_0.setValid();
        if (b_0) {
            x = h_0.a;
            h_0.a = 32w0;
            h_0.a = 32w0;
        } else {
            h_0.a = 32w0;
            x = 32w0;
            x = 32w0;
            h_0.a = 32w0;
        }
        simple_action();
    }
}

top(c()) main;

