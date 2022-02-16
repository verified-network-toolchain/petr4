header hdr {
    bit<32> a;
}

control ct(out bit<32> x, out bit<32> y);
package top(ct _ct);
bit<32> f(out bit<32> a) {
    bool hasReturned = false;
    bit<32> retval;
    a = 32w0;
    {
        hasReturned = true;
        retval = a;
    }
    return retval;
}
bit<32> g(in bit<32> a) {
    bool hasReturned_0 = false;
    bit<32> retval_0;
    {
        hasReturned_0 = true;
        retval_0 = a;
    }
    return retval_0;
}
control c(out bit<32> x, out bit<32> y) {
    @name("h") hdr h_0;
    @name("b") bool b_0;
    @name("simple_action") action simple_action_0() {
        y = g(x);
        f(x);
    }
    @name("simple_action") action simple_action() {
        y = g(x);
        f(x);
    }
    apply {
        h_0 = (hdr){a = 32w0};
        b_0 = h_0.isValid();
        h_0.setValid();
        if (b_0) {
            x = h_0.a;
            f(h_0.a);
            f(h_0.a);
        } else {
            x = f(h_0.a);
            x = g(h_0.a);
            f(h_0.a);
        }
        simple_action();
    }
}

top(c()) main;

