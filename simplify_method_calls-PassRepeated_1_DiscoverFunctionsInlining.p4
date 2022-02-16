header hdr {
    bit<32> a;
}

control ct(out bit<32> x, out bit<32> y);
package top(ct _ct);
bit<32> f(out bit<32> a) {
    @name("hasReturned") bool hasReturned_1;
    @name("retval") bit<32> retval_1;
    hasReturned_1 = false;
    a = 32w0;
    {
        hasReturned_1 = true;
        retval_1 = a;
    }
    return retval_1;
}
bit<32> g(in bit<32> a) {
    @name("hasReturned_0") bool hasReturned_2;
    @name("retval_0") bit<32> retval_2;
    hasReturned_2 = false;
    {
        hasReturned_2 = true;
        retval_2 = a;
    }
    return retval_2;
}
control c(out bit<32> x, out bit<32> y) {
    @name("h") hdr h;
    @name("b") bool b;
    @name("simple_action") action simple_action_0() {
        y = g(x);
        f(x);
    }
    apply {
        h = (hdr){a = 32w0};
        b = h.isValid();
        h.setValid();
        if (b) {
            x = h.a;
            f(h.a);
            f(h.a);
        } else {
            x = f(h.a);
            x = g(h.a);
            f(h.a);
        }
        simple_action_0();
    }
}

top(c()) main;

