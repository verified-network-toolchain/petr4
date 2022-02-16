header H {
    bit<8> a;
    bit<8> b;
}

struct Headers {
    H h;
}

bit<8> f(in bit<8> x, in bit<8> y, out bit<8> z) {
    bool hasReturned = false;
    bit<8> retval;
    z = x | y;
    {
        hasReturned = true;
        retval = 8w4;
    }
    return retval;
}
bit<8> g(out bit<8> w) {
    bool hasReturned_0 = false;
    bit<8> retval_0;
    w = 8w3;
    {
        hasReturned_0 = true;
        retval_0 = 8w1;
    }
    return retval_0;
}
control ingress(inout Headers h) {
    bit<8> tmp;
    bit<8> tmp_0;
    apply {
        tmp = h.h.a;
        tmp_0 = g(h.h.a);
        f(tmp, tmp_0, h.h.b);
    }
}

control i(inout Headers h);
package top(i _i);
top(ingress()) main;

