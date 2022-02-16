header H {
    bit<8> a;
    bit<8> b;
}

struct Headers {
    H h;
}

bit<8> f(in bit<8> x, in bit<8> y, out bit<8> z) {
    @name("hasReturned") bool hasReturned_1;
    @name("retval") bit<8> retval_1;
    hasReturned_1 = false;
    z = x | y;
    {
        hasReturned_1 = true;
        retval_1 = 8w4;
    }
    return retval_1;
}
bit<8> g(out bit<8> w) {
    @name("hasReturned_0") bool hasReturned_2;
    @name("retval_0") bit<8> retval_2;
    hasReturned_2 = false;
    w = 8w3;
    {
        hasReturned_2 = true;
        retval_2 = 8w1;
    }
    return retval_2;
}
control ingress(inout Headers h) {
    @name("tmp") bit<8> tmp_1;
    @name("tmp_0") bit<8> tmp_2;
    apply {
        tmp_1 = h.h.a;
        tmp_2 = g(h.h.a);
        f(tmp_1, tmp_2, h.h.b);
    }
}

control i(inout Headers h);
package top(i _i);
top(ingress()) main;

