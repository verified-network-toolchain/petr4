header H {
    bit<8> a;
    bit<8> b;
}

struct Headers {
    H h;
}

bit<8> f(in bit<8> x, in bit<8> y, out bit<8> z) {
    z = x | y;
    return 8w4;
}
bit<8> g(out bit<8> w) {
    w = 8w3;
    return 8w1;
}
control ingress(inout Headers h) {
    bit<8> tmp;
    bit<8> tmp_0;
    apply {
        {
            tmp = h.h.a;
            tmp_0 = g(h.h.a);
            f(tmp, tmp_0, h.h.b);
        }
    }
}

control i(inout Headers h);
package top(i _i);
top(ingress()) main;

