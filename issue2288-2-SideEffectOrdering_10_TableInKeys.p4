struct Headers {
    bit<8> a;
    bit<8> b;
}

bit<8> g(inout bit<8> z) {
    z = 8w3;
    return 8w1;
}
bit<8> f(in bit<8> z, inout bit<8> x) {
    return 8w4;
}
control ingress(inout Headers h) {
    bit<8> tmp;
    bit<8> tmp_0;
    apply {
        {
            tmp = g(h.a);
            tmp_0 = h.a;
            f(tmp, tmp_0);
            h.a = tmp_0;
        }
    }
}

control c<T>(inout T d);
package top<T>(c<T> _c);
top<Headers>(ingress()) main;

