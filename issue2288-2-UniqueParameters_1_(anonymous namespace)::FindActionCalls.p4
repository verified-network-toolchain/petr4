struct Headers {
    bit<8> a;
    bit<8> b;
}

bit<8> g(inout bit<8> z) {
    @name("hasReturned") bool hasReturned_1 = false;
    @name("retval") bit<8> retval_1;
    z = 8w3;
    {
        hasReturned_1 = true;
        retval_1 = 8w1;
    }
    return retval_1;
}
bit<8> f(in bit<8> z, inout bit<8> x) {
    @name("hasReturned_0") bool hasReturned_2 = false;
    @name("retval_0") bit<8> retval_2;
    {
        hasReturned_2 = true;
        retval_2 = 8w4;
    }
    return retval_2;
}
control ingress(inout Headers h) {
    @name("tmp") bit<8> tmp_1;
    @name("tmp_0") bit<8> tmp_2;
    apply {
        tmp_1 = g(h.a);
        tmp_2 = h.a;
        f(tmp_1, tmp_2);
        h.a = tmp_2;
    }
}

control c<T>(inout T d);
package top<T>(c<T> _c);
top<Headers>(ingress()) main;

