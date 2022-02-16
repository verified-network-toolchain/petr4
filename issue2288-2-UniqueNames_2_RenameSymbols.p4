struct Headers {
    bit<8> a;
    bit<8> b;
}

control ingress(inout Headers h) {
    @name("tmp") bit<8> tmp;
    @name("tmp_0") bit<8> tmp_0;
    apply {
        {
            @name("z_0") bit<8> z = h.a;
            @name("hasReturned") bool hasReturned;
            @name("retval") bit<8> retval;
            hasReturned = false;
            z = 8w3;
            hasReturned = true;
            retval = 8w1;
            h.a = z;
            tmp = retval;
        }
        tmp_0 = h.a;
        {
            @name("x_0") bit<8> x = tmp_0;
            @name("hasReturned_0") bool hasReturned_0;
            @name("retval_0") bit<8> retval_0;
            hasReturned_0 = false;
            hasReturned_0 = true;
            retval_0 = 8w4;
            tmp_0 = x;
        }
        h.a = tmp_0;
    }
}

control c<T>(inout T d);
package top<T>(c<T> _c);
top<Headers>(ingress()) main;

