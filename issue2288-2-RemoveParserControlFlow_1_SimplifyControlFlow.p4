struct Headers {
    bit<8> a;
    bit<8> b;
}

control ingress(inout Headers h) {
    @name("tmp") bit<8> tmp_1;
    @name("tmp_0") bit<8> tmp_2;
    apply {
        {
            bit<8> z_0 = h.a;
            @name("hasReturned") bool hasReturned_1;
            @name("retval") bit<8> retval_1;
            hasReturned_1 = false;
            z_0 = 8w3;
            hasReturned_1 = true;
            retval_1 = 8w1;
            h.a = z_0;
            tmp_1 = retval_1;
        }
        tmp_2 = h.a;
        {
            bit<8> x_0 = tmp_2;
            @name("hasReturned_0") bool hasReturned_2;
            @name("retval_0") bit<8> retval_2;
            hasReturned_2 = false;
            hasReturned_2 = true;
            retval_2 = 8w4;
            tmp_2 = x_0;
        }
        h.a = tmp_2;
    }
}

control c<T>(inout T d);
package top<T>(c<T> _c);
top<Headers>(ingress()) main;

