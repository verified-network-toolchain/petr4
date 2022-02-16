header H {
    bit<8> a;
    bit<8> b;
}

struct Headers {
    H h;
}

control ingress(inout Headers h) {
    @name("tmp") bit<8> tmp_1;
    @name("tmp_0") bit<8> tmp_2;
    apply {
        tmp_1 = h.h.a;
        {
            bit<8> w_0;
            @name("hasReturned_0") bool hasReturned_2;
            @name("retval_0") bit<8> retval_2;
            hasReturned_2 = false;
            w_0 = 8w3;
            {
                hasReturned_2 = true;
                retval_2 = 8w1;
            }
            h.h.a = w_0;
            tmp_2 = retval_2;
        }
        {
            bit<8> x_0 = tmp_1;
            bit<8> y_0 = tmp_2;
            bit<8> z_0;
            @name("hasReturned") bool hasReturned_1;
            @name("retval") bit<8> retval_1;
            hasReturned_1 = false;
            z_0 = x_0 | y_0;
            {
                hasReturned_1 = true;
                retval_1 = 8w4;
            }
            h.h.b = z_0;
        }
    }
}

control i(inout Headers h);
package top(i _i);
top(ingress()) main;

