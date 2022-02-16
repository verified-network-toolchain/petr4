bit<32> min(in bit<32> a, in bit<32> b) {
    @name("hasReturned") bool hasReturned_0;
    @name("retval") bit<32> retval_0;
    @name("tmp") bit<32> tmp_2;
    hasReturned_0 = false;
    if (a > b) {
        tmp_2 = b;
    } else {
        tmp_2 = a;
    }
    {
        hasReturned_0 = true;
        retval_0 = tmp_2;
    }
    return retval_0;
}
control c(inout bit<32> x) {
    @name("tmp_0") bit<32> tmp_3;
    @name("tmp_1") bit<32> tmp_4;
    apply {
        {
            bit<32> a_0 = x;
            bit<32> b_0 = x + 32w1;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<32> retval_0;
            @name("tmp") bit<32> tmp_2;
            hasReturned_0 = false;
            if (a_0 > b_0) {
                tmp_2 = b_0;
            } else {
                tmp_2 = a_0;
            }
            {
                hasReturned_0 = true;
                retval_0 = tmp_2;
            }
            tmp_3 = retval_0;
        }
        {
            bit<32> a_1 = x;
            bit<32> b_1 = x + 32w4294967295;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<32> retval_0;
            @name("tmp") bit<32> tmp_2;
            hasReturned_0 = false;
            if (a_1 > b_1) {
                tmp_2 = b_1;
            } else {
                tmp_2 = a_1;
            }
            {
                hasReturned_0 = true;
                retval_0 = tmp_2;
            }
            tmp_4 = retval_0;
        }
        {
            bit<32> a_2 = tmp_3;
            bit<32> b_2 = tmp_4;
            @name("hasReturned") bool hasReturned_0;
            @name("retval") bit<32> retval_0;
            @name("tmp") bit<32> tmp_2;
            hasReturned_0 = false;
            if (a_2 > b_2) {
                tmp_2 = b_2;
            } else {
                tmp_2 = a_2;
            }
            {
                hasReturned_0 = true;
                retval_0 = tmp_2;
            }
            x = retval_0;
        }
    }
}

control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;

