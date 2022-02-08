bit<32> min(in bit<32> a, in bit<32> b) {
    @name("hasReturned") bool hasReturned_1;
    @name("retval") bit<32> retval_1;
    @name("tmp") bit<32> tmp_3;
    hasReturned_1 = false;
    if (a > b) {
        tmp_3 = b;
    } else {
        tmp_3 = a;
    }
    {
        hasReturned_1 = true;
        retval_1 = tmp_3;
    }
    return retval_1;
}
bit<32> fun(in bit<32> a, in bit<32> b) {
    @name("hasReturned_0") bool hasReturned_2;
    @name("retval_0") bit<32> retval_2;
    @name("tmp_0") bit<32> tmp_4;
    @name("tmp_1") bit<32> tmp_5;
    @name("tmp_2") bit<32> tmp_6;
    hasReturned_2 = false;
    tmp_4 = a;
    {
        bit<32> a_0 = a;
        bit<32> b_0 = b;
        @name("hasReturned") bool hasReturned_1;
        @name("retval") bit<32> retval_1;
        @name("tmp") bit<32> tmp_3;
        hasReturned_1 = false;
        if (a_0 > b_0) {
            tmp_3 = b_0;
        } else {
            tmp_3 = a_0;
        }
        {
            hasReturned_1 = true;
            retval_1 = tmp_3;
        }
        tmp_5 = retval_1;
    }
    tmp_6 = tmp_4 + tmp_5;
    {
        hasReturned_2 = true;
        retval_2 = tmp_6;
    }
    return retval_2;
}
control c(inout bit<32> x) {
    apply {
        {
            bit<32> a_1 = x;
            bit<32> b_1 = x;
            @name("hasReturned_0") bool hasReturned_2;
            @name("retval_0") bit<32> retval_2;
            @name("tmp_0") bit<32> tmp_4;
            @name("tmp_1") bit<32> tmp_5;
            @name("tmp_2") bit<32> tmp_6;
            hasReturned_2 = false;
            tmp_4 = a_1;
            {
                bit<32> a_0 = a_1;
                bit<32> b_0 = b_1;
                @name("hasReturned") bool hasReturned_1;
                @name("retval") bit<32> retval_1;
                @name("tmp") bit<32> tmp_3;
                hasReturned_1 = false;
                if (a_0 > b_0) {
                    tmp_3 = b_0;
                } else {
                    tmp_3 = a_0;
                }
                {
                    hasReturned_1 = true;
                    retval_1 = tmp_3;
                }
                tmp_5 = retval_1;
            }
            tmp_6 = tmp_4 + tmp_5;
            {
                hasReturned_2 = true;
                retval_2 = tmp_6;
            }
            x = retval_2;
        }
    }
}

control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;

