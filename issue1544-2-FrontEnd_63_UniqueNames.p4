control c(inout bit<32> x) {
    @name("tmp_0") bit<32> tmp;
    @name("tmp_1") bit<32> tmp_0;
    apply {
        {
            @name("a_0") bit<32> a = x;
            @name("b_0") bit<32> b = x + 32w1;
            @name("hasReturned") bool hasReturned;
            @name("retval") bit<32> retval;
            @name("tmp") bit<32> tmp_1;
            hasReturned = false;
            if (a > b) {
                tmp_1 = b;
            } else {
                tmp_1 = a;
            }
            hasReturned = true;
            retval = tmp_1;
            tmp = retval;
        }
        {
            @name("a_1") bit<32> a_3 = x;
            @name("b_1") bit<32> b_3 = x + 32w4294967295;
            @name("hasReturned") bool hasReturned_1;
            @name("retval") bit<32> retval_1;
            @name("tmp") bit<32> tmp_5;
            hasReturned_1 = false;
            if (a_3 > b_3) {
                tmp_5 = b_3;
            } else {
                tmp_5 = a_3;
            }
            hasReturned_1 = true;
            retval_1 = tmp_5;
            tmp_0 = retval_1;
        }
        {
            @name("a_2") bit<32> a_4 = tmp;
            @name("b_2") bit<32> b_4 = tmp_0;
            @name("hasReturned") bool hasReturned_2;
            @name("retval") bit<32> retval_2;
            @name("tmp") bit<32> tmp_6;
            hasReturned_2 = false;
            if (a_4 > b_4) {
                tmp_6 = b_4;
            } else {
                tmp_6 = a_4;
            }
            hasReturned_2 = true;
            retval_2 = tmp_6;
            x = retval_2;
        }
    }
}

control ctr(inout bit<32> x);
package top(ctr _c);
top(c()) main;

